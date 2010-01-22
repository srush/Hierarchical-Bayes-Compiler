-----------------------------------------------------------------------------
-- |
-- Module      :  GenC
-- Project     :  HBC
-- Copyright   :  (c) Hal Daume III
-- License     :  Open
-- 
-- Maintainer  :  Hal Daume III <me@hal3.name>
-- Stability   :  stable
-- Portability :  portable
--
-- Generate C code
--
-----------------------------------------------------------------------------

module GenC where

import qualified Core as C
import Code
import qualified Data.Map as M
import Type
import Data.Char
import Control.Monad
import Control.Monad.State
import System.IO
import Data.List
import Data.Maybe
import Data.Generics hiding ((:*:))
import Data.Typeable
import Util
import qualified Simulate
import qualified CodeOpt
import Debug.Trace 

type TypeMap' = M.Map Id [Type]
data GenC = GenC { indentSize :: Int , typemap :: TypeMap' , etypemap :: TypeMap' , nameMap :: M.Map String String , hh :: Handle , dump :: Bool , currentDistribution :: String }
               deriving (Eq, Show)

spec = (".c", run, ["stats.c","samplib.c"],["stats.h","samplib.h"])

run src compileCmd defaults dumpCore dumpSpec fname typ likF initF dumpF sampF (etyp :: TypeMap) einitF esampF edumpF = do
  h <- openFile fname WriteMode
  let genC0   = GenC 0 (mkTypeMap' typ) (mkTypeMap' etyp) M.empty h dumpCore ""
  evalStateT (gen src compileCmd dumpSpec fname defaults 
                      ((mapReturnType 1) likF) 
                      (map (mapReturnType 1)  initF)  dumpF (map (mapReturnType 1)  sampF)
                      (map (mapReturnType 1) einitF) edumpF (map (mapReturnType 1) esampF)
             ) genC0
  hClose h
  return ()

makeGlobalMap :: C.Core -> M.Map String String
makeGlobalMap core = M.fromList [(g, renameV g) | g <- C.getGlobals core]

renameV [] = []
renameV (x:xs)
  | x `elem` okChars = x : renameV xs
  | otherwise        = '_' : renameV xs
  where okChars = ['a'..'z'] ++ ['A'..'Z'] ++ ['0'..'9'] ++ "_&"

{- we need to get return types computed properly for the sampling
function.  we do the following:
 - if the variable type is Z or R, we return it directly
 - if the type is a vector *AND* it is a passed-in argument, we
   just overwrite and return void
 - if the type is a vector and is NOT a passed-in argument, we
   add an initial passed-in parameter that must be pre-allocated
   and post-freed
the key invariant this maintains is that any malloc that happens
in a function gets freed in the same function

-}

mapReturnType nn f =
  case (returnVal f, returnType f) of
    ([],_)          -> f    -- no return: very easy
    (_,[Type _ []]) -> f    -- simple return value
    ([Var (V id [])],_)
      | id `elem` map fst (params f) -> f { returnVal = [], returnType = [] }
                                     -- ^-- passed in variable
    ([Var (V id [])],[t]) ->
                      f { returnVal = [], returnType = [],
                          params = (id, t) : params f,
                          tempVars = filter ((/=id).fst) (tempVars f) }
    ([expr], [t]) -> f { returnVal = [], returnType = [],
                          params = ("return_value", t) : params f,
                          body = body f ++ [Assn (V "return_value" []) expr] }
--    _ -> error ("GenC.mapReturnType: cannot handle multiple parameter returns")

    (el, tl) -> f { returnVal = [], returnType = []
                  , params = params f ++ [("ptr_return_" ++ n, t) | (Var (V n []),t) <- zip el tl]
                  , body = body f ++ [Assn (V ("ptr_return_" ++ n) []) e | (Var (V n []),e) <- zip el el]
                  }

{-
    (e:e':es, t:t':ts) -> mapReturnType (nn+1) $
                        f { returnVal = e:es , returnType = t:ts -- use the first and remainder
                        -- add a parameter 
                          , params = params f ++ [("ptr_return_" ++ show nn, t')]
                          , body = body f ++ [Assn (V ("ptr_return_" ++ show nn) []) e']
                          }
-}

type M a = StateT GenC IO a

--gen :: FilePath -> Function -> [Function] -> [Function] -> M ()
gen (src,args) compileCmd (dumpSpecN,dumpSpecVars) fname (vals,loadD,loadM,numi::Int) likF initF dumpF sampF einitF edumpF esampF = do
--  let initF' = filter (not.isDefined) initF
--  let sampF' = filter (not.isDefined) sampF

  let initF_sorted = let (a,b) = partition (("initialize_post_" `isPrefixOf`).name) initF in b++a

  statement $
    "/*\n" ++
    "This program was automatically generated using:\n" ++
    hbcString ++ "\n" ++
    "HBC is a freely available compiler for statistical models.  This generated\n" ++
    "code can be built using the following command:\n\n" ++
    "  " ++ compileCmd ++ "\n\n" ++
    "The hierarchical model that this code reflects is:\n\n" ++
    src ++ "\n" ++
    "Generated using the command:\n\n" ++
    "  hbc compile " ++ unwords args ++ "\n" ++
    "*/\n"

  statement "#include <stdio.h>\n#include <stdlib.h>\n#include <math.h>\n#include \"stats.h\"\n\n"
  statement "\n/**************************** SAMPLING ****************************/\n\n"
  sampF'  <- mapM (\f -> genF f >>= \f' -> statement "\n" >> return f') (sampF)
  esampF' <- mapM (\f -> genF f >>= \f' -> statement "\n" >> return f') (esampF)
  statement "\n/************************* INITIALIZATION *************************/\n\n"
  initF'  <- mapM (\f -> genF f >>= \f' -> statement "\n" >> return f') (initF_sorted)
  einitF' <- mapM (\f -> genF f >>= \f' -> statement "\n" >> return f') (einitF)
  statement "\n/**************************** DUMPING *****************************/\n\n"
  dumpF'  <- mapM (\f -> genF f >>= \f' -> statement "\n" >> return f') (dumpF)
  edumpF' <- mapM (\f -> genF f >>= \f' -> statement "\n" >> return f') (edumpF)
  statement "\n/*************************** LIKELIHOOD ***************************/\n\n"
  likF'   <- genF likF
  statement "\n/****************************** MAIN ******************************/\n\n"

  let initF'' = [f | f <- initF', not (isDefined (name f))]
  let sampF'' = [f | f <- sampF', not (isDefined (name f))]

  statement "int main(int ARGC, char *ARGV[]) {\n"
  indent 1
  showIndent >> statement "double loglik,bestloglik;\n"
  showIndent >> statement "int iter;\n"

  tm  <- (unTypeMap' .  typemap) `liftM` get
  etm <- (unTypeMap' . etypemap) `liftM` get

  let dumpSpecVars_unf = [(v',t) | v <- dumpSpecVars
                              , let v' = if ("post_" ++ v) `elem` M.keys tm then "post_" ++ v else v
                              , t <- M.lookup v' tm `mplus` M.lookup v' etm]

  let varLengthParams = map (\s -> C.V (drop 11 s) []) $ nub $ listify ("ptr_return_" `isPrefixOf`) sampF'
  dumpSpecVars' <- flip filterM dumpSpecVars_unf $ \ (v,t) -> do
                     let b = (dumpSpecN == -2) && ("post_" `isPrefixOf` v) && any (typeDependsOn t) varLengthParams
                     when b $ lift $ hPutStrLn stderr $ "Warning: cannot both collapse and 'dump best' variable length parameter '" ++ v ++ "'"
                     return (not b)

  let vars0 = [(id,t) | (id,t) <- M.toList tm, not ("tmpSP" `isPrefixOf` id)] ++ [(id,t) | (id,t) <- M.toList etm, not ("tmpSP" `isPrefixOf` id)]
  let loadVars = concat ([high:dims | (_,(_,high,dims,_)) <- loadD] ++ [[n,d] | (_,(_,_,n,d)) <- loadM])
  let vars_old  = vars0 ++ [(n,tInt) | n <- loadVars, not (n `elem` map fst vars0)]
  let vars = nub (vars_old ++ [(v, t) | (v,_) <- vals, not (v `elem` map fst vars_old), let t = fromMaybe tInt (M.lookup v tm)]
                           ++ [("best_" ++ v, t) | (v,t) <- dumpSpecVars', dumpSpecN == -2])
  let postVars = filter ("post_" `isPrefixOf`) $ map fst vars

  mapM_ (\ (id,t) -> showIndent >> genType ("init",id,t) t >> statement " " >> statement (renameV id) >> statement ";\n") vars

  let mallocDims = nub $ map (\ (v, Type _ ti) -> if "best_" `isPrefixOf` v then length ti else length ti-1) vars

  mapM_ (\i  -> showIndent >> genIT ("malloc_dim_" ++ show i, tInt) >> statement ";\n") [1..maximum (0:mallocDims)]

  statement "\n"

  showIndent >> statement ("fprintf(stderr, \"-- This program was automatically generated using HBC (v " ++ hbcVersionString ++ ") from " ++ init fname ++ "hier\\n--     see http://hal3.name/HBC for more information\\n\");\n")
  showIndent >> statement "fflush(stderr);\n";


  showIndent >> statement "setall(time(0),time(0));   /* initialize random number generator */\n\n";

  mapM_ (\id -> showIndent >> statement (id ++ " = ???;    /* YOU MUST DEFINE THIS!!! */\n"))
        [renameV id | id <- M.keys tm, 
                      not ("tmpSP" `isPrefixOf` id), 
                      not (("initialize_" ++ id) `elem` map name initF'),
                      not (id `elem` commandDefined)]
  statement "\n"

  showIndent >> statement "/* variables defined with --define */\n"
  flip mapM_ vals $ \ (var,val) -> 
    showIndent >> statement (var ++ " = " ++ showValue (M.lookup var tm) val ++ ";\n")
  statement "\n"

  showIndent >> statement "fprintf(stderr, \"Loading data...\\n\");\n"
  showIndent >> statement "fflush(stderr);\n";

  showIndent >> statement "/* variables defined with --loadD */\n"
  flip mapM_ loadD $ \ (var,(fn,high,dims,seps)) -> 
    showIndent >> statement (var ++ " = load_discrete" ++ (show (length dims)) ++ "(" ++
                                 showFilename fn ++ concatMap (\d -> ", &" ++ d) dims ++ ", &" ++ high ++ ");\n");
  statement "\n"

  showIndent >> statement "/* variables defined with --loadM or --loadMI */\n"
  flip mapM_ loadM $ \ (var,(isReal,fn,n,d)) -> 
    showIndent >> statement (var ++ " = load_matrix" ++ (if isReal then "" else "_int") ++ "(" ++ showFilename fn ++ ", &" ++ n ++ ", &" ++ d ++ ");\n");
  statement "\n"

--  mapM_ (\ (id,t) -> showIndent >> genType t >> statement " " >> statement (renameV id) >> statement ";     /* YOU MUST DEFINE THIS */\n") defs

  -- mallocs
  showIndent >> statement "fprintf(stderr, \"Allocating memory...\\n\");\n"
  showIndent >> statement "fflush(stderr);\n";

--  mapM_ (lift . hPutStrLn stderr . show) vars
  mapM_ (\ (id,t) -> when (not $ null $ indices t) $ genMalloc 1 (statement id) t >> statement "\n") [(id,t) | (id,t) <- vars, not (id `elem` commandDefined)]
  statement "\n"

  showIndent >> statement "fprintf(stderr, \"Initializing variables...\\n\");\n"
  showIndent >> statement "fflush(stderr);\n";
  mapM_ (\f -> genFCall [] [] "" f) initF''
  mapM_ (\f -> genFCall [] [] "" f) einitF'

  statement "\n"
  showIndent >> statement ("for (iter=1; iter<=" ++ show numi ++ "; iter++) {\n")
  indent 1
  showIndent >> statement "fprintf(stderr, \"iter %d\", iter);\n"
  showIndent >> statement "fflush(stderr);\n";
  mapM_ (\f -> genFCall [] [] "" f) sampF''
  statement "\n"
  genFCall [] postVars "loglik" likF'
  showIndent >> statement "fprintf(stderr, \"\\t%g\", loglik);\n"

  showIndent >> statement "if ((iter==1)||(loglik>bestloglik)) {\n"
  indent 1
  showIndent >> statement "bestloglik = loglik;\n"
  showIndent >> statement "fprintf(stderr, \" *\");\n"

  when (dumpSpecN == -2 && not (null dumpSpecVars')) $  -- dump best
    flip mapM_ dumpSpecVars' $ \ (v,t) ->
      genCopy 1 (statement v) t
                  {- (fromMaybe (error $ "cannot find type of " ++ show v ++ " in " ++ show tm ++ " and " ++ show etm) 
                                                                          (M.lookup v tm `mplus` M.lookup v etm))) -}

  indent (-1)
  showIndent >> statement "}\n"


  showIndent >> statement "fprintf(stderr, \"\\n\");\n"
  showIndent >> statement "fflush(stderr);\n";

  -- handle dumping
  when (dumpSpecN >= 0 && not (null dumpSpecVars)) $ do  -- dump nth
    showIndent
    statement $ "if ((iter % " ++ show dumpSpecN ++ ") == 0) {\n";
    indent 1
    showIndent
    statement $ "printf(\"ll = %g\\n\", loglik);\n"
    mapM_ (\f -> when (drop 5 (name f) `elem` dumpSpecVars) $ genFCall [] postVars "" f) dumpF'
    mapM_ (genFCall [] postVars "") esampF'
    mapM_ (genFCall [] postVars "") edumpF'
    indent (-1)
    showIndent
    statement "}\n"

  indent (-1)
  showIndent >> statement "}\n\n"

  when (dumpSpecN == -1 && not (null dumpSpecVars)) $ do
    showIndent
    statement $ "printf(\"ll = %g\\n\", loglik);\n"
    mapM_ (\f -> when (drop 5 (name f) `elem` dumpSpecVars) $ genFCall [] postVars "" f) dumpF'
    statement "\n"

  when (dumpSpecN == -2 && not (null dumpSpecVars')) $ do
    showIndent
    statement $ "printf(\"ll = %g\\n\", bestloglik);\n"
    mapM_ (\f -> when (drop 5 (name f) `elem` map fst dumpSpecVars') $ genFCall (map fst dumpSpecVars') postVars "" f) dumpF'
    statement "\n"

  mapM_ (\ (id,t) -> when (not $ null $ indices t) $ genFree 1 (statement id) t >> statement "\n") (reverse vars)
  statement "\n"

  showIndent >> statement "return 0;\n"
  indent (-1)
  showIndent >> statement "}\n"
  where
    commandDefined = map fst vals ++ 
                     concatMap (\ (var,(_,high,dims,_)) -> var:high:dims) loadD ++ 
                     concatMap (\ (var,(_,_,n,d)) -> [var,n,d]) loadM
    isDefined x
      | "initialize_" `isPrefixOf` x = (drop 11 x) `elem` commandDefined
      | "resample_post" `isPrefixOf` x = True
      | "resample_"   `isPrefixOf` x = (drop  9 x) `elem` commandDefined
      | otherwise                    = False

    showFilename x =
      case parseArg x of
        Nothing -> "\"" ++ x ++ "\""
        Just i  -> "ARGV[" ++ i ++ "]"

    showValue typ0 (Simulate.ARG i) =
      case typ0 of
--        Nothing -> error $ "GenC.showValue: could not infer type of " ++ x
        Just (Type T0Real _) -> "atof(ARGV[" ++ i ++ "])"
        Just (Type _      _) -> "atoi(ARGV[" ++ i ++ "])"
        Nothing -> "atoi(ARGV[" ++ i ++ "])"
    showValue _ z = show z

genCopy dim mkId (Type _ []) = showIndent >> statement "best_" >> mkId >> statement " = " >> mkId >> statement ";\n"
genCopy dim mkId mytype@(Type t0 ((C.Range _ lo hi):rs)) = do
  tm <- (unTypeMap' . typemap) `liftM` get
  let (lo', []) = codifyExpr tm lo
  let (hi', []) = codifyExpr tm hi

  let ptr = pointerString 0 mytype

  showIndent
  statement "best_"
  mkId
  statement $ " = (" ++ ptr ++ "*) realloc(best_"
  mkId
  statement $ ", sizeof(" ++ ptr ++ ") * (("
  genE hi'
  statement ") - ("
  genE lo'
  statement ") + 1));\n"


  let md = "malloc_dim_" ++ show dim
  setName ('#' : show dim) md
  showIndent
  statement $ "for (" ++ md ++ "="
  genE lo'
  statement $ "; " ++ md ++ "<="
  genE hi'
  statement $ "; " ++ md ++ "++) {\n"
  indent ( 1)
  genCopy (dim+1) (mkId >> statement ("[" ++ md ++ "-") >> genE lo' >> statement "]") (Type t0 rs)
  indent (-1)
  unsetName ('#' : show dim)
  showIndent
  statement "}\n"

genFCall bestVars postVars defStr f = do
  genS [] (Call (name f) ret [Var (V id' []) | (nn,(id,_)) <- zip [2..] (params f)
                                             , let id' = 
                                                       if "ptr_return_" `isPrefixOf` id 
                                                       then ('&' : drop 11 id)
                                                       else 
                                                           case (("post_" ++ id) `elem` postVars, id `elem` bestVars) of
                                                             (True , True ) -> "best_post_" ++ id
                                                             (True , False) -> "post_" ++ id
                                                             (False, True ) -> "best_" ++ id
                                                             (False, False) -> id])
  where
    ret = 
      case returnVal f of
        [] -> []
        e@[Var (V v [])] -> e
        _ -> [Var (V defStr [])]


genF f = do
  tm <- (unTypeMap' . typemap) `liftM` get
  let tm'   = foldr (\ (t,i) m -> M.insert t i m) tm (params f ++ tempVars f)
  let f'    = devectorizeF tm' $ liftVecF tm' f
  let tm''  = foldr (\ (t,i) m -> M.insert t i m) tm (params f' ++ tempVars f')
  let f''   = addDimsF tm'' f'
  let f'''  = unliftVecLoops f''
  let tm''' = foldr (\ (t,i) m -> M.insert t i m) tm (params f''' ++ tempVars f''')
  let newp  = ((nub (codeIdsF f''') `intersect` M.keys tm''') \\ map fst (params f')) \\ map fst (tempVars f')
  let f'''' = f''' { params = params f''' ++ [(i,fromJust $ M.lookup i tm''') | i <- newp] }
  let [fopt]  = CodeOpt.opt [f'''']

  intermediate "initial function" (show f)
  intermediate "typemap" (show tm')
  intermediate "removedsub" (show $ removeSubF f)
  intermediate "lifted" (show (liftVecF tm' f))
  intermediate "devectorized" (show f')
  intermediate "new parameters" (show newp)
  intermediate "almost final function" (show f'')
  intermediate "unlifted function" (show f''')
  intermediate "final function" (show f'''')
  intermediate "optimized function" (show fopt)

  genF'  fopt
  return fopt

genF' f = do
  setDistribution (name f)
  showIndent
  statement $ case (returnVal f, returnType f) of
                ([],_) -> "void "
                (_,[Type T0Int  []]) -> "int "
                (_,[Type T0Real []]) -> "double "
                (_,t) -> error ("GenC.genF: cannot generate functions with return type " ++ show t ++ "; error on function " ++ name f)
  statement $ name f ++ "("
  case params f of
    [] -> return ()
    (x:xs) -> genIT x >> mapM_ (\x -> statement ", " >> genIT x) xs
  statement ") {\n"
  indent 1

  -- create temporary variables
  let mallocDims = nub $ map (\ (_, Type _ ti) -> length ti-1) (nub $ tempVars f)
  let dvvVars    = nub $ [v | v <- codeIdsF f, "dvv_loop_var_" `isPrefixOf` v]
  mapM_ (\it -> showIndent >> genIT it >> statement ";\n") $ nub $ tempVars f
  mapM_ (\i  -> showIndent >> genIT ("malloc_dim_" ++ show i, tInt) >> statement ";\n") [1..maximum (0:mallocDims)]
  mapM_ (\i  -> showIndent >> genIT (i, tInt) >> statement ";\n") dvvVars

  mapM_ (uncurry defineType) $ params   f
  mapM_ (uncurry defineType) $ nub $ tempVars f
  mapM_ (\i -> defineType ("malloc_dim_" ++ show i) tInt) [1..maximum (0:mallocDims)]
  mapM_ (\i -> defineType i                         tInt) dvvVars

  -- we need to make sure that we have qualified everything that's necessary
  -- for our mallocs to take place.  so, we maintain a list of variables that
  -- each malloc depends on
  let mallocDeps = [(idT, nub (concatMap findDeps ti \\ (map fst $ params f))) | idT@(id,Type _ ti) <- nub (tempVars f), not (null ti)]

--  lift $ mapM_ print mallocDeps

  -- malloc
  mapM_ (\ ((id,t),deps) -> when (null deps) $ genMalloc 1 (statement id) t) mallocDeps
--  mapM_ (\ (id, t@(Type _ ti)) -> if null ti then return () else genMalloc 1 (statement id) t) $ nub $ tempVars f

  -- generate body
  let mallocDeps' = filter (not.null.snd) mallocDeps
  tm <- (unTypeMap' . typemap) `liftM` get
  mapM_ (genS mallocDeps') $ body f

  -- free
  mapM_ (\ ((id,t),deps) -> when (null deps) $ genFree 1 (statement id) t) mallocDeps
--  mapM_ (\ (id, t@(Type _ ti)) -> if null ti then return () else genFree   1 (statement id) t) $ nub $ tempVars f

  -- generate return
  case returnVal f of
    []   -> return ()
    [e]  -> showIndent >> statement "return (" >> genE e >> statement ");\n"
  indent (-1)
  showIndent
  statement "}\n"

  mapM_ (uncurry undefinedType) $ params   f
  mapM_ (uncurry undefinedType) $ nub $ tempVars f
  mapM_ (\i -> undefinedType ("malloc_dim_" ++ show i) tInt) [1..maximum (0:mallocDims)]
  mapM_ (\i -> undefinedType i                         tInt) dvvVars


genMalloc dim mkId t@(Type t0 ((C.Range _ lo hi):rs)) = do
  tm <- (unTypeMap' . typemap) `liftM` get
  let (lo', []) = codifyExpr tm lo
  let (hi0, []) = codifyExpr tm hi
  let hi' = if null rs then (Fun "+" [hi0,Con (C.I 1)]) else hi0
  showIndent
  mkId >> statement " = "
  statement "(" >> genType ("malloc",t) t >> statement ") "
  statement "malloc(sizeof(" >> genType ("sizeof",t0,rs) (Type t0 rs) >> statement ") * (1+(" >> genE hi' >> statement ")-(" >> genE lo' >> statement ")));\n"
  when (not $ null rs) $ do
    let md = "malloc_dim_" ++ show dim
    setName ('#' : show dim) md
    showIndent
    statement $ "for (" ++ md ++ "="
    genE lo'
    statement $ "; " ++ md ++ "<="
    genE hi'
    statement $ "; " ++ md ++ "++) {\n"
    indent ( 1)
    genMalloc (dim+1) (mkId >> statement ("[" ++ md ++ "-") >> genE lo' >> statement "]") (Type t0 rs)
    indent (-1)
    unsetName ('#' : show dim)
    showIndent
    statement "}\n"

genFree dim mkId t@(Type t0 ((C.Range _ lo hi):rs)) = do
  tm <- (unTypeMap' . typemap) `liftM` get
  let (lo', []) = codifyExpr tm lo
  let (hi', []) = codifyExpr tm hi
  when (not $ null rs) $ do
    let md = "malloc_dim_" ++ show dim
    setName ('#' : show dim) md
    showIndent
    statement $ "for (" ++ md ++ "="
    genE lo'
    statement $ "; " ++ md ++ "<="
    genE hi'
    statement $ "; " ++ md ++ "++) {\n"
    indent ( 1)
    genFree (dim+1) (mkId >> statement ("[" ++ md ++ "-") >> genE lo' >> statement "]") (Type t0 rs)
    indent (-1)
    unsetName ('#' : show dim)
    showIndent
    statement "}\n"
  showIndent
  statement "free(" >> mkId >> statement ");\n"

genIT = uncurry genVarDef

genType context (Type t0 ix) = do
  genBType t0
  statement $ replicate (length ix) '*'
  where
    genBType t0 = statement =<< case t0 of 
                                  T0Int -> return "int" 
                                  T0Real -> return "double"
                                  _ -> do
                                    lift $ hPutStrLn stderr ("warning: GenC.genBType: unknown base type in context: " ++ show context ++ "; assuming int")
                                    return "int"

genVarDef id t = do
  genType ("varDef", id, t) t
  when ("ptr_return_" `isPrefixOf` id) $ statement "*"
  statement $ ' ' : (renameV id)

genS mallocDeps (Loop id lo hi b) = do
  showIndent

{-
  statement $ "for (" ++ (renameV id) ++ "="
  genE lo
  statement $ "-1; " ++ (renameV id) ++ "<"
  genE hi
  statement $ "; " ++ (renameV id) ++ "++) {\n"
  indent ( 1)
-}

  statement $ "for (" ++ (renameV id) ++ "="
  genE lo
  statement $ "; " ++ (renameV id) ++ "<="
  genE hi
  statement $ "; " ++ (renameV id) ++ "++) {\n"
  indent ( 1)


  -- check to see if we're now allowed to malloc anything
  let mallocDeps' = [(idT, deps \\ [id]) | (idT,deps) <- mallocDeps]
  let mallocDeps'' = filter (not.null.snd) mallocDeps'

  mapM_ (\ ((id,t),deps) -> when (null deps && id `elem` concatMap codeIdsS b) $ genMalloc 1 (statement id) t) mallocDeps'
  mapM (genS mallocDeps'') b
  mapM_ (\ ((id,t),deps) -> when (null deps && id `elem` concatMap codeIdsS b) $ genFree 1 (statement id) t) mallocDeps'


  indent (-1)
  showIndent
  statement "}\n"

genS mallocDeps (If c t e) = do
  showIndent
  statement $ "if ("
  genE c
  statement $ ") {\n"
  indent ( 1)
  mapM (genS mallocDeps) t
  indent (-1)
  case e of
    [] -> showIndent >> statement "}\n"
    _  -> do
      showIndent
      statement "} else {\n"
      indent ( 1)
      mapM (genS mallocDeps) e
      indent (-1)
      showIndent
      statement "}\n"

--genS (Assn v (Fun fn el)) | fn `elem` ["vec", "ID"] = genS (Call "vec" [] ((Var v):el))

genS mallocDeps (Assn v@(V v0 vl) e)
  | null vl && "ptr_return_" `isPrefixOf` v0 = do
  showIndent
  statement "*"
  genV v
  statement " = "
  genE e
  statement ";\n";

  | otherwise = do
  showIndent
  genV v
  statement " = "
  genE e
  statement ";\n";

genS mallocDeps (Incr v e) = do
  showIndent
  genV v
  statement " += "
  genE e
  statement ";\n";

-- we special case printf statements
genS mallocDeps (Call "printf_string"  [] [Var (V str [])]) = genPrintf (str ++ " = ") []
genS mallocDeps (Call "printf_int"     [] [x]) = genPrintf "%d" [x]
genS mallocDeps (Call "printf_real"    [] [x]) = genPrintf "%g" [x]
genS mallocDeps (Call "printf_newline" [] [] ) = genPrintf "\\n" []
genS mallocDeps (Call "printf_sep"     [] [Con (C.I 0)]) = genPrintf " " []
genS mallocDeps (Call "printf_sep"     [] [Con (C.I n)]) = genPrintf (" " ++ (genericReplicate n ';') ++ " ") []

genS mallocDeps (Call fname [Var (V v0 el)] args) -- [oldVar, size])
  | fname == "malloc" || fname == "realloc" = do
  tm <- (unTypeMap' . typemap) `liftM` get
  let ptr = pointerString (length el) $ fromJust $ M.lookup v0 tm
  let fname' = "(" ++ ptr ++ "*) " ++ fname

  showIndent
  genV (V v0 el)
  statement $ " = " ++ fname' ++ "("
  when (fname == "realloc") $ do
    genE (args !! 0)
    statement ", "

  statement $ "sizeof(" ++ ptr ++ ") * ("
  genE (last args)
  statement "));\n"

genS mallocDeps (Call f [ret] arg)
  | "sample_" `isPrefixOf` f, multivarRange (drop 7 f) = do
  showIndent
  statement $ (renameV f) ++ "("
  genE ret
  mapM_ (\a -> statement ", " >> genE a) arg
  statement ");\n"

genS mallocDeps (Call f [] l) = do
  showIndent
  statement $ (renameV f) ++ "("
  when (not $ null l) $ let (a:as) = l in do
    genE a
    mapM_ (\a -> statement ", " >> genE a) as
  statement ");\n"

genS mallocDeps (Call f [Var v] l) = do
  showIndent
  genV v
  statement $ " = " ++ (renameV f) ++ "("
  when (not $ null l) $ let (a:as) = l in do
    genE a
    mapM_ (\a -> statement ", " >> genE a) as
  statement ");\n"

genS mallocDeps (Call f ((Var v):vs) args) = do
  showIndent
  statement $ (renameV f) ++ "("
  -- generate normal args
  mapM_ (\a -> genE a >> statement ", ") args
  -- generate "lifted" return values
  statement "&" >> genV v
  mapM_ (\ (Var v) -> statement ", &" >> genV v) vs
  statement ");\n"

genS mallocDeps (Comment c) = showIndent >> statement ("/* " ++ c ++ " */\n")

genS mallocDeps s = error ("GenC.genS: cannot generate -- " ++ show s)

pointerString len_el (Type t0 l) 
      | n == 0 = error $ "malloc on scalar: " ++ show (Type t0 l) ++ " with len_el=" ++ show len_el
      | otherwise = s0 ++ replicate (n-1) '*'
      where n  = length l - len_el
            s0 = case t0 of { T0Int -> "int" ; T0Real -> "double" ; _ -> "void" }

genPrintf format args = do
  showIndent
  statement $ "printf(\"" ++ format ++ "\""
  case args of
    [] -> return ()
    l  -> mapM_ (\x -> statement ", " >> genE x) l
  statement ");\n";


genE (Var v) = genV v
genE (Con (C.I i)) = statement (show i)
genE (Con (C.R r)) = statement (show r)
genE (Fun f [a,b]) 
  | f == ".+" || f == ".*" = do
  tm <- (unTypeMap' . typemap) `liftM` get
  let Type t1 t1i = inferCodeType tm a
  let Type t0 t0i = inferCodeType tm b

  if null t0i
    then genE (Fun (drop 1 f) [a,b])
    else do
      let f' = (if f == ".+" then "add_const_" else "mult_const_") ++
               (if t1 == T0Int then "i" else "r") ++ "_" ++
               (show (length t0i))
      statement f' >> statement "(" >> genE a >> statement ", " >> genE b
      mapM_ (\ (C.Range _ lo hi) ->
                 let (lo', []) = codifyExpr tm lo
                     (hi', []) = codifyExpr tm hi
                 in  statement ", (" >> genE hi' >> statement ")-(" >> genE lo' >> statement ")+1"
            ) (drop (length t1i) t0i)
      statement ")"

  | f `elem` ["=","~=","<=","<",">",">="] = do
  let f' = case f of { "=" -> "==" ; "~=" -> "!=" ; _ -> f }
  statement "(((" >> genE a >> statement") "
  statement f'
  statement " (" >> genE b >> statement ")) ? 1 : 0)"

  | all (not.isAlpha) f = do
  
  genOp f (statement "(" >> genE a >> statement ")") (statement "(" >> genE b >> statement ")")

genE (Fun f (e:es)) = do
  statement $ (renameV f) ++ "("
  genE e
  mapM_ (\e -> statement ", " >> genE e) es
  statement ")"

genE (CaseOf cv ((e,f):cs)) = do
  statement "(("
  genE cv
  statement "=="
  genE e
  statement ") ? ("
  genE f
  statement ") : "
  genE (CaseOf cv cs)
  statement ")"
genE (CaseOf cv []) = statement " 0 "

genV v0@(V i el) = do
  nm <- nameMap `liftM` get
  let i' = M.findWithDefault i i nm
  when ((i == "") || (i == "?")) $ do
    curD <- currentDistribution `liftM` get
    fail ("GenC.genV: Type inference appears to have failed; try adding explicit type definitions for " ++ show curD ++ "; i could not find the type of variable " ++ show v0 ++ " in map " ++ show nm)
  tm <- (unTypeMap' . typemap) `liftM` get
  let Just (Type _ ranges) = M.lookup i tm
  statement (renameV i')
  mapM_ (\ (e, C.Range _ lo _) -> do
           statement "[" 
           genE e
           case lo of
             C.Con (C.I 0) -> return ()
             C.Con (C.R 0) -> return ()
             _ -> let (lo',[]) = codifyExpr tm lo in statement "-" >> genE lo'
           statement "]"
        ) (zip el ranges)

statement s = get >>= \st -> lift (hPutStr (hh st) s)

intermediate heading str = do
  d <- dump `liftM` get
  when d (lift (hPutStrLn stderr heading >> hPutStrLn stderr str >> hPutStrLn stderr ""))

showIndent :: StateT GenC IO ()
showIndent = do
  i <- indentSize `liftM` get
  statement (replicate (2*i) ' ')
  return ()

setName   old new = get >>= \st -> put (st { nameMap = M.insert old new (nameMap st) })
unsetName old     = get >>= \st -> put (st { nameMap = M.delete old     (nameMap st) })

setDistribution d = get >>= \st -> put (st { currentDistribution = d })

--defineType    i t = get >>= \st -> put (st { typemap = M.insert i t (typemap st) })
--undefinedType i _ = get >>= \st -> put (st { typemap = M.delete i   (typemap st) })

defineType    i t = get >>= \st -> put (st { typemap = M.insertWith (++) i [t] (typemap st) })
undefinedType i _ = get >>= \st -> put (st { typemap = 
                                                 case M.lookup i (typemap st) of
                                                   Nothing     -> typemap st
                                                   Just []     -> M.delete i (typemap st)
                                                   Just [_]    -> M.delete i (typemap st)
                                                   Just (_:xs) -> M.insert i xs (typemap st) })


mkTypeMap' = M.map (:[])
unTypeMap' = M.map head


indent i = get >>= \st -> put (st { indentSize = indentSize st + i })

genOp ('.':f) a1 a2 = genOp f a1 a2
genOp "^" a1 a2 = statement "pow(" >> a1 >> statement ", " >> a2 >> statement ")"
genOp f a1 a2 = a1 >> statement (" " ++ f ++ " ") >> a2

-----------------------------------------------------------------------------

-- removes "sub" and "vec" and "ID"; also removes vector assignments and increments
devectorizeF tm f = f { returnVal = liftM     (devectorizeE tm') $ returnVal f
                      , body      = concatMap (devectorizeS tm') $ body f }
  where tm' = foldr (\ (v,t) -> M.insert v t) tm (params f ++ tempVars f)

devectorizeS tm (Loop i lo hi b) = [Loop i (devectorizeE tm lo) (devectorizeE tm hi) (concatMap (devectorizeS tm) b)]
devectorizeS tm (If c t e) = [If (devectorizeE tm c) (concatMap (devectorizeS tm) t) (concatMap (devectorizeS tm) e)]
--devectorizeS tm (Assn v (Fun "vec" l)) = devectorizeS tm $ devectorizeVec 1 v l
devectorizeS tm assn@(Assn v e) 
  | V v0 [] <- v, "ptr_return_" `isPrefixOf` v0 = [assn]
  | mytrace (show ("devectorizeS",assn,v',e',v==v',e==e',inferCodeType tm (Var v'))) True =
  case inferCodeType tm (Var v') of
    Type _ [] -> [Assn v' e']
    Type T0Int  _ -> concatMap (devectorizeS tm) [Assn v' (Con (C.I 0)), Incr v' e']
    Type T0Real _ -> concatMap (devectorizeS tm) [Assn v' (Con (C.R 0)), Incr v' e']
  where v' = devectorizeV tm v ; e' = devectorizeE tm e
devectorizeS tm incr@(Incr v e)  =
--  | mytrace (show (incr, (inferCodeType tm (Var v'), inferCodeType tm e'))) True = 
  case (inferCodeType tm (Var v'), inferCodeType tm e') of
    (Type _ [], _)  -> [Incr v' e']
    (Type _ dV, Type _ dE) -> devectorizeS tm $ devectorizeIncr tm 1 v' e' dV dE
  where v' = devectorizeV tm v ; e' = devectorizeE tm e

devectorizeS tm call@(Call "vec" [] ((Var (V v sub)):val:dims)) = concatMap (devectorizeS tm) $ mkLoops 1 sub dims -- concatMap (devectorizeS tm) $ mkLoops 1 sub dims
  where
    mkLoops nn sub' [] = [Assn (V v sub') val]
    mkLoops nn sub' (lo:hi:[])   = [Loop i lo hi (mkLoops (nn+1) (sub' ++ [Var (V i [])]) [])
                                   ,Assn (V v (sub' ++ [Fun "+" [hi,Con (C.I 1)]])) (Fun "*" [val, Fun "-" [Fun "+" [lo,hi], Con (C.I 1)]])]
      where i = "dvv_loop_var_" ++ show nn
    mkLoops nn sub' (lo:hi:dims) = [Loop i lo hi (mkLoops (nn+1) (sub' ++ [Var (V i [])]) dims)]
--                                   ,Assn (V v (sub' ++ [Fun "+" [hi,Con (C.I 1)]])) (Fun "*" [val, Fun "-" [Fun "+" [lo,hi], Con (C.I 1)]])]
      where i = "dvv_loop_var_" ++ show nn
    mkLoops nn sub' args = error $ "GenC.devectorizeS.mkLoops: got " ++ show (nn,sub',args,call)

--devectorizeS tm c@(Call "vec" [] (ret:val:dims)) | mytrace (show (c, inferCodeType tm val)) False = undefined
{-
devectorizeS tm (Call "vec" [] (ret:val:dims)) =
  devectorizeS tm $
  case inferCodeType tm val of
    Type T0Int  _ -> Call ("vec_i_" ++ show ((length dims) `div` 2)) [] (ret : val : dims)
    Type T0Real _ -> Call ("vec_r_" ++ show ((length dims) `div` 2)) [] (ret : val : dims)
-}
--  where
--    makeDims (_:hi:xs) = hi : makeDims xs
--    makeDims [] = []

devectorizeS tm (Call v r a) = [Call v (map (devectorizeE tm) r) (map (devectorizeE tm) a)]
devectorizeS tm (Comment s) = [Comment s]

plusOne hi = Fun "+" [hi, Con (C.I 1)]

--devectorizeIncr tm num v e dV eV | mytrace (show (num,v,e,dV,eV)) False = undefined
devectorizeIncr tm num v e [] [] = Incr v e
devectorizeIncr tm num (V v vl) e ((C.Range _ lo hi):dV) eV@[] = 
  Loop i lo' (plusOne hi') [devectorizeIncr tm (num+1) (V v (vl ++ [Var (V i [])])) e dV (drop 1 eV)]
  where 
    i = "dvv_loop_var_" ++ show num
    (lo', []) = codifyExpr tm lo
    (hi', []) = codifyExpr tm hi
devectorizeIncr tm num (V v vl) (Var (V e el)) ((C.Range _ lo hi):dV) ((C.Range _ lo2 hi2):eV) = 
  Loop i lo' (plusOne hi') [devectorizeIncr tm (num+1) (V v (vl ++ [Var (V i [])])) (Var (V e (el ++ [Var (V i [])]))) dV eV]
  where 
    i = "dvv_loop_var_" ++ show num
    (lo', []) = codifyExpr tm lo 
    (hi', []) = codifyExpr tm hi
devectorizeIncr tm num (V v vl) e ((C.Range _ lo hi):dV) ((C.Range _ lo2 hi2):eV) = 
  Loop i lo' (plusOne hi') [devectorizeIncr tm (num+1) (V v (vl ++ [Var (V i [])])) (devectorizeIncrE (Var (V i [])) e) dV eV]
  where 
    i = "dvv_loop_var_" ++ show num
    (lo', []) = codifyExpr tm lo 
    (hi', []) = codifyExpr tm hi
{-
devectorizeIncr tm num (V v vl) e [] ((C.Range _ lo hi):eV) = 
  Loop i lo' hi' [devectorizeIncr tm (num+1) (V v (vl ++ [Var (V i [])])) (devectorizeIncrE (Var (V i [])) e) [] eV]
  where 
    i = "dvv_loop_var_" ++ show num
    (lo', []) = codifyExpr tm lo 
    (hi', []) = codifyExpr tm hi
-}
devectorizeIncr tm num v e r1 r2 = error ("Code.devectorizeIncr: cannot handle: " ++ show (v,e,r1,r2))

devectorizeIncrE sub e | mytrace ("devectorizeIncrE" ++ show (sub,e)) False = undefined
devectorizeIncrE sub (Var (V i el)) = Var (V i (el ++ [sub]))
devectorizeIncrE sub (Con c) = Con c -- error ("GenC.devectorizeIncrE: got constant")
devectorizeIncrE sub (Fun f [a,b])
  | f `elem` [".+",".-",".*","./"] = Fun f [a, devectorizeIncrE sub b]
  | f `elem` ["+","-","*","/","=","~=","<=","<",">",">=","||","&&"] = Fun f [devectorizeIncrE sub a, devectorizeIncrE sub b]
  | f == "^" = Fun f [devectorizeIncrE sub a, b]
devectorizeIncrE sub (Fun f (a:b:c:dims))
  | "mult_const_" `isPrefixOf` f ||
    "add_const_"  `isPrefixOf` f || 
    "sub_const_"  `isPrefixOf` f 
--    "div_const_"  `isPrefixOf` f
    = if length f' == 1 
      then Fun f' [b,c']
      else Fun f' (a:b:c':dims)
  where
    n  = read $ reverse $ takeWhile (/='_') $ reverse f
    c' = devectorizeIncrE sub c
    f' = if n == 1 then 
           case head f of
             'm' -> "*"
             'a' -> "+"
             's' -> "-"
             'd' -> "/"
         else reverse (reverse (show (n-1)) ++ dropWhile (/='_') (reverse f))
devectorizeIncrE sub (Fun "IDR" [_,posn,_,_]) = Fun "=" [posn, sub]
devectorizeIncrE sub (Fun "ID"  [_,posn,_,_]) = Fun "=" [posn, sub]
devectorizeIncrE sub (Fun f [a])
  | f `elem` ["log","exp"] = Fun f [devectorizeIncrE sub a]
devectorizeIncrE sub f@(Fun _ _) = error ("GenC.devectorizeIncrE: cannot devectorize " ++ show f ++ " with " ++ show sub)

devectorizeVec num v [val] = Assn v val
devectorizeVec num (V v sub) (val:lo:hi:dims) =
  Loop i lo hi [devectorizeVec (num+1) (V v (sub ++ [Var (V i [])])) (val:dims)]
  where i = "dvv_loop_var_" ++ show num

devectorizeE tm (Var v) = Var (devectorizeV tm v)
devectorizeE tm (Con c) = Con c
devectorizeE tm (Fun "sub" ((Var (V v el)):es)) = Var (V v (map (devectorizeE tm) (el++es)))
devectorizeE tm e@(Fun "vec" _) = error ("GenC.devectorizeE: vec not removed in: " ++ show e)
devectorizeE tm (Fun f (_:s:e:_))
  | "mult_const_" `isPrefixOf` f || "add_const_" `isPrefixOf` f
  , null $ indices $ inferCodeType tm e = devectorizeE tm (Fun "*" [s,e])

{- devectorizeE tm (Fun "vec" (val:dims)) = 
  case inferCodeType tm val of
    Type T0Int  _ -> Fun ("vec_i_" ++ show ((length dims) `div` 2)) (val : makeDims dims)
    Type T0Real _ -> Fun ("vec_r_" ++ show ((length dims) `div` 2)) (val : makeDims dims)
  where
    makeDims (_:hi:xs) = hi : makeDims xs
    makeDims [] = []
-}
devectorizeE tm (Fun f el) = Fun f (map (devectorizeE tm) el)
devectorizeE tm (CaseOf cv cs) = CaseOf (devectorizeE tm cv) (map (\ (e,f) -> (devectorizeE tm e, devectorizeE tm f)) cs)

devectorizeV tm (V ('#':i) el) = V ("dvv_loop_var_" ++ i) el
devectorizeV tm (V v el) = V v (map (devectorizeE tm) el)

addDimsF tm f = f { body = map (addDimsS tm) $ body f }

addDimsS tm (Loop i lo hi b) = Loop i lo hi (map (addDimsS tm) b)
addDimsS tm (If c t e) = If c (map (addDimsS tm) t) (map (addDimsS tm) e)
addDimsS tm (Assn v e) = Assn v (addDimsE tm e)
addDimsS tm (Incr v e) = Incr v (addDimsE tm e)
addDimsS tm (Call f ret arg)
  | f `elem` ["sample_Mult" , "mode_Mult" , "normalizeLog"] = Call f ret (map (addDimsE tm) arg ++ [lo',hi'])
  | f `elem` ["sample_NorMV", "mode_NorMV"]                 = Call f ret (map (addDimsE tm) (init arg) ++ [lo',hi'])
  -- "sample_NorMV", "mode_NorMV", 
  where 
    Type _ [C.Range _ lo hi] = inferCodeType tm (arg!!0)
    (lo', []) = codifyExpr tm lo
    (hi', []) = codifyExpr tm hi
addDimsS tm (Call f ret arg) = Call f ret (map (addDimsE tm) arg)
addDimsS tm (Comment c) = Comment c

addDimsE tm (Var (V id el)) = Var (V id $ map (addDimsE tm) el)
addDimsE tm (Con c) = Con c
addDimsE tm f0@(Fun f arg)
  | f `elem` ["sqrDiff"] = Fun f (map (addDimsE tm) arg ++ [lo',hi'])
  where 
    (lo,hi) = case inferCodeType tm (arg!!1) of
                Type _ [C.Range _ lo hi] -> (lo,hi)
                t -> error $ "GenC.addDimsE: cannot infer type of " ++ show (arg!!1) ++ " in " ++ show f0
    (lo', []) = codifyExpr tm lo
    (hi', []) = codifyExpr tm hi
addDimsE tm (Fun f arg)
  | f `elem` ["ldf_Mult" ] = Fun f (map (addDimsE tm) arg ++ [lo',hi'])
  | f `elem` ["ldf_NorMV"] = Fun f (map (addDimsE tm) (init arg) ++ [lo',hi'])
                            
  where 
    Type _ [C.Range _ lo hi] = inferCodeType tm (arg!!2)
    (lo', []) = codifyExpr tm lo
    (hi', []) = codifyExpr tm hi
addDimsE tm (Fun f arg) = Fun f $ map (addDimsE tm) arg
addDimsE tm (CaseOf cv cs) = CaseOf cv' (map (\ (e,f) -> (addDimsE tm e, addDimsE tm f)) cs)
  where cv' = addDimsE tm cv

findDeps (C.Range _ lo hi) = nub ((map unVar  (listify findDeps'  lo ++ listify findDeps'  hi)) ++
                                  (map unVar' (listify findDeps'' lo ++ listify findDeps'' hi)))
  where
    findDeps'  (C.V  id _) = True
    findDeps'' (C.Id id _) = True
    unVar  (C.V  id _) = id
    unVar' (C.Id id _) = id

