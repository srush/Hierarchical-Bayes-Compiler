-----------------------------------------------------------------------------
-- |
-- Module      :  Code
-- Project     :  HBC
-- Copyright   :  (c) Hal Daume III
-- License     :  Open
-- 
-- Maintainer  :  Hal Daume III <me@hal3.name>
-- Stability   :  stable
-- Portability :  portable
--
-- Abstract code generation
--
-----------------------------------------------------------------------------

module Code where

import Type
import Core(Const(..))
import qualified Core as C
import qualified Data.Map as M
import Data.Maybe
import Data.Char
import Data.List
import Control.Monad
import Control.Monad.State
import Util
import Marginalize
import Data.Generics hiding ((:*:))
import Data.Typeable

import qualified UnLift
import qualified Math

type Code = [Function]

type Id = String

data Function = 
     Function { 
       name       :: Id,
       returnVal  :: [Expr],
       returnType :: [Type],
       params     :: [(Id,Type)],
       tempVars   :: [(Id,Type)],  -- these needn't be created in body
       body       :: [Statement]
     } deriving (Eq, Ord, Typeable, Data)

data V = V Id [Expr] deriving (Eq, Ord, Typeable, Data)

data Statement = 
      Loop    { loopVar :: Id, loopBegin :: Expr, loopEnd :: Expr, loopBody :: [Statement] }
    | If      { condExp :: Expr, condThen :: [Statement], condElse :: [Statement]}
    | Assn    { assnVar :: V , assnVal :: Expr }
    | Incr    { incrVar :: V , incrVal :: Expr }
    | Call    { callFun :: Id, callRet :: [Expr], callArg :: [Expr] }  -- different languages handle return values differently
    | Comment { comment :: String }
    | Seq     Statement Statement
    deriving (Eq, Ord, Typeable, Data)

data Expr =
      Var V
    | Con C.Const
--    | Ind Expr [Expr]
    | Fun Id [Expr]
    | CaseOf Expr [(Expr,Expr)]
    | FuncPtr Id [Expr]
    deriving (Eq, Ord, Typeable, Data)

type TmpVar = ((Id,Type),[Statement])

-- in order to translate sums and products, we need to create
-- auxiliary variables.  all of these generated statements
-- are guaranteed to be Loops.  the id/type included is the
-- new id created and its type (to be added to "tempVars")
codifyExpr :: TypeMap -> C.Expr -> (Expr, [TmpVar])
codifyExpr tm (C.Var (C.V id [])) = (Var (V id []), [])
codifyExpr tm (C.Var (C.V id sl)) = (Var (V id sl'), sts)
  where (sl', sts) = codifyMany (codifySExpr tm) sl
codifyExpr tm (C.Con c)           = (Con c, [])

codifyExpr tm e0@(C.Func "sub" [a,b]) =
  case a' of
    Var (V a' ax') -> (Var (V a' (ax'++[b'])), stsA++stsB)
    Fun  "+" [Fun "vec" (vecVal:_), Var (V a' ax')] -> (Fun "+" [vecVal, Var (V a' (ax'++[b']))], stsA++stsB)
    Fun ".+" [lhs, Var (V a' ax')] -> (Fun ".+" [lhs, Var (V a' (ax'++[b']))], stsA++stsB)
    e -> (Fun "sub" [a',b'], stsA++stsB) -- error ("Code.codifyExpr: cannot codify " ++ show e ++ " in " ++ show e0)
  where (a', stsA) = codifyExpr tm a
        (b', stsB) = codifyExpr tm b

codifyExpr tm (C.Case cv cs) = (CaseOf cv' (zip csA' csB'), sts ++ sts' ++ sts'')
  where
    (cv' ,    sts  ) = codifyExpr tm cv
    (csA',    sts' ) = codifyMany (codifyExpr tm) $ map fst cs
    (csB',    sts'') = codifyMany (codifyExpr tm) $ map snd cs

{-
codifyExpr tm (C.Func "sub" [a,b]) = (Var (V a' (ax'++[b'])), stsA++stsB)
  where (Var (V a' ax'), stsA) = codifyExpr tm a
        (b', stsB) = codifyExpr tm b
-}

codifyExpr tm (C.Func f el)       = (Fun f el', sts)
  where (el', sts) = codifyMany (codifyExpr tm) el

codifyExpr tm sp@(C.SP _ _ _ [] ) = error ("Code.codifyExpr: got unnamed SP in: " ++ show sp)
codifyExpr tm sp@(C.SP b r e var) = (Var (V var []), ((var,typ),st):sts0'++sts1)
  where
    (rl,eNew) = gatherSP e
    
    typ = case M.lookup var tm of { Nothing -> error ("Code.codifyExpr: could not find type of sum/product " ++ show var ++ " in: " ++ show sp) ; Just t -> t }
    (e',sts0) = codifyExpr tm eNew
    (sts0',states0) = splitStatements sts0

    (st,sts1) = sumProductStatement tm var typ b (r:rl) e' states0

    gatherSP (C.SP b' r' e' _) | b == b' = let (rl,e0) = gatherSP e' in (r':rl, e0)
    gatherSP e = ([],e)

{-
codifyExpr tm sp@(C.SP b r e var) | null var  = error ("Code.codifyExpr: got unnamed SP in: " ++ show sp)
codifyExpr tm sp@(C.SP b r e var) = (Var (V var []), ((var,typ),st):sts0'++sts1)
  where
    typ = case M.lookup var tm of { Nothing -> error ("Code.codifyExpr: could not find type of sum/product " ++ show var ++ " in: " ++ show sp) ; Just t -> t }
    (e',sts0) = codifyExpr tm e
    (sts0',states0) = splitStatements sts0
    (st,sts1) = sumProductStatement tm var typ b r e' states0
-}


codifySExpr tm (C.Id id Nothing) = (Var (V id []), [])
codifySExpr tm (C.Id id (Just c)) = (Fun "+" [Var (V id []), Con c], [])
codifySExpr tm (C.Cn c) = (Con c, [])

sumProductStatement tm var typ b rangeList e (rest :: [Statement]) = 
  ((Assn var0 (if b then one else zero)) : loopBody, statements)
  where
    var0 = V var []

    (zero,zeroS) = mkVec (indices typ) $ Con (if baseType typ == T0Real then C.R 0 else C.I 0)
    (one ,oneS ) = mkVec (indices typ) $ Con (if baseType typ == T0Real then C.R 1 else C.I 1)

    mkVec [] e = (e, [])
    mkVec l  e = (Fun "vec" (e : l'), sts)
      where (l', sts) = codifyMany (codifyExpr tm) $ concatMap rangeToExpr l

    body0 = rest ++ [if b
                     then Assn var0 (Fun "*" [Var var0, e])
                     else Incr var0 e]

    (loopBody, statements) = 
      foldr (\ (C.Range id lo hi) (body, sts) ->
                 let (lo', stsLo) = codifyExpr tm lo
                     (hi', stsHi) = codifyExpr tm hi
                 in  ([Loop id lo' hi' body], ((id,tInt),[]) : sts ++ stsLo ++ stsHi)
            ) (body0, []) rangeList


{-
sumProductStatement tm var typ b (C.Range id lo hi) e rest = -- (C.SP b (C.Range id lo hi) e) =
  ([if doAssn then Assn var0 (if b then one else zero) else Comment "",
    Loop id lo' hi' $
      rest ++
      if doAssn 
      then [if b 
            then Assn var0 (Fun "*" [Var var0, e])
            else Incr var0 e]
      else []
   ],
   ((id,tInt),[]):stsLo ++ stsHi)
  where
    (var0,doAssn) = if head var == '~' then (V (drop 1 var) [], False) else (V var [], True)

    (lo', stsLo) = codifyExpr tm lo
    (hi', stsHi) = codifyExpr tm hi

    (zero,zeroS) = mkVec (indices typ) $ Con (if baseType typ == T0Real then C.R 0 else C.I 0)
    (one ,oneS ) = mkVec (indices typ) $ Con (if baseType typ == T0Real then C.R 1 else C.I 1)

    mkVec [] e = (e, [])
    mkVec l  e = (Fun "vec" (e : l'), sts)
      where 
        (l', sts) = codifyMany (codifyExpr tm) $ concatMap rangeToExpr l
-}


rangeToExpr (C.Range _ lo hi) = [lo,hi]
    

{-

fixRange tm sp e (C.Range v0 (C.Var (C.V "?" [])) (C.Var (C.V "?" []))) 
  | otherwise = error ("Code.fixRange: " ++ show (v0,varEq,e,sp,tm))
  where
    varEq = nub $ findEquality e

    findEquality (C.Func "=" [C.Var (C.V v []), e']) | v0 == v = [e']
    findEquality (C.Func "=" [e', C.Var (C.V v [])]) | v0 == v = [e']
    findEquality (C.Func _ el) = concatMap findEquality el
    findEquality (C.SP _ _ e _) = findEquality e
    findEquality _ = []
fixRange _ _ _ r = r
-}

--    (e' , stsE ) = codifyExpr tm e

{-
codifyLDF tm (_, dist, rl) = (e, sts ++ sts')
  where
    (dist', sts ) = codifyDistLDF tm dist
    (rl',   tm' ) = applyRanges tm rl dist'
    (e    , sts') = codifyExpr    tm rl'

    applyRanges tm []     e = (e , tm)
    applyRanges tm (r:rs) e = (e', M.insert (C.spVarName sp) tReal tm')
      where
        (e', tm') = applyRanges tm rs e
        sp        = C.SP False r e'
-}

codifyVar tm (C.V id []) = Var (V id [])
codifyVar tm (C.V id sl) = Var (V id (map (fst . codifySExpr tm) sl))

codifyDistLDF tm normIt (C.Dist var "IG" el) = (Fun "ldf_Gam"   (Con (if normIt then I 1 else I 0) : (Fun "/" [Con (R 1), codifyVar tm var]) : el'), sts)
  where (el', sts) = codifyMany (codifyExpr tm) el
codifyDistLDF tm normIt (C.Dist var "Delta" el) = (Con (C.R 0), [])
codifyDistLDF tm normIt (C.Dist var dist el) = (Fun ("ldf_"   ++ dist) ((Con (if normIt then I 1 else I 0)) : codifyVar tm var : el'), sts)
  where (el', sts) = codifyMany (codifyExpr tm) el
codifyDistLDF tm normIt ((C.:*:) a b) = (Fun "+" [a',b'], stsA ++ stsB)
  where (a', stsA) = codifyDistLDF tm normIt a
        (b', stsB) = codifyDistLDF tm normIt b
codifyDistLDF tm normIt ((C.:^:) a e) = (Fun "*" [e',a'], stsA ++ stsE)
  where (a', stsA) = codifyDistLDF tm normIt a
        (e', stsE) = codifyExpr tm e
codifyDistLDF tm normIt prod@(C.Prod r d var) 
  | null var  = error ("Code.codifyDistLDF: unnamed product variable found in: " ++ show prod)
  | otherwise = (Var (V var []), ((var,typ),st):sts0'++sts1)
  where
    typ = tReal
    tm' = M.insert var typ tm
    (d',sts0) = codifyDistLDF tm' normIt d
    (sts0',states0) = splitStatements sts0
    (st,sts1) = sumProductStatement tm var typ False [r] d' states0

codifyLDF tm collapsed (_, (C.V id _,_,_)) | id `elem` collapsed = (Con (C.R 0), [])
codifyLDF tm collapsed (nn, (_, (C.Dist _ dist _), _ )) | dist `elem` collapsed = (Con (C.R 0), [])
codifyLDF tm collapsed (nn, (_, dist, rl)) = codifyDistLDF tm True $ applyRanges 0 rl dist
  where
    applyRanges mm []     d = d
    applyRanges mm (r@(C.Range v _ _):rs) d =
      C.Prod r' (applyRanges (mm+1) rs d) ("ldfP" ++ show nn ++ "_" ++ show mm)
      where 
        off = filter (/=0) $ C.getOffsets v d
        r'  = case off of { [] -> r ; os -> C.applyRangeOffset (minimum os) (maximum os) r }

splitStatements sl = ([(i,[]) | (i,_) <- sl], concatMap snd sl)

codifyMany :: (a -> (b, [TmpVar])) -> [a] -> ([b], [TmpVar])
codifyMany f [] = ([], [])
codifyMany f (x:xs) =
  let (y ,sts ) = f x
      (ys,sts') = codifyMany f xs
  in  (y:ys, sts++sts')


------------------------------------------------------------------------------------------------------------------------------

makeLikFunction :: C.Core -> [Id] -> TypeMap -> [String] -> Function
makeLikFunction (C.Core dl) globals tm collapsed =
  Function { name       = "compute_log_posterior"
           , returnVal  = [ret]
           , returnType = [tReal]
           , params     = [(v, fromMaybe (error $ "makeLikFunction: Nothing on type lookup for " ++ show v) $ M.lookup v tm) 
                          | v <- globals
                          , not (isDimRefVar v)
                          , not ("tmp" `isPrefixOf` v)]
           , tempVars   = temps
           , body       = concatMap snd sts }
  where
    (el, sts) = codifyMany (codifyLDF tm collapsed) (zip [0..] dl)
    temps     = map fst sts
    ret       = foldr1 (\a b -> Fun "+" [a,b]) el

------------------------------------------------------------------------------------------------------------------------------

makeSampleFunction :: C.Decl -> TypeMap -> [Update] -> Maybe Bool -> Function
makeSampleFunction decl@(v0@(C.V sampVar varIdx), dist, rl) tm updates maximizeIt =
  Function { name       = "resample_" ++ sampVar
           , returnVal  = (Var (V sampVar [])) : map (Var . fst) newRet
           , returnType = typ0 : map snd newRet
           , params     = nub [(v, fromMaybe (error $ "Code.makeSampleFunction: Nothing on type lookup for " ++ show v ++ " in " ++ show tm) $ M.lookup v tm) 
                              | v <- myGlobals ++ newGlob
                              , not (isDimRefVar v)
                              , not ("tmp" `isPrefixOf` v)
                              , not (v `elem` rangeVars)] ++
                          case maximizeIt of { Just False -> [("iter", tInt)] ; _ -> [] }
           , tempVars   = temps'
           , body       = body'  }
  where
    rangeVars = [id | C.Range id _ _ <- rl]
    typ0@(Type t0 t0i) = fromMaybe (error $ "Code.makeSampleFunction: Nothing on type lookup for sampVar " ++ show sampVar) $ M.lookup sampVar tm
    myGlobals = sort $ nub $ C.getDeclGlobals decl

    {- we structure the sampling function as follows.  "sampVar" will always come
       in as a parameter, because it's considered one of my globals.  we will
       always *overwrite* this variable *and* set it as the return val (the return
       val will always be a simple Var).  this means that if we're generating code
       in a pass-by-reference language, and the variable is passed by reference,
       then we can just return void.  OTOH, if it's passed by value, we'll need
       to return it.  overwriting will also give us speedups in matlab, where
       this will not result in the creation of an temporary copy
    -}

    (body , temps , newGlob, newRet) = makeSampleBody v0 tm dist maximizeIt
    ((updBef, updAft), updTmp) = generateMarginalUpdates tm updates sampVar varIdx
    (body', temps') = foldr (addLoopRange tm) (concatMap snd updTmp ++ updBef ++ body ++ updAft, temps ++ map fst updTmp) rl


addLoopRange :: TypeMap -> C.Range -> ([Statement], [(Id,Type)]) -> ([Statement], [(Id,Type)])
addLoopRange tm (C.Range rid lo hi) (b,t) = 
  ( (concatMap snd (stsLo++stsHi)) ++ [Loop rid lo' hi' b]
  , (rid,tInt) : t ++ map fst (stsLo++stsHi))
  where
    (lo', stsLo) = codifyExpr tm lo
    (hi', stsHi) = codifyExpr tm hi
--    off = filter (/=0) $ getOffsets rid 

------------------------------------------------------------------------------------------------------------------------------

generateMarginalUpdates :: TypeMap -> [Update] -> Id -> [C.SExpr] -> (([Statement],[Statement]), [TmpVar])
generateMarginalUpdates tm updates id0 rl =
  case filter ((==id0).indexVariable) updates of
    [] -> (([],[]), [])
    up -> 
      let (stmts,idts) = unzip $ map (generateMarginalUpdate tm id0 rl) up
          (befS, aftS) = unzip stmts
      in  mytrace (show ("genMarg",((concat befS, concat $ reverse aftS), nub $ concat idts)))
          ((concat befS, concat $ reverse aftS), nub $ concat idts)

generateMarginalUpdate :: TypeMap -> Id -> [C.SExpr] -> Update -> (([Statement],[Statement]), [TmpVar])
generateMarginalUpdate tm id0 rl (Update _ isIncr _ varRem varAdd) 
  | mytrace (show ("generateMarginalUpdate",id0,rl,bef,aft,sts)) True
  = ((bef, aft), sts)
  where
    (remRL, remVar, remE) = varRem rl
    (addRL, addVar, addE) = varAdd rl

    (bef,befS) = mkS (remRL, remVar, {- MkCore.simplifyAllCoreE -} remE)
    (aft,aftS) = mkS (addRL, addVar, {- MkCore.simplifyAllCoreE -} addE)
--    (aft,aftS) = mkS $ MkCore.simplifyAllCoreE $ varAdd rl -- (map C.rangeIds rl)
    sts = befS ++ aftS

    mkS (ranges, v0, expr) =
      let (e0, tmp)   = codifyExpr tm expr
          (Var v, []) = codifyExpr tm (v0)
          s0          = if isIncr then Incr v e0 else Assn v e0
          (s, it)     = foldr (addLoopRange tm) ([s0], []) ranges
      in  (s, map (\x -> (x,[])) it ++ tmp)
    

------------------------------------------------------------------------------------------------------------------------------

makeDumpFunction :: C.Core -> C.Decl -> TypeMap -> Function
makeDumpFunction core@(C.Core decls) decl@(v0@(C.V sampVar varIdx), dist, rl) tm =
  Function { name       = "dump_" ++ sampVar
           , returnVal  = []
           , returnType = []
           , params     = nub ([(v, fromMaybe (error $ "Code.makeDumpFunction: Nothing on type lookup for " ++ show v) $ M.lookup v tm) | v <- myGlobals, not ("tmp" `isPrefixOf` v), not (v `elem` lhsVars), not (v `elem` rangeVars)])
           , tempVars   = temps
           , body       = body'  }
  where
    lhsVars = [id | (C.V id _,_,_) <- decls, id /= sampVar]
    rangeVars = [id | C.Range id _ _ <- rl]

    typ0@(Type t0 t0i) = fromMaybe (error $ "Code.makeDumpFunction: Nothing on type lookup for sampVar: " ++ show sampVar) $ M.lookup sampVar tm
    myGlobals = sort $ nub $ (sampVar : C.getDeclGlobals decl)

    (Var (V v0' _),[]) = codifyExpr tm (C.Var v0)

    (body,  temps )  = makeDumpBody 1 (Var (V v0' [])) tm typ0
    body' = (Call "printf_string" [] [Var (V sampVar [])]) : body ++ [Call "printf_newline" [] []]

    zero = case t0 of { T0Real -> Con (C.R 0) ; _ -> Con (C.I 0) }

makeDumpBody _ v0 tm (Type T0Int  []) = ([Call "printf_int"  [] [v0]], [])
makeDumpBody _ v0 tm (Type T0Real []) = ([Call "printf_real" [] [v0]], [])
makeDumpBody z (Var (V v0 v0i)) tm (Type t0 ((C.Range _ lo hi):t0i)) =
  ([Loop tIdx lo' hi' body''], map fst loV ++ map fst hiV ++ vars')
  where
    tIdx = "dvv_loop_var_" ++ show z
    (lo', loV) = codifyExpr tm lo
    (hi', hiV) = codifyExpr tm hi
    (body', vars') = makeDumpBody (z+1) (Var (V v0 (v0i ++ [(Var (V tIdx []))]))) tm (Type t0 t0i)
    body'' = body' ++ [Call "printf_sep" [] [Con (C.I (genericLength t0i))]]

    


------------------------------------------------------------------------------------------------------------------------------

makeInitializeFunction :: C.Core -> C.Decl -> TypeMap -> Function
makeInitializeFunction core@(C.Core decls) decl@(v0@(C.V sampVar varIdx), dist, rl) tm
  | mytrace (show (myGlobals,newGlob,lhsVars,body)) False = undefined
  | otherwise =
  Function { name       = "initialize_" ++ sampVar
           , returnVal  = [varNew]
           , returnType = [typ0]
           , params     = nub ([(v, fromMaybe (error $ "Code.makeInitializeFunction: Nothing on type lookup for " ++ show v) $ M.lookup v tm) 
                               | v <- myGlobals ++ newGlob
                               , not (isDimRefVar v)
                               , not ("tmp" `isPrefixOf` v)
                               , not (v `elem` lhsVars)
                               , not (v `elem` rangeVars)])
           , tempVars   = (sampVar, typ0) : temps''
           , body       = body''  }
  where
    varNew  = Var (V sampVar [])

    lhsVars = [id | (C.V id _,_,_) <- decls]
    rangeVars = [id | C.Range id _ _ <- rl]

    typ0@(Type t0 t0i) = fromMaybe (error $ "Code.makeInitializeFunction: Nothing on type lookup for sampVar: " ++ show sampVar) $ M.lookup sampVar tm
    myGlobals = sort $ nub $ C.getDeclGlobals decl

    (v0',[]) = codifyExpr tm (C.Var v0)

    (body,  temps , newGlob)  = makeInitializeBody v0' tm dist
    (body', temps')  = foldr (addLoopRange tm) (body, temps) rl
    (body'',temps'') = 
      if null t0i then (body',temps') else
        let (l',sts) = codifyMany (codifyExpr tm) $ concatMap rangeToExpr t0i
        in  ((Assn (V sampVar []) (Fun "vec" (zero:l'))) : body', map fst sts ++ temps')

    zero = case t0 of { T0Real -> Con (C.R 0) ; _ -> Con (C.I 0) }

makeMarginalInitialization :: TypeMap -> Code -> Id -> Function
makeMarginalInitialization tm code id =
  case find ((==("resample_" ++ id)).name) code of
    Nothing -> error ("Code.makeMarginalInitialization: cannot find resample function for " ++ id)
    Just f  ->
      let Type t0 t0i = fromMaybe (error $ "makeMarginalInitialization: Nothing on type lookup for " ++ show id) $ M.lookup id tm
          zero = case t0 of { T0Real -> Con (C.R 0) ; _ -> Con (C.I 0) }
          (l',[]) = codifyMany (codifyExpr tm) $ concatMap rangeToExpr t0i
      in  Function { name = "initialize_" ++ id
                   , returnVal  = returnVal  f
                   , returnType = returnType f
                   , params     = filter ((/=id).fst) $ params f
                   , tempVars   = [(id, Type t0 t0i)]
                   , body       = [
                                    Assn (V id []) (Fun "vec" (zero:l'))
                                  , Call (name f) [] (map (\ (id,_) -> Var (V id [])) $ params f)
                                  ] }

------------------------------------------------------------------------------------------------------------------------------

makeInitializeBody :: Expr -> TypeMap -> C.Dist -> ([Statement], [(Id,Type)], [Id]) -- final is new GLOBALS for multsym or delta
makeInitializeBody v0 tm dist0@(C.Dist var dist el) =
  case dist of
    "DirSym" ->
      let (el',tv) = codifyExpr tm (el !! 1)
      in  (concatMap snd tv ++ [Call "sample_DirSym" [v0] [one, el']], map fst tv, [])

    "PY"     ->
      let (el',tv) = codifyExpr tm (el !! 2)
      in  (concatMap snd tv ++ [Call "sample_DirSym" [v0] [one, (Fun "+" [el', Con (C.I 1)])]], map fst tv, [])

    "Dir"    ->
      let (el',tv) = codifyExpr tm (el !! 1)
      in  (concatMap snd tv ++ [Call "sample_DirSym" [v0] [one, el']], map fst tv, [])

    "Bin"    -> ([Call "sample_Bin"   [v0] [half]], [], [])
    "Poi"    -> ([Call "sample_Poi"   [v0] [one]], [], [])
    "Gam"    -> ([Call "sample_Gam"   [v0] [one , one]], [], [])
    "IG"     -> ([Call "sample_Gam"   [v0] [one , one], Assn v0var (Fun "/" [one, v0])], [], [])
    "Bet"    -> ([Call "sample_Bet"   [v0] [one , one]], [], [])
    "Nor"    -> ([Call "sample_Nor"   [v0] [zero, one]], [], [])
    "NorMV"  -> (concatMap snd sts ++ [Call "sample_NorMV" [v0] [zerV, one, one]], map fst sts, [])
      where 
        (zerV,sts) = 
          case typEl !! 0 of
            Just (Type _ dims) -> 
              let (l',sts) = codifyMany (codifyExpr tm) $ concatMap rangeToExpr dims
              in  (Fun "vec" (zero:l'), sts)
            t -> error ("Code.makeInitializeBody: don't know how to deal with type " ++ show t ++ " in NorMV")

    "Mult"   ->
      mytrace (show ("makeInitializeBody", v0, tm, dist0, typEl)) $
      case typEl !! 0 of
        Just (Type _ [C.Range _ (C.Con (C.I 1)) hi]) ->
          let (hi',tv) = codifyExpr tm hi
          in  (concatMap snd tv ++ [Call "sample_MultSym" [v0] [Con (C.I 1),hi']], map fst tv, C.getExprGlobals [] hi)
        _ -> error ("Code.makeInitializeBody: cannot infer type of Mult in " ++ show dist ++ ", typEl=" ++ show typEl ++ ", el=" ++ show el)

    "MultSym" ->
      let (el', tv) = codifyMany (codifyExpr tm) el
      in  (concatMap snd tv ++ [Call "sample_MultSym" [v0] el'], map fst tv, [])


--          in  (concatMap snd tv ++ [Call "sample_Mult" [v0] [Fun "vec" [Fun "/" [one, hi'], Con (C.I 1), hi']]], map fst tv)

    "Delta" -> 
        case v0 of
          Var v -> ([], [], [])
--      case typEl !! 0 of
--        Just (Type T0Real [C.Range _ (C.Con (C.I 1)) hi]) ->
--          let (hi',tv) = codifyExpr tm hi
--          in  (concatMap snd tv ++ [Call "add_const_r_1" [v0] [Con (C.I 1),hi']], map fst tv, C.getExprGlobals [] hi)
--          in  (concatMap snd tv ++ [Call "copy_vector" [v0] [Con (C.I 1),hi']], map fst tv, C.getExprGlobals [] hi)
--
--        _ -> error ("Code.makeInitializeBody: cannot infer type of " ++ show (el !! 0) ++ "; found " ++ show (typEl !! 0))
        


    d -> error ("Code.makeInitializeBody: don't know how to generate code for distribution " ++ show d)

  where typEl = map (inferType tm) el
        half  = Con (C.R 0.5)
        one   = Con (C.R 1)
        zero  = Con (C.R 0)
        Var v0var = v0

makeInitializeBody _ _ d = error ("Code.makeInitializeBody: expecting Dist, maybe you forgot to pass the prior?  Got " ++ show d)

------------------------------------------------------------------------------------------------------------------------------

makeSampleBody :: C.Var -> TypeMap -> C.Dist -> Maybe Bool -> ([Statement], [(Id,Type)], [Id], [(V,Type)])
makeSampleBody _ tm d@(C.Dist var "PY" el@[_,_,C.Var _vK,_]) maximizeIt =  -- special case for Pitman-Yor distributions
  (comm ++ sts ++ call, 
   ("tmp_old_K", tInt) : ("tmp_k", tInt) : {- map (\dvv -> (dvv,tInt)) dvvs ++ -} map fst tmpVars,
   map fst kVars, 
   (_codeK, tInt) : (map (\ (i,t) -> (V i [], t)) kVars))
  where
    (el'@[alpha, delta, _K@(Var _codeK), post], tmpVars) = codifyMany (codifyExpr tm) el
    sts = concatMap snd tmpVars
    v0@(Var v0v)  = fst $ codifyExpr tm (C.Var var)
    comm = [Comment ("Implements direct sampling from the following distribution:")
           ,Comment ("  " ++ show d)]


    -- find variables whos sizes depend on "K"
    C.V myId _ = var
    kVars = [ (v,t) | (v,t) <- M.toList tm
                    , t `typeDependsOn` _vK
                    , not (v == myId)
                    , not ("tmp" `isPrefixOf` v)
            ]

    dvvs = nub $ listify ("dvv_loop_var_" `isPrefixOf`) call

    -- generate code
    kit  = V "tmp_k" []
    oldK = V "tmp_old_K" []
    call = [ 
            Assn oldK _K,
            makeMaximize maximizeIt "PY" [_K,v0] (v0 : el'),
            Comment ("sample variables associated with new clusters: " ++ unwords (map fst kVars)),
            If (Fun ">" [_K, Var oldK])
               (concatMap (\ (v,t) -> remake 1 (V v []) t) kVars)
               []
           ]

    remake n x@(V id sl) (Type t0 (r@(C.Range _ lo hi):rs)) 
      | not (rangeDependsOn r _vK) =
          let (lo', []) = codifyExpr tm lo
              (hi', []) = codifyExpr tm hi
          in [Loop ("dvv_loop_var_" ++ show n) lo' hi'
                   (remake (n+1) (V id (sl ++ [Var (V ("dvv_loop_var_" ++ show n) [])])) (Type t0 rs))]
      | otherwise =
          let (lo', []) = codifyExpr tm lo
              (hi', []) = codifyExpr tm hi
              v' = V id (sl ++ [Var (V "tmp_k" [])])
          in  (Call "realloc" [Var x] [Var x, Fun "+" [_K, Con (C.I 1)]]) :
              case rs of
                [] -> [Assn v' (Con (C.I 0))]
                _  -> [Loop "tmp_k" 
                                (Fun "+" [Var oldK, Con (C.I 2)])
                                (Fun "+" [_K, Con (C.I 1)])
                                (genInterior n v' (Type t0 rs))]
    genInterior n x@(V id sl) (Type t0 []) = [Assn x (Con (C.I 0))]
    genInterior n x@(V id sl) (Type t0 (r@(C.Range _ lo hi):rs)) =
      let (lo', []) = codifyExpr tm lo
          (hi', []) = codifyExpr tm hi
      in  [Call "malloc" [Var x] [Fun "+" [Fun "-" [hi', lo'], Con (C.I 2)]],
           Loop ("dvv_loop_var_" ++ show n) lo' (Fun "+" [hi', Con (C.I 1)])
                (genInterior (n+1) (V id (sl ++ [Var (V ("dvv_loop_var_" ++ show n) [])])) (Type t0 rs))]

makeSampleBody _ tm d@(C.Dist var dist el) maximizeIt = -- this is the easy case: conjugacy has rescued us
  (comm ++ sts ++ sampleCall, map fst tmpVars, [], [])
  where
    (el', tmpVars) = codifyMany (codifyExpr tm) el
    sts = concatMap snd tmpVars
    v0@(Var v0v)  = fst $ codifyExpr tm (C.Var var)
    sampleCall = 
      case dist of
        "IG" -> [makeMaximize maximizeIt "Gam" [v0] el', Assn v0v (Fun "/" [Con (C.R 1), v0])]
        _    -> [makeMaximize maximizeIt dist  [v0] el']
    comm = [Comment ("Implements direct sampling from the following distribution:")
           ,Comment ("  " ++ show d)]

makeSampleBody v0@(C.V sampVar varIdx) tm dist maximizeIt
  | t0 == T0Int && length t0i == length varIdx &&     -- check if it's discrete
    isJust varOcc && 
    (dist0 == "Mult" || dist0 == "MultSym") &&               -- and appears in a multinomial
    isJust typTh && thLoIsOne                         -- make sure we can figure out the dimensions
    = (comm ++ body, 
        (tPost, Type T0Real rtheta) :
        (tIdx , tInt) :
        map fst stsHi ++
        map fst stsD,
       C.getExprGlobals [] hi,
       [])
            
  where
    Type t0 t0i = fromMaybe (error $ "Code.makeSampleBody (Mult): Nothing on type lookup for sampVar " ++ show sampVar) $ M.lookup sampVar tm
    varOcc      = C.findVariableOccurance v0 dist
    Just (C.Dist _ dist0 (theta:rest)) = varOcc
    typTh       = inferType tm theta
    rtheta@[C.Range _ lo hi] =
      if dist0 == "Mult"
      then case typTh of
             Just (Type _ rtheta@[_]) -> rtheta
             z -> error $ "Code.makeSampleBody (Mult): got typTh = " ++ show typTh
      else [C.Range "multSymIdx" (C.Con (C.I 1)) (rest !! 0)]

    thLoIsOne = lo == C.Con (C.I 1)
    {- to create the body, we need a temporary R[hi] to store the log
       probabilities.  we also need a temporary Z to iterate over these
       positions.  we fill in each position with a sum of ldfs.  then,
       we normalize and sample a multinomial -}
    tPost = makeTmpVar "post" v0
    tIdx  = makeTmpVar "idx"  v0

    (hi',stsHi0)    = codifyExpr tm hi
    (stsHi,stateHi) = splitStatements stsHi0

    Just dist'      = C.replaceVar v0 tIdx dist

    (df, stsD0)     = codifyDistLDF tm False dist'
    (stsD,stateD)   = splitStatements stsD0

    body =
        stateHi ++ 
        [ Assn (V tPost []) (Fun "vec" [Con (C.R 0), Con (C.I 1), hi'])
        , Loop tIdx (Con (C.I 1)) hi'
               (stateD ++ 
                [Assn (V tPost [Var (V tIdx [])]) df]
               )
        , Call "normalizeLog" [] [Var (V tPost [])]
        , makeMaximize maximizeIt "Mult" [fst $ codifyExpr tm (C.Var v0)] [Var (V tPost [])]
        ]
    comm = [Comment ("Implements multinomial sampling from the following distribution:")
           ,Comment ("  " ++ show dist)]

makeSampleBody v0@(C.V sampVar varIdx) tm dist maximizeIt
  | mytrace ("makeSampleBody: " ++ sampVar ++ ": " ++ show (t0,(length t0i,length varIdx),varOcc,dist0)) False = undefined
  | t0 == T0Int && length t0i == length varIdx &&     -- check if it's discrete
    isJust varOcc && dist0 == "Bin"                   -- and appears in a binomial
    = (comm ++ body, 
        (tPostT, tReal) :
        (tPostF, tReal) :
--Type T0Real [C.Range "" (C.Con (C.I 1)) (C.Con (C.I 2))]) :
        (tIdx , tInt) :
        map fst stsD,
       C.getExprGlobals [] (C.Con (C.I 2))
      ,[])
            
  where
    Type t0 t0i = fromMaybe (error $ "Code.makeSampleBody (Bin): Nothing on type lookup for sampVar " ++ show sampVar) $ M.lookup sampVar tm
    varOcc      = C.findVariableOccurance v0 dist
    Just (C.Dist _ dist0 _) = 
      case varOcc of
        Just (C.Dist _ dist0 _) -> varOcc
        _ -> error ("Code.makeSampleBody (Bin): varOcc = " ++ show varOcc)

    {- to create the body, we need a temporary R[hi] to store the log
       probabilities.  we also need a temporary Z to iterate over these
       positions.  we fill in each position with a sum of ldfs.  then,
       we normalize and sample a multinomial -}
    tPostT = makeTmpVar "post_true" v0
    tPostF = makeTmpVar "post_fals" v0
    tIdx   = makeTmpVar "idx"       v0

    Just dist'      = C.replaceVar v0 tIdx dist

    (df, stsD0)     = codifyDistLDF tm False dist'
    (stsD,stateD)   = splitStatements stsD0

    body =
        [ Assn (V tIdx   []) (Con (C.I 1))]  ++
        stateD ++
        [ Assn (V tPostT []) df
        , Assn (V tIdx   []) (Con (C.I 0)) ] ++
        stateD ++
        [ Assn (V tPostF []) df
        , Assn (V tPostT []) (Fun "exp" [Fun "-" [Var (V tPostT []), Fun "addLog" [Var (V tPostT []), Var (V tPostF [])]]])
        , makeMaximize maximizeIt "Bin" [fst $ codifyExpr tm (C.Var v0)] [Var (V tPostT [])]
        ]

{-
--        stateHi ++ 
        [ Assn (V tPost []) (Fun "vec" [Con (C.R 0), Con (C.I 0), Con (C.I 1)])
        , Loop tIdx (Con (C.I 1)) (Con (C.I 2))
               (stateD ++ 
                [Assn (V tPost [{-Fun "+" [-}Var (V tIdx []){-, Con (C.I 1)]-}]) df]
               )
        , Call "normalizeLog" [] [Var (V tPost [])]
        , Call (if maximizeIt then "mode_Bin" else "sample_Bin")  [fst $ codifyExpr tm (C.Var v0)] [Var (V tPost [Con (C.I 1)])]
        ]
-}

    comm = [Comment ("Implements binomial sampling from the following distribution:")
           ,Comment ("  " ++ show dist)]

makeSampleBody v0@(C.V sampVar varIdx) tm dist Nothing = 
    ("Implementing Metropolis sampling for " ++ show v0 ++ " because it does not appear in a recognizable form")
    `issueWarning`
    (body, 
     (unV backupVar,typ0):
     (unV loglikVal,tReal):
     (unV unifVal,  tReal):
     priorVars ++ map fst loglikSts,
     priorIds ++ [],
     []
    )
  where
    (prior,lik) = case splitPriorLikelihood v0 (Nothing,Nothing) dist of
                    (Just prior, Just lik) -> (prior, lik)
                    other -> error $ "Code.makeSampleBody: splitPriorLikelihood on variable " ++ show v0 ++ " and distribution " ++ show dist ++ " returned " ++ show other

    (priorSts, priorVars, priorIds, []) = makeSampleBody v0 tm prior Nothing

    unV (V x []) = x

    {- method:
         (1) compute the log-likelihood with the current value
         (2) back up the current value
         (3) sample a new value from the prior
         (4) compute the log-likelihood of the sampled value
         (5) choose to accept/reject... if the latter, restore the original value
         -}

    v0'@(Var v0var') = codifyVar tm v0

    typOrig = fromMaybe (error $ "Code.makeSampleBody (Metropolis): Nothing on type lookup for sampVar " ++ show sampVar) $ M.lookup sampVar tm

    typ0@(Type t0 t0i) = case typOrig of { Type t0 t0i -> Type t0 (resolvePoundType varIdx $ drop (length varIdx) t0i) }

    backupVar = V (makeTmpVar "backup" v0) []
    (loglikEl, loglikSts) = codifyLDF tm [] (0, (v0, lik, []))

    loglikVal = V (makeTmpVar "loglik" v0) []
    unifVal   = V (makeTmpVar "unifrand" v0) []

    body = 
      [Comment "Code.makeSampleBody: I don't know how to sample in the following distribution; perhaps conjugacy application failed?"
      ,Comment ("  " ++ show dist)
      ,Comment "Temporary solution: use an independence Metropolis step drawn from the prior!"] ++
      -- compute log-likelihood
      concatMap snd loglikSts ++
      [Assn loglikVal (Fun "-" [Con (C.R 0), loglikEl])] ++ 
      -- backup old value
      [genAssn (zip t0i [1..]) backupVar v0'] ++
      -- resample
      priorSts ++
      -- recompute log-likelihood
      concatMap snd loglikSts ++
      [Incr loglikVal loglikEl] ++
      -- now, loglikVal stores log(lik-orig / lik-new)
      -- generate a uniform random variable u and check to see if we should reject (i.e., log(u) < loglikVal)
      [Call "sample_Unif" [Var unifVal] [Con (C.R 0), Con (C.R 1)]
      ,If (Fun "<" [Fun "log" [Var unifVal], Var loglikVal])
          [genAssn (zip t0i [1..]) v0var' (Var backupVar)]
          []
      ]

    genAssn []         lhs rhs = Assn lhs rhs
    genAssn ((i,n):is) lhs rhs = Loop loopV lo' hi' [genAssn is lhs' rhs']
      where
        C.Range _ lo hi = i
        (lo', stsLo) = codifyExpr tm lo
        (hi', stsHi) = codifyExpr tm hi
        lhs' = case lhs of { V id el -> V id (el ++ [loopV']) }
        rhs' = case rhs of { Var (V id el) -> Var (V id (el ++ [loopV'])) ; _ -> Fun "sub" [rhs, loopV'] }
        loopV = "dvv_loop_var_" ++ show n
        loopV' = Var (V loopV [])


splitPriorLikelihood v0 (pr0,lik0) d =
  case d of
    C.Dist v {- (C.V v _) -} _ _ 
      | v == v0   -> (addTo pr0 d, lik0)
    a C.:*: b     -> splitPriorLikelihood v0 (splitPriorLikelihood v0 (pr0,lik0) a) b
    _             -> (pr0, addTo lik0 d)
  where
    addTo Nothing  x = Just x
    addTo (Just y) x = Just (y C.:*: x)


makeTmpVar str (C.V v l) = "tmp_" ++ str ++ "_" ++ v ++ "_" ++ show (length l)

------------------------------------------------------------------------------------------------------------------------------

-- removeID: remove occurances of the ID vector when possible
removeID :: TypeMap -> Code -> Code
removeID tm = map (\f -> 
                       let res   = map (removeIDS tm) $ body f
                           body' = concatMap fst res
                           ids   = (nub $ concatMap snd res) \\ map fst (params f)
                       in  f { body = body' , params = params f ++ zip ids (repeat tInt) }
                  )

removeIDS :: TypeMap -> Statement -> ([Statement], [Id])
removeIDS tm (Loop i lo hi b) = 
  let res = map (removeIDS tm) b
  in  ([Loop i lo hi (concatMap fst res)], nub $ concatMap snd res)
removeIDS tm (If c t e) =
  let t' = map (removeIDS tm) t
      e' = map (removeIDS tm) e
  in  ([If c (concatMap fst t') (concatMap fst e')], nub (concatMap snd t' ++ concatMap snd e'))
removeIDS tm (Assn (V v sl) e) 
  | Just (val,idx) <- conditionalID e = ([Incr (V v (sl++[hi0])) (Fun "-" [val, Var (V v (sl++[idx]))]),
                                          Assn (V v (sl++[idx])) val]
                                        , nub $ codeIdsE hiVar)
  | otherwise                         = ([Assn (V v sl) e], [])
  where 
    hiVar = case M.lookup v tm of
              Just (Type _ r@(_:_)) -> fst $ codifyExpr tm $ C.rangeHi $ last r
    hi0   = Fun "+" [hiVar, Con (C.I 1)]
removeIDS tm (Incr (V v sl) e)
  | Just (val,idx) <- conditionalID e = ([Incr (V v (sl++[hi0])) val,
                                          Incr (V v (sl++[idx])) val]
                                        , nub $ codeIdsE hiVar)
  | otherwise                         = ([Incr (V v sl) e], [])
  where 
    hiVar = case M.lookup v tm of
              Just (Type _ r@(_:_)) -> fst $ codifyExpr tm $ C.rangeHi $ last r
    hi0   = Fun "+" [hiVar, Con (C.I 1)]
removeIDS hi0 x = ([x], [])

conditionalID :: Expr -> Maybe (Expr, Expr)
conditionalID (Fun "ID" (idx:_)) = Just (Con (C.I 1), idx)
conditionalID (Fun "IDR" (idx:_)) = Just (Con (C.R 1), idx)
conditionalID (Fun ".*" [a,b]) =
  case conditionalID b of
    Just (val, idx) -> Just (Fun "*" [val,a], idx)
    Nothing -> Nothing
conditionalID (Fun "*" [a,b]) =
  case conditionalID b of
    Just (val, idx) -> Just (Fun "*" [Fun "sub" [a,idx],val], idx)
    Nothing -> Nothing
conditionalID (Fun fn [c@(Con _), e])
  | fn `elem` ["-",".-"] = 
    case conditionalID e of
      Nothing -> Nothing
      Just (val, idx) -> Just (Fun fn [c, val], idx)
conditionalID _ = Nothing

------------------------------------------------------------------------------------------------------------------------------

removeSub :: Code -> Code
removeSub = map removeSubF

removeSubF f = f { returnVal = liftM removeSubE $ returnVal f
                 , body      = map   removeSubS $ body f      }

removeSubS (Loop id lo hi s) = Loop id (removeSubE lo) (removeSubE hi) (map removeSubS s)
removeSubS (If c t e) = If (removeSubE c) (map removeSubS t) (map removeSubS e)
removeSubS (Assn v e) = Assn (removeSubV v) (removeSubE e)
removeSubS (Incr v e) = Incr (removeSubV v) (removeSubE e)
removeSubS (Call f r a) = Call f (map removeSubE r) (map removeSubE a)
removeSubS (Comment c) = Comment c

removeSubV (V id e) = V id $ map removeSubE e

removeSubE (Fun "sub" ((Fun f [a,b]):el))
  | f `elem` [ "+", "-", "*", "/"] = removeSubE (Fun f [Fun "sub" (a:el), Fun "sub" (b:el)])
  | f `elem` [".+",".-",".*","./"] = removeSubE (Fun f [a, Fun "sub" (b:el)])
removeSubE (Fun "sub" ((Fun "vec" [a,_,_]):_)) = a
removeSubE (Fun "sub" ((Fun "vec" (a:_:_:rest)):_:el)) = removeSubE (Fun "sub" ((Fun "vec" (a:rest)) : el))
removeSubE (Fun "sub" ((Fun "ID"  [p,_,_]):[v])) = Fun "=" [p,v]
removeSubE (Fun "sub" ((Fun "IDR" [p,_,_]):[v])) = Fun "=" [p,v]
removeSubE (Fun "sub" ((Var (V id e0)):el)) = Var $ V id $ map removeSubE (e0++el)
removeSubE (Var v) = Var $ removeSubV v
removeSubE (Con c) = Con c
removeSubE (Fun i e) = Fun i $ map removeSubE e
removeSubE (CaseOf cv cs) = CaseOf (removeSubE cv) (map (\ (e,f) -> (removeSubE e, removeSubE f)) cs)

------------------------------------------------------------------------------------------------------------------------------

-- giveNewVarNames :: Code -> Code
giveNewVarNames map0 m = evalState (mapM giveF m) (map0, 0)

giveF f = do
  mapM (fixName.fst) (params f)
  rv <- mapM giveE (returnVal f)
  tv <- mapM  giveIT $ tempVars  f
  b  <- mapM  giveS  $ body      f
  mapM (unfixName.fst) (params f)
  return (f { returnVal = rv , tempVars = tv , body = b })

fixName   n = get >>= \ (m,i) -> put (M.insert n n m, i)
unfixName n = get >>= \ (m,i) -> put (M.delete n   m, i)

giveIT (i,t) = do
  i' <- getName i
  return (i',t)

giveS (Loop v lo hi b) = do
  v'  <- getName v
  lo' <- giveE   lo
  hi' <- giveE   hi
  b'  <- mapM giveS b
  return (Loop v' lo' hi' b')
giveS (If c t e) = do
  c' <- giveE c
  t' <- mapM giveS t
  e' <- mapM giveS e
  return (If c' t' e')
giveS (Assn v e) = do
  v' <- giveV v
  e' <- giveE e
  return (Assn v' e')
giveS (Incr v e) = do
  v' <- giveV v
  e' <- giveE e
  return (Incr v' e')
giveS (Call f r a) = do
  r' <- mapM giveE r
  a' <- mapM giveE a
  return (Call f r' a')
giveS (Comment c) = return (Comment c)

giveV (V i e) = do
  i' <- getName i
  e' <- mapM giveE e
  return (V i' e')

giveE (Var v) = giveV v >>= return . Var
giveE (Con c) = return (Con c)
giveE (Fun i e) = mapM giveE e >>= return . Fun i

getName n = get >>= \ (m,i) ->
  case M.lookup n m of
    Just n' -> return n'
    Nothing -> do
      let (n',i') = makeName m i
      let m' = M.insert n n' m
      put (m',i')
      return n'
  where
    makeName m i 
      | n `M.member` m = makeName m (i+1)
      | otherwise      = (n, i+1)
      where n = makeName0 i
          
    makeName0 i
      | i < 26    = [chr (i+97)]
      | otherwise = (chr ((i `mod` 26)+97)) : makeName0 (i `div` 26)

------------------------------------------------------------------------------------------------------------------------------

rhsIdsF f  = concatMap codeIdsE (returnVal f) ++ concatMap rhsIdsS (body f)

rhsIdsS (Loop id lo hi b) = id : codeIdsE lo ++ codeIdsE hi ++ concatMap rhsIdsS b
rhsIdsS (If c t e) = codeIdsE c ++ concatMap rhsIdsS (t++e)
rhsIdsS (Assn v e) = codeIdsE e
rhsIdsS (Incr v e) = codeIdsE e
rhsIdsS (Call _ r a) = concatMap codeIdsE a
rhsIdsS (Comment _) = []
rhsIdsS (a `Seq` b) = rhsIdsS a ++ rhsIdsS b


codeIdsF f = concatMap codeIdsE (returnVal f) ++ concatMap codeIdsS (body f)

codeIdsS (Loop id lo hi b) = id : codeIdsE lo ++ codeIdsE hi ++ concatMap codeIdsS b
codeIdsS (If c t e) = codeIdsE c ++ concatMap codeIdsS (t++e)
codeIdsS (Assn v e) = codeIdsV v ++ codeIdsE e
codeIdsS (Incr v e) = codeIdsV v ++ codeIdsE e
codeIdsS (Call _ r a) = concatMap codeIdsE (r ++ a)
codeIdsS (Comment _) = []
codeIdsS (a `Seq` b) = codeIdsS a ++ codeIdsS b

codeIdsE (Var v) = codeIdsV v
codeIdsE (Con _) = []
codeIdsE (Fun _ e) = concatMap codeIdsE e
codeIdsE (CaseOf cv cs) = codeIdsE cv ++ concatMap (codeIdsE.fst) cs ++ concatMap (codeIdsE.snd) cs

codeIdsV (V i e) = i : concatMap codeIdsE e

------------------------------------------------------------------------------------------------------------------------------

instance Show Function where
  showsPrec _ f =
    showString "Function " . showString (name f) . showChar '(' . showsParams (params f) . showChar ')' . showChar '\n' .
    (foldr (\x a -> showsTempVar x . a) id (tempVars f)) .
    (foldr (\x a -> showsPrec 1 x . a) id (body f)) .
    (case returnVal f of
       [] -> id
       e  -> showString "  Return " . showsPrec 0 e . showChar '\n') 
    where
      showsParams [] = id
      showsParams [(id,t)]    = showString id . showString " : " . shows t
      showsParams ((id,t):xs) = showString id . showString " : " . shows t . showString ", " . showsParams xs

      showsTempVar (id,t) = showString "  temporary " . showString id . showString " : " . shows t . showChar '\n'

instance Show Statement where
  showsPrec i s = showString (replicate (i*2) ' ') . showSt s
    where
      showSt (Loop v lo hi b) = 
        showString "For " . showString v . showString " = " . shows lo . showString " to " . shows hi . showString " do \n" . 
        foldr (\x a -> showsPrec (i+1) x . a) id b
      showSt (If cond thenS elseS) =
        showString "If " . shows cond . showString " Then\n" .
        foldr (\x a -> showsPrec (i+1) x . a) id thenS .
        (if null elseS then id else
          showString (replicate (i*2) ' ') . showString "Else \t {-- " . shows cond . showString " --}\n" .
          foldr (\x a -> showsPrec (i+1) x . a) id elseS)
      showSt (Assn v e) = shows v . showString " := " . shows e . showChar '\n'
      showSt (Incr v e) = shows v . showString " += " . shows e . showChar '\n'
      showSt (Call f [] e) = showString f . showChar '(' . showsParams e . showChar ')' . showChar '\n'
      showSt (Call f rl e) = showChar '[' . showsParams rl . showString "] <- " . showString f . showChar '(' . showsParams e . showChar ')' . showChar '\n'
      showSt (Comment s)   = showString " {-- " . showString s . showString " --}\n"

      showsParams []     = id
      showsParams [e]    = shows e
      showsParams (e:es) = shows e . showString ", " . showsParams es

instance Show V where
  showsPrec _ (V v []) = showString v
  showsPrec _ (V v el) = showString v . showString "_{" . showsParams el . showChar '}'
    where
      showsParams []     = id
      showsParams [e]    = shows e
      showsParams (e:es) = shows e . showString ", " . showsParams es

instance Show Expr where
  showsPrec _ (Var v) = shows v
  showsPrec _ (Con c) = shows c
--  showsPrec _ (Ind e []) = shows e
--  showsPrec _ (Ind e sl) = shows e . showString "_{" . showsParams sl . showChar '}'
  showsPrec _ (Fun f el) 
    | length el == 2 && not (any isAlphaNum f) = showChar '(' . shows (el!!0) . showChar ')' . showString f . showChar '(' . shows (el!!1) . showChar ')'
    | otherwise = showString f . showString "(" . showsParams el . showChar ')'
    where
      showsParams []     = id
      showsParams [e]    = shows e
      showsParams (e:es) = shows e . showString ", " . showsParams es
  showsPrec i (CaseOf cv cs) = showString "case " . shows cv . showString " of {" . showCases cs . showString " }"
    where
      showCases [] = id
      showCases ((e,r):rs) = showChar ' ' . showsPrec i e . showString " :> " . showsPrec i r . if null rs then id else (showString " ;" . showCases rs)
  showsPrec i (FuncPtr f args) = showChar '*' . showChar '(' . showsPrec i (Fun f args) . showChar ')'

inferCodeType :: TypeMap -> Expr -> Type
inferCodeType tm (Var (V ('#':_) _)) = tInt
inferCodeType tm (Var (V v sl)) =
  case M.lookup v tm of -- `mplus` M.lookup ('~':v) tm of
    Nothing -> if '*' == head v && '@' `elem` v 
               then tInt 
               else error ("Code.inferCodeType: cannot find type of: " ++ v)
    Just (Type t0 t0i) -> 
        if length sl > length t0i
        then error ("Code.inferCodeType: too many subscripts on: " ++ v)
        else Type t0 (everywhere (mkT resolveTypePointer) $ drop (length sl) t0i)   -- TODO: if t0i contains # we need to resolve based on sl!
  where
    resolveTypePointer ('#':z)
      | all isDigit z && read z <= length sl =
          case sl !! (read z - 1) of
            Var (V i0 []) -> i0
            _ -> error $ "Code.inferCodeType.resoveTypePointer: found type pointer to non-Var expr: " ++ show (sl !! (read z - 1))
    resolveTypePointer v = v
        
{-    resolveTypePointer (C.V ('#':z) [])
      | all isDigit z && read z <= length sl =
          case sl !! (read z - 1) of
            Var (V i0 []) -> C.V i0 []
            _ -> error $ "Code.inferCodeType.resoveTypePointer: found type pointer to non-Var expr: " ++ show (sl !! (read z - 1))
    resolveTypePointer v = v            -}

inferCodeType tm (Con (C.I _)) = tInt
inferCodeType tm (Con (C.R _)) = tReal
inferCodeType tm (Fun f el) = fromJust $ getFuncRange tm f (map (Just . inferCodeType tm) el) (Just $ map codeE2coreE el)
inferCodeType tm (CaseOf cv cs) = inferCodeType tm $ snd $ head cs

codeE2coreE (Var (V id el)) = C.Var (C.V id (map (fromJust . C.exprToSExpr . codeE2coreE) el))
codeE2coreE (Con c) = C.Con c
codeE2coreE (Fun i el) = C.Func i (map codeE2coreE el)


{-
-- the purpose of liftVecF is to replace functions on vectors with
-- vector variables plus computation for those variables.  liftVecF
-- effectively accomplishes two orthogonal tasks: first, it does the
-- actual lifting; second, it replaces the lifted computations with
-- explicit loops so that everything happens at the scalar level.

liftVecF :: TypeMap -> Function -> Function
liftVecF tm f = removeSubF $
                f { body     = newVarsBody ++ concat body'
                  , tempVars = tempVars f ++ newTemps }
  where
    (body', newVars, _) = liftMany liftVecS tm 0 $ body f
    newVarsBody         = mapMaybe thr3 newVars
    newTemps            = [(id,t) | (Var (V id []), t, _) <- newVars]


liftVecS tm nn (Loop id lo hi b) = (zHereInit ++ [Loop id lo' hi' (concat b')], zHereNoInit ++ zUp, nn2)
  where
    (lo',z0,nn0) = liftVecE tm nn  lo
    (hi',z1,nn1) = liftVecE tm nn0 hi
    (b' ,z2,nn2) = liftMany liftVecS tm nn1 b
    (zHere,zUp)  = partition (dependsOn id) (z0++z1++z2)
    zHereInit    = mapMaybe thr3 zHere
    zHereNoInit  = [(v,t,Nothing) | (v,t,_) <- zHere]

liftVecS tm nn (If c t e) = ([If c' (concat t') (concat e')], zc++zt++ze, nn''')
  where
    (c', zc, nn')   = liftVecE tm nn c
    (t', zt, nn'')  = liftMany liftVecS tm nn'  t
    (e', ze, nn''') = liftMany liftVecS tm nn'' e

--liftVecS tm nn (Assn v (Fun "vec" el)) = liftVecS tm nn (Call "vec" [] ((Var v):el))
--liftVecS tm nn (Assn v (Fun "ID"  el)) = liftVecS tm nn (Call "ID"  [] ((Var v):el))
--liftVecS tm nn (Assn v (Fun "IDR" el)) = liftVecS tm nn (Call "IDR" [] ((Var v):el))

liftVecS tm nn (Assn v e) =
  case inferCodeType tm e of
    Type _ []    -> ([Assn v e'], zz, nn')
      where
        (e', zz, nn') = liftVecE tm nn e

    Type _ (r:_) -> (stmts, (var, tInt, Nothing) : z, nn')
      where 
        id  = "vec_var_" ++ show nn
        var = Var (V id [])
        v'  = case v of { V id el -> V id (el ++ [var]) }
        C.Range _ lo hi = r
        (lo',[]) = codifyExpr tm lo
        (hi',[]) = codifyExpr tm hi

        (stmts, z, nn') = liftVecS tm (nn+1) (Loop id lo' hi' [Assn v' (Fun "sub" [e,var])])

liftVecS tm nn (Incr v e) =
  case inferCodeType tm e of
    Type _ []    -> ([Incr v e'], zz, nn')
      where
        (e', zz, nn') = liftVecE tm nn e

    Type _ (r:_) -> (stmts, (var, tInt, Nothing) : z, nn')
      where 
        id  = "vec_var_" ++ show nn
        var = Var (V id [])
        v'  = case v of { V id el -> V id (el ++ [var]) }
        C.Range _ lo hi = r
        (lo',[]) = codifyExpr tm lo
        (hi',[]) = codifyExpr tm hi

        (stmts, z, nn') = liftVecS tm (nn+1) (Loop id lo' hi' [Incr v' (Fun "sub" [e,var])])
 
liftVecS tm nn (Call f r a) = result
  where
    -- any arg that's a scalar can stay put; anything else must be lifted (but only one level!)
    scalar           = map isScalarOrVar a
    ((nn',assn), a') = mapAccumL makeArgs (nn,[]) (zip a scalar)

    -- now, we need to lift all the assns
    (assn', assnVars, assnNN) = liftMany liftVecS tm nn' (map snd assn)

    -- we need to add types for the new variables
    newTmp = [(Var v, typ, Nothing) | (typ, Assn v _) <- assn]

    -- our result is the assignments followed by the original call; our new tvs are those returned by the recursion
    result = (concat assn' ++ [Call f r a'], newTmp ++ assnVars, assnNN)

    -- the things that have to be lifted are non-vector, non-vars; for everything else, return the type
    isScalarOrVar (Var _) = Nothing
    isScalarOrVar e = 
      case inferCodeType tm e of
        Type _ [] -> Nothing
        typ       -> Just typ

    -- replace vector args *and* return associated assignments
    makeArgs (nn,assn) (a,Nothing ) = ((nn  ,           assn), a)
    makeArgs (nn,assn) (a,Just typ) = ((nn+1,(typ,Assn v a):assn), Var v)
      where v = V ("vec_var_" ++ show nn) []

liftVecS tm nn (Comment s) = ([Comment s], [], nn)

liftVecE tm nn (Var v) = (Var v, [], nn)
liftVecE tm nn (Con c) = (Con c, [], nn)
liftVecE tm nn (CaseOf v cases) = (CaseOf v cases', zz, nn')
  where
    (rhs, zz, nn') = liftMany liftVecE tm nn (map snd cases)
    cases'         = zip (map fst cases) rhs
liftVecE tm nn e@(Fun f args) =
  case inferCodeType tm e of
    Type _ [] -> (Fun f args', zz, nn')
    typ       -> (Fun f args', (var,typ,(Just $ Assn (V id []) e)):zz,nn'+1)
      where
        id  = "vec_var_" ++ show nn'
        var = Var (V id [])
  where
    (args', zz, nn') = liftMany liftVecE tm nn args

{-
liftVecE tm nn (Var v) = (Var v, [], nn)
liftVecE tm nn e =
  case inferCodeType tm e of
    Type _ [] -> (e, [], nn)
    typ       -> (var, [(id, typ, Assn var e)], nn+1)
      where
        id  = "vec_var_" ++ show nn
        var = Var (V id [])
-}
-}

dependsOn id (_,t,_)      | id `elem` map C.rangeIds (indices t) = True
dependsOn id (_,_,Just e) | id `elem` codeIdsS e = True
dependsOn _ _ = False

liftMany f tm nn [] = ([], [], nn)
liftMany f tm nn (x:xs) = 
  let (y,  b,  nn1) = f tm nn x
      (ys, bs, nn2) = liftMany f tm nn1 xs
  in  (y:ys, b++bs, nn2)

liftVecF :: TypeMap -> Function -> Function
liftVecF tm f = f { body     = body'' ++ concat body' 
                  , tempVars = tempVars f ++ newTemps }
  where
    (body', newVars, _) = liftMany liftVecS tm 0 $ body f
    body'' = mapMaybe thr3 newVars
    newTemps = [(id,t) | (Var (V id []), t, _) <- newVars]
    


liftVecS tm nn (Loop id lo hi b) = 
  let (lo', z0, nn0) = liftVecE tm nn  lo
      (hi', z1, nn1) = liftVecE tm nn0 hi
      (b' , z2, nn2) = liftMany liftVecS tm nn1 b 
      -- we need to find which z's have to appear here (those that depend on id)
      -- and which can be lifted further
      (zHere,zUp)    = partition (dependsOn id) (z0++z1++z2)
      zHereInit      = mapMaybe thr3 zHere
      zHereNoInit    = [(v,t,Nothing) | (v,t,_) <- zHere]
  in  (zHereInit ++ [Loop id lo' hi' (concat b')], zHereNoInit ++ zUp, nn2)
liftVecS tm nn (If c t e) = 
  let (c', z0, nn0) = liftVecE tm nn c
      (t', z1, nn1) = liftMany liftVecS tm nn0 t
      (e', z2, nn2) = liftMany liftVecS tm nn1 e
  in  ([If c' (concat t') (concat e')], z0++z1++z2, nn2)
liftVecS tm nn (Assn v (Fun "vec" el)) = liftVecS tm nn (Call "vec" [] ((Var v):el))
liftVecS tm nn (Assn v (Fun "ID"  el)) = liftVecS tm nn (Call "ID"  [] ((Var v):el))
liftVecS tm nn (Assn v (Fun "IDR" el)) = liftVecS tm nn (Call "IDR" [] ((Var v):el))
liftVecS tm nn (Assn v e) =
  let (v', z0, nn0) = liftVecV tm nn  v
      (e', z1, nn1) = liftVecE tm nn0 e
  in  ([Assn v' e'], z0++z1, nn1)
liftVecS tm nn (Incr v e) =
  let (v', z0, nn0) = liftVecV tm nn  v
      (e', z1, nn1) = liftVecE tm nn0 e
  in  ([Incr v' e'], z0++z1, nn1)
-- todo: call sample and ldf; add dims
liftVecS tm nn (Call f r a) =
  let (a', z, nn0) = liftMany liftVecE tm nn a
  in  ([Call f r a'], z, nn0)
liftVecS tm nn (Comment s) = ([Comment s], [], nn)


liftVecE tm nn (Var v) = let (v',z,nn') = liftVecV tm nn v in (Var v', z, nn')
liftVecE tm nn (Con c) = (Con c, [], nn)
liftVecE tm nn f0@(Fun f el) 
  | null (indices $ inferCodeType tm f0) = (Fun f el', z, nn1)
  | f == "vec" = (var               , (var, inferCodeType tm f0, Just (Call "vec" [] (var:el'))) : z, nn1+1)
  | f == "ID"  = (Fun "ID"  (var:el), (var, inferCodeType tm f0, Just (Call "vec" [] (var:zeroI:drop 1 el'))) : z, nn1+1)
  | f == "IDR" = (Fun "IDR" (var:el), (var, inferCodeType tm f0, Just (Call "vec" [] (var:zeroR:drop 1 el'))) : z, nn1+1)

--  | f `elem` ["vec","ID","IDR"] = (var, (var, inferCodeType tm f0, Just (Call f [] (var:el'))) : z, nn1+1)
  where var = Var (V ("vec_var_" ++ show nn1) [])
        (el', z, nn1) = liftMany liftVecE tm nn el
        zeroI = Con (C.I 0)
        zeroR = Con (C.R 0)
liftVecE tm nn (Fun f [a,b])
  | f `elem` dotF++normF && null t0i = (Fun f [a',b'], aRest ++ bRest, nn2)
  | f `elem` dotF                    = (Fun fn (var:a':b':dmm), [(var, t0, Nothing)] ++ aRest ++ bRest, nn2+1)
  | f `elem` normF                   = (Fun fn (var:a':b':dmm), [(var, t0, Nothing)] ++ aRest ++ bRest, nn2+1)
  where t0@(Type t0t t0i) = inferCodeType tm b 
        var = Var (V ("vec_var_" ++ show nn2) [])
        (a', aRest, nn1) = liftVecE tm nn  a
        (b', bRest, nn2) = liftVecE tm nn1 b

        dotF  = [".+",".-",".*","./"]
        normF = [ "+", "-", "*", "/"]

        fn = (case last f of { '+' -> "add" ; '-' -> "sub" ; '*' -> "mult" ; '/' -> "div" }) ++ "_" ++
             (if head f == '.' then "const" else "vec") ++ "_" ++ (case t0t of { T0Int -> "i" ; _ -> "r" }) ++ "_" ++ 
             show (length t0i)

        (dmm,[]) = codifyMany (codifyExpr tm) $ concatMap rangeToExpr t0i
liftVecE tm nn (Fun f [a])
  | f `elem` ["exp","log"] && null t0i = (Fun f  [a'], aRest, nn)
  | f `elem` ["exp","log"]             = (Fun fn (var:a':dmm), [(var, t0, Nothing)] ++ aRest, nn+1)
  where t0@(Type t0t t0i) = inferCodeType tm a
        var = Var (V ("vec_var_" ++ show nn) [])
        (a', aRest, nn1) = liftVecE tm nn  a
        fn = f ++ "_vec_" ++ show (length t0i)
        (dmm,[]) = codifyMany (codifyExpr tm) $ concatMap rangeToExpr t0i

liftVecE tm nn (CaseOf cv cs) = (CaseOf cv' (zip csa csb), zb, nnb)
  where
    (cv', zv, nnv) = liftVecE tm nn cv
    ((za, nna), csa) = mapAccumL (\ (z,n) e -> let (e',z',n') = liftVecE tm n e in ((z++z',n'),e')) (zv,nnv) $ map fst cs
    ((zb, nnb), csb) = mapAccumL (\ (z,n) e -> let (e',z',n') = liftVecE tm n e in ((z++z',n'),e')) (za,nna) $ map snd cs

liftVecE tm nn f = error ("Code.liftVecE: cannot lift " ++ show f)

liftVecV tm nn (V id el) =
  let (el', z, nn0) = liftMany liftVecE tm nn el
  in  (V id el', z, nn0)


unliftVecLoops :: Function -> Function
unliftVecLoops f = f { body = uvl (map fst $ params f) [] $ body f}
  where
    -- note: all dvv loops will be top-level!
    uvl qual toadd [] = map snd toadd
    uvl qual toadd (b@(Loop id lo hi body):bs)
      | "dvv_loop_var_" `isPrefixOf` id && 
        mytrace ("unliftVecLoops::" ++ show (name f,b,getEVars lo ++ getEVars hi,qual,remainingVars)) True =
      if null remainingVars 
        then b : uvl qual toadd bs
        else     uvl qual ((remainingVars,b):toadd) bs
      where
        remainingVars = filter (not . (`elem` qual)) $ nub $ (getEVars lo ++ getEVars hi)
        getEVars e = [id | V id _ <- listify (const True) e]
    uvl qual toadd ((Loop id lo hi body):bs) = (Loop id lo hi (toadd_now ++ body')) : uvl qual {-toadd-} [] bs
      where 
        toadd0    = [(vl \\ [id], b) | (vl,b) <- toadd]
        toadd_now = map snd $ filter (null.fst) toadd0
        toadd'    = filter (not.null.fst) toadd0
        body'     = uvl (id:qual) toadd' body
    uvl qual toadd (b:bs) = b : uvl qual toadd bs

isDimRefVar ('#':z) = all isDigit z 
isDimRefVar _ = False

makeMaximize Nothing      str ret args = Call ("sample_" ++ str) ret args
makeMaximize (Just True ) str ret args = Call ("mode_"   ++ str) ret args
makeMaximize (Just False) str ret args = 
  If (Fun "sample_Bin" [Fun "sqrt" [Fun "/" [Con (C.R 1), Var (V "iter" [])]]])
     [makeMaximize Nothing     str ret args]
     [makeMaximize (Just True) str ret args]

