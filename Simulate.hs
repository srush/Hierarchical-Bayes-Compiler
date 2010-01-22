-----------------------------------------------------------------------------
-- |
-- Module      :  Simulate
-- Project     :  HBC
-- Copyright   :  (c) Hal Daume III
-- License     :  Open
-- 
-- Maintainer  :  Hal Daume III <me@hal3.name>
-- Stability   :  stable
-- Portability :  portable
--
-- Internally simulate sampler without generating code
--
-----------------------------------------------------------------------------

module Simulate where

import Code
import qualified Core as C
import Type
import qualified Data.Map as M
import Data.Maybe
import Data.List
import Debug.Trace 
import Control.Monad
import Control.Monad.State
import Data.Array.IO
import Util
import qualified Stats
import qualified Data.Array.Base as DAB
import Gen

data SimType = II Int
             | RR Double 
             | AA (IOArray Int SimType)
             | ARG String
             deriving Eq

type M a = StateT St IO a

data St = St { valueTable    :: M.Map String SimType  -- a stack
             , functionTable :: M.Map String ([Expr] -> M [SimType])
             , verbosity     :: Verbosity
             }

evalM verb a = evalStateT a (St M.empty simFTable verb)
runM  verb a = runStateT  a (St M.empty simFTable verb)

type DumpIt = (M.Map String SimType -> Double -> IO ())

simAll :: Int -> Function -> [Function] -> [Function] -> [(Id,SimType)] -> DumpIt -> [Function] -> [Function] -> M ()
simAll numSamples likF initF sampF defs dump einitF esampF = do
  let initF' = filter (not.isDefined) initF
  let sampF' = filter (not.isDefined) sampF

  let initF_sorted = let (a,b) = partition (("initialize_post_" `isPrefixOf`).name) initF' in b++a

  -- define functions
  printVerboseLn (>=Verbose) "Adding functions..."
  addFunctions initF'
  addFunctions sampF'
  addFunctions einitF
  addFunctions esampF

  -- define variables
  printVerboseLn (>=Verbose) "Defining passed-in variables..."
  mapM_ (\ (id,v) -> assignVariable (V id []) v) defs

  -- initialize everything else
  printVerboseLn (>=Verbose) "Running other initializations..."
  flip mapM_ (initF_sorted ++ einitF) $ \f -> do
    printVerboseLn (>=Trace) $ "  ... " ++ name f ++ " ..."
    [r] <- simF' f
    assignVariable (V (drop 11 $ name f) []) r

  -- begin sampling
  printVerboseLn (>=Verbose) "Beginning sampling..."
  printVerbose   (==Quiet)   "Sampling"
  for 1 numSamples $ \iter -> do
    assignVariable (V "iter" []) (II iter)
    flip mapM_ sampF' $ \f -> do
      when (not ("resample_post_" `isPrefixOf` name f)) $ do
        printVerboseLn (>=Trace) $ "  ... " ++ name f ++ " ..."
        [ret] <- simF' f
        assignVariable (V (drop 9 $ name f) []) ret

    printVerboseLn (>=Trace) "  Computing log likelihood..."
    [RR ll] <- simF' likF
    printVerbose   (==Quiet)   $ "."
    printVerboseLn (>=Verbose) $ "iter " ++ show iter ++ "\tll " ++ show ll
    
    when (not $ null esampF) $ do
      printVerboseLn (>=Trace) "  Sampling test variables..."
      mapM_ simF' esampF

    curVT <- valueTable `liftM` get
    lift $ dump curVT ll

    return ()

  printVerboseLn (==Quiet)   ""
  return ()
  where 
    simF' f = simF f =<< mapM (\ (id,_) -> getVariable (V id [])) (params f)
    isDefined f
      | "initialize_" `isPrefixOf` x = (drop 11 x) `elem` map fst defs
      | "resample_"   `isPrefixOf` x = (drop  9 x) `elem` map fst defs
      | otherwise                    = False
      where x = name f

addFunctions flist = 
  get >>= \st -> put (st { functionTable = foldr insertIt (functionTable st) flist })
  where
    insertIt f = M.insert (name f) (\el -> simF f =<< mapM evalE el)

simF f par
  | length (params f) /= length par = error ("Simulate.simF: incorrect number of parameters to " ++ name f)
  | otherwise = do
  -- if we're returning a variable that's passed in, just leave it and don't create extra storage
  let retVar = Nothing -- case returnVal f of { Just (Var (V id [])) -> Just id ; _ -> Nothing }

  -- get a fresh value table
  oldState <- getNewState retVar

  -- add the parameters to the state
  mapM_ (\ ((id,_),st) -> 
             when (Just id /= retVar) $
               assignVariable (V id []) st
        ) (zip (params f) par)

  -- execute the body
  mapM_ simS $ body f

  -- compute the return value
  ret <- mapM evalE (returnVal f)

  -- return to the old value table
  returnOldState retVar oldState

  -- and return  
  return ret

simS stmt = do
--  get >>= \st -> when ("eta" `M.member` valueTable st) $ do { v <- evalE (Var (V "eta" [])) ; showSimType v >>= \vs -> printVerboseLn SuperTrace $ "eta=" ++ vs "" }
  printVerbose (>=SuperTrace) ("  -> " ++ show stmt)
  simS0 stmt

simS0 stmt@(Loop var beg end body) = do
  begV <- evalE beg
  endV <- evalE end
  case (begV, endV) of
    (II b, II e) -> 
      mapM_ (\v -> assignVariable (V var []) (II v) >> mapM_ simS body) [b..e]
    _ -> error ("Simulate.simS: expecting loop bounds to evaluate to integers in " ++ show stmt)
simS0 stmt@(If cond th el) = do
  condV <- evalE cond
  mapM_ simS (case condV of
                II 0 -> el
                II _ -> th
                _    -> error ("Simulate.simS: expecting conditional to evaluate to integer in " ++ show stmt)
             )
simS0 stmt@(Assn v e) = evalE e >>= assignVariable v
simS0 stmt@(Incr v e) = fn_incr [Var v, e]
simS0 stmt@(Call f ret el) = do
  retV <- call f el
  mapM_ (\ (Var v,e) -> assignVariable v e) $ zip ret retV
simS0 (Comment _) = return ()

evalE (Var v) = getVariable v
evalE (Con (C.I i)) = return (II (fromInteger i))
evalE (Con (C.R r)) = return (RR r)
evalE (Fun i el) = head `liftM` call i el
evalE c@(CaseOf v caseOf) = evalE v >>= \val -> evalCases val caseOf
  where
    evalCases val [] = error $ "Simulate.evalE:  reached the end of a case statement without finding any matches!  The value evaluated to " ++ show v ++ " and the case statement was: " ++ show c
    evalCases val ((e,r):cs) = do
      eval <- evalE e
      if val == eval
        then evalE r
        else evalCases val cs
  
getVariable (V id el) = do
  st <- get
  v  <- case M.lookup id (valueTable st) of
          Just (z) -> return z
          _ -> case M.lookup ("post_"++id) (valueTable st) of
                 Just (z) -> return z
                 _          -> error ("Simulate.getVariable: lookup of variable " ++ id ++ " failed")
  ev <- mapM evalE el
  applyIndices v ev

assignVariable (V id []) val = 
--  lift (putStrLn ("assign "++id)) >>
  get >>= \st -> put (st { valueTable = M.insert id val (valueTable st) })
--  get >>= \st -> put (st { valueTable = M.insertWith (++) id [val] (valueTable st) })
assignVariable (V id el) val = do
--  lift $ putStrLn ("assign "++id)
  v   <- getVariable (V id [])
  elV <- mapM evalE el
  v'  <- applyIndices v (init elV)
  case (v',last elV) of
    (AA arr, II i) -> writeArray arr i val
    (AA _,_) -> error ("Simulate.assignVariable: expecting integer for array index")
    _ -> error ("Simulate.assignVariable: expecting array for assignment")

unassignVariable (V id _) = do
  st <- get
--  lift $ putStrLn ("unassign "++id)
  let t' = case M.lookup id (valueTable st) of
             Just (z)    -> M.delete id    (valueTable st)
--             Just (_:zs) -> M.insert id zs (valueTable st)
             _ -> error ("Simulate.unassignVariable: variable " ++ id ++ " not defined")
  put (st { valueTable = t' })

getNewState Nothing = do
  st <- get
  put (st { valueTable = M.empty })
  return (valueTable st)
getNewState (Just exc) = do
  st <- get
  put (st { valueTable = M.singleton exc (fromJust $ M.lookup exc (valueTable st)) })
  return (M.delete exc (valueTable st))

returnOldState Nothing vt = do
  st <- get
  put (st { valueTable = vt })
returnOldState (Just exc) vt = do
  st <- get
  let Just excVal = M.lookup exc (valueTable st)
  put (st { valueTable = M.insert exc excVal vt })

applyIndices v [] = return v
applyIndices (AA arr) ((II i):is) = do
  v' <- readArray arr i
  applyIndices v' is
applyIndices _ (i:_) = error ("Simulate.applyIndices: expected integral index; got: " ++ show i)

call f args = do
  ft <- functionTable `liftM` get
  case M.lookup f ft of
    Nothing -> error ("Simulate.call: cannot find function definition for " ++ f)
    Just ff -> ff args

-----------------------------------------------------------------------------

simFTable = M.fromList
  [ 
  -- vector creation functions
    ("vec", fn_vec)
  , ("ID",  fn_ID)
  , ("IDR", fn_IDR)
  -- sampling functions
  , ("sample_Dir"    , fn_sample_Dir)
  , ("sample_DirSym" , fn_sample_Dir)
  , ("sample_Mult"   , fn_sample_Mult)
  , ("sample_MultSym", fn_sample_MultSym)
  , ("sample_Exp"    , fn_sample_OneParam "Exp")
  , ("sample_Bin"    , fn_sample_OneParam "Bin")
  , ("sample_Poi"    , fn_sample_OneParam "Poi")
  , ("sample_Gam1"   , fn_sample_OneParam "Gam")
  , ("sample_Nor1"   , fn_sample_OneParam "Nor")
  , ("sample_Gam"    , fn_sample_TwoParam "Gam")
  , ("sample_Bet"    , fn_sample_TwoParam "Bet")
  , ("sample_Nor"    , fn_sample_TwoParam "Nor")
  , ("sample_NorMV"  , fn_sample_NorMV)
  , ("sample_Delta"  , fn_sample_Delta)
  -- maximizing functions
  , ("mode_Dir"    , fn_mode_Dir)
  , ("mode_DirSym" , fn_mode_Dir)
  , ("mode_Mult"   , fn_mode_Mult)
  , ("mode_MultSym", fn_mode_MultSym)
  , ("mode_Exp"    , fn_mode_OneParam "Exp")
  , ("mode_Bin"    , fn_mode_OneParam "Bin")
  , ("mode_Poi"    , fn_mode_OneParam "Poi")
  , ("mode_Gam1"   , fn_mode_OneParam "Gam")
  , ("mode_Nor1"   , fn_mode_OneParam "Nor")
  , ("mode_Gam"    , fn_mode_TwoParam "Gam")
  , ("mode_Bet"    , fn_mode_TwoParam "Bet")
  , ("mode_Nor"    , fn_mode_TwoParam "Nor")
  , ("mode_NorMV"  , fn_mode_NorMV)
  , ("mode_Delta"  , fn_mode_Delta)
  -- ldf functions
  , ("ldf_Dir"    , fn_ldf_Dir)
  , ("ldf_DirSym" , fn_ldf_Dir)
  , ("ldf_Mult"   , fn_ldf_Mult)
  , ("ldf_MultSym", fn_ldf_MultSym)
  , ("ldf_Exp"    , fn_ldf_OneParam "Exp")
  , ("ldf_Bin"    , fn_ldf_OneParam "Bin")
  , ("ldf_Poi"    , fn_ldf_OneParam "Poi")
  , ("ldf_Gam1"   , fn_ldf_OneParam "Gam")
  , ("ldf_Nor1"   , fn_ldf_OneParam "Nor")
  , ("ldf_Gam"    , fn_ldf_TwoParam "Gam")
  , ("ldf_Bet"    , fn_ldf_TwoParam "Bet")
  , ("ldf_Nor"    , fn_ldf_TwoParam "Nor")
  , ("ldf_NorMV"  , fn_ldf_NorMV)
  -- math functions
  , ( "+", fn_arith "+")
  , ( "-", fn_arith "-")
  , ( "*", fn_arith "*")
  , ( "/", fn_arith "/")
  , ( "^", fn_arith "^")
  , (".+", fn_arith "+")
  , (".-", fn_arith "-")
  , (".*", fn_arith "*")
  , ("./", fn_arith "/")
  , ("=" , fn_arith "=")
  , ("~=", fn_arith "~=")
  , ("<=", fn_arith "<=")
  , ("<" , fn_arith "<")
  , (">=", fn_arith ">=")
  , (">" , fn_arith ">")
  , ("||", fn_arith "||")
  , ("&&", fn_arith "&&")
  , ("log", fn_logexp "log")
  , ("exp", fn_logexp "exp")
  , ("sqrt",fn_logexp "sqrt")
  , ("all" , fn_unitval "all")
  , ("any" , fn_unitval "any")
  , ("sum" , fn_unitval "sum")
  , ("prod", fn_unitval "prod")
  , ("sqrDiff", fn_unitval "sqrDiff")
  , ("normalizeLog", fn_normalizeLog)
  ]


fn_vec (val : indices) = fn_vec' 1 indices >>= return . (:[])
  where
    fn_vec' idx [lo,hi] = do
      (II lo') <- evalE lo
      (II hi') <- evalE hi
      val'     <- evalE val
      arr      <- newArray (lo',hi'+1) val'
      writeArray arr (hi'+1) (case val' of { RR v -> RR (v * fromIntegral (hi'-lo'+1)) ; II v -> II (v * (hi'-lo'+1)) })
      return (AA arr)
    fn_vec' idx (lo:hi:rest) = do
      (II lo') <- evalE lo
      (II hi') <- evalE hi
      arr      <- newArray_ (lo',hi')
      let idxV = V ("#" ++ show idx) []
      flip mapM_ [lo'..hi'] $ \i -> do
        assignVariable idxV (II i)
        rarr <- fn_vec' (idx+1) rest
        writeArray arr i rarr
        unassignVariable idxV
      return (AA arr)

fn_ID [pos, lo, hi] = do
  II po <- evalE pos
  II lo <- evalE lo
  II hi <- evalE hi
  arr <- newArray (lo, hi+1) (II 0)
  writeArray arr po (II 1)
  writeArray arr (hi+1) (II 1)
  return [AA arr]

fn_IDR [pos, lo, hi] = do
  II po <- evalE pos
  II lo <- evalE lo
  II hi <- evalE hi
  arr <- newArray (lo, hi+1) (RR 0)
  writeArray arr po (RR 1)
  writeArray arr (hi+1) (RR 1)
  return [AA arr]


fn_incr [a0,b0] = do 
  bb <- evalE b0
  aa <- evalE a0
  showSimType aa >>= \v -> printVerboseLn (>=SuperTrace) ("    aa = " ++ v "")
  showSimType bb >>= \v -> printVerboseLn (>=SuperTrace) ("    bb = " ++ v "")
  fn_incr' (aa, bb)
  where 
    fn_incr' (AA a,AA b) = do
      b1@(lo,hi) <- getBounds a
      b2 <- getBounds b
      when (b1 /= b2) $ error ("Simulate.fn_incr: array increment bound mismatch")
      for lo hi $ \i -> do
        ai <- readArray a i
        bi <- readArray b i
        case (ai,bi) of
          (AA ai', _)  -> fn_incr' (ai,bi)
          (_, AA _  )  -> error ("Simulate.fn_incr: cannot increment constants by an array")
          (II i, II j) -> writeArray a i (II (i+j))
          _            -> writeArray a i (RR (toReal ai + toReal bi))

    fn_incr' (aa@(AA _),bb) = fn_incr'' aa bb
    fn_incr' (II i,II j) = assign_incr (II (i+j))
    fn_incr' (II i,RR j) = assign_incr (RR (fromIntegral i + j))
    fn_incr' (RR i,II j) = assign_incr (RR (i + fromIntegral j))
    fn_incr' (RR i,RR j) = assign_incr (RR (i+j))
    fn_incr' (II i,_   ) = error ("Simulate.fn_incr: cannot increment " ++ show i ++ " by an array")
    fn_incr' (RR i,_   ) = error ("Simulate.fn_incr: cannot increment " ++ show i ++ " by an array")

    assign_incr val =
      case a0 of
        (Var v) -> assignVariable v val
        _ -> error ("Simulate.fn_incr: cannot increment complex expressions")

    fn_incr'' (AA a) b = do
      (lo,hi) <- getBounds a
      for lo hi $ \i -> do
        v <- readArray a i
        case (v,b) of
          (II x, II y) -> writeArray a i (II (x+y))
          (II x, RR y) -> writeArray a i (RR (fromIntegral x + y))
          (RR x, II y) -> writeArray a i (RR (x + fromIntegral y))
          (RR x, RR y) -> writeArray a i (RR (x+y))
          (AA x, _   ) -> fn_incr'' (AA x) b


fixSums (II a) = return (II a)
fixSums (RR a) = return (RR a)
fixSums (AA a) = do
  (loA,hiA) <- getBounds a
  -- figure out if this is a "base" array
  a0 <- readArray a loA
  case a0 of
    AA _ -> for loA hiA $ \i -> do  -- it is not a base array
              a' <- readArray a i
              fixSums a'
    v0   -> do
              sum <- foldM (\s i -> readArray a i >>= return . (add s)) v0 [(loA+1)..(hiA-1)]
              writeArray a hiA sum
  return (AA a)
  where
    add (II a) (II b) = II (a+b)
    add (RR a) (RR b) = RR (a+b)
    add (II a) (RR b) = RR ((fromIntegral a) + b)
    add (RR a) (II b) = RR (a + (fromIntegral b))

fn_arith f [a,b] = do { aa <- evalE a ; bb <- evalE b ; fn_arith' aa bb >>= fixSums >>= return . (:[]) }
  where
    fn_arith' (II a) (II b) | f == "/" || f == "./" = return $ RR ((fromIntegral a) / (fromIntegral b))
    fn_arith' (RR a) (II b) | f == "/" || f == "./" = return $ RR (a / (fromIntegral b))
    fn_arith' (II a) (RR b) | f == "/" || f == "./" = return $ RR ((fromIntegral a) / b)
    fn_arith' (RR a) (RR b) | f == "/" || f == "./" = return $ RR (a / b)

    fn_arith' (II a) (II b) | f == "^" || f == ".^" = return $ RR ((fromIntegral a) ** (fromIntegral b))
    fn_arith' (RR a) (II b) | f == "^" || f == ".^" = return $ RR (a ** (fromIntegral b))
    fn_arith' (II a) (RR b) | f == "^" || f == ".^" = return $ RR ((fromIntegral a) ** b)
    fn_arith' (RR a) (RR b) | f == "^" || f == ".^" = return $ RR (a ** b)

    fn_arith' (II a) (II b) = return $ II (a `ff` b)
    fn_arith' (RR a) (RR b) = return $ RR (a `ff` b)
    fn_arith' (II a) (RR b) = return $ RR ((fromIntegral a) `ff` b)
    fn_arith' (RR a) (II b) = return $ RR (a `ff` (fromIntegral b))

    fn_arith' (AA a) (AA b) = do
      (loA,hiA) <- getBounds a
      (loB,hiB) <- getBounds b
      when ((loA /= loB) || (hiA /= hiB)) $
        error ("Simulate.fn_arith: array bound mismatch; got " ++ show (loA,hiA) ++ " and " ++ show (loB,hiB))
      arr' <- newArray_ (loA,hiA)
      for loA hiA $ \i -> do
        a' <- readArray a i
        b' <- readArray b i
        z  <- fn_arith' a' b'
        writeArray arr' i z
      return (AA arr')

    fn_arith' (AA a) b = do
      (lo,hi) <- getBounds a
      arr' <- newArray_ (lo,hi)
      for lo hi $ \i -> readArray a i >>= \a' -> fn_arith' a' b >>= writeArray arr' i
      return (AA arr')

    fn_arith' a (AA b) = do
      (lo,hi) <- getBounds b
      arr' <- newArray_ (lo,hi)
      for lo hi $ \i -> readArray b i >>= \b' -> fn_arith' a b' >>= writeArray arr' i
      return (AA arr')

    a `ff` b 
      | f == "+" || f == ".+" = a + b
      | f == "-" || f == ".-" = a - b
      | f == "*" || f == ".*" = a * b
      | f == "="  = boolToInt (a == b)
      | f == "~=" = boolToInt (a /= b)
      | f == "<=" = boolToInt (a <= b)
      | f == "<"  = boolToInt (a <  b)
      | f == ">=" = boolToInt (a >= b)
      | f == ">"  = boolToInt (a >  b)
      | f == "||" = boolToInt ((0/=a) || (0/=b))
      | f == "&&" = boolToInt ((0/=a) && (0/=b))
      | otherwise = error ("Simulate.fn_arith: unknown function " ++ f)

fn_logexp f [a] = do { aa <- evalE a ; fn_logexp' aa >>= fixSums >>= return . (:[]) }
  where
    fn_logexp' (II a) = return (RR $ ff $ fromIntegral a)
    fn_logexp' (RR a) = return (RR $ ff a)
    fn_logexp' (AA a) = do
      (lo,hi) <- getBounds a
      a' <- newArray_ (lo,hi)
      for lo hi $ \i -> writeArray a' i =<< fn_logexp' =<< readArray a i
      return (AA a')

    ff z | f == "log"  = log z
         | f == "exp"  = exp z
         | f == "sqrt" = sqrt z

fn_unitval f [a] = evalE a >>= foldValue fn zero >>= fixSums >>= return . (:[])
  where
    (fn,zero) =
      case f of
        "all"  -> (fn_and  , II 1)
        "any"  -> (fn_or   , II 0)
        "sum"  -> (fn_plus , II 0)
        "prod" -> (fn_times, II 1)
    fn_and a b = II $ boolToInt ((not $ isZero a) && (not $ isZero b))
    fn_or  a b = II $ boolToInt ((not $ isZero a) || (not $ isZero b))
    fn_plus (II i) (II j) = II (i+j)
    fn_plus (II i) (RR j) = RR (fromIntegral i + j)
    fn_plus (RR i) (II j) = RR (i + fromIntegral j)
    fn_plus (RR i) (RR j) = RR (i+j)
    fn_times (II i) (II j) = II (i*j)
    fn_times (II i) (RR j) = RR (fromIntegral i * j)
    fn_times (RR i) (II j) = RR (i * fromIntegral j)
    fn_times (RR i) (RR j) = RR (i*j)

fn_unitval "sqrDiff" [a,b] = evalE a >>= \a' -> evalE b >>= \b' -> foldValue2 sqrDiff 0 a' b' >>= \i -> return [RR i]
  where
    sqrDiff i j z0 = z0 + (i' - j') * (i' - j')
      where { i' = toReal i ; j' = toReal j }

fn_normalizeLog (val:_) = do
  (AA v)  <- evalE val
  (lo,hi) <- getBounds v
  r <- (map (\ (RR r) -> r) . init) `liftM` getElems v
  let s = Stats.addLogs r
  for lo (hi-1) $ \i ->
    writeArray v i . (\ (RR x) -> RR (exp(x-s))) =<< readArray v i
  writeArray v hi (RR 1)
  return []

fn_sample_NorMV (mu:si2:_) = do
  (AA muV ) <- evalE mu
  (RR si2V) <- evalE si2
  bnd <- getBounds muV
  el  <- map toReal `liftM` getElems muV
  xx  <- newListArray bnd . map RR . (++[0])  =<< lift (Stats.sample (Stats.NorMV el si2V))
  xx  <- fixSums (AA xx)

  showSimType (AA muV) >>= \vs -> showSimType xx >>= \xs -> 
    printVerboseLn (>=SuperTrace) $ "    sample_NorMV: " ++ vs "" ++ ", " ++ show si2V ++ " ==> " ++  xs ""

  return [xx]

fn_sample_Delta [val,dim] = do
  v <- evalE val
  d <- evalE dim
  showSimType v >>= \vs -> showSimType d >>= \ds -> 
    printVerboseLn (>=SuperTrace) $ "    sample_Delta: " ++ vs "" ++ ", " ++ ds ""
  ret <- case (v,d) of
    (II i,II j) -> return [II i]
    (RR i,II j) -> return [RR i]
    (AA a,_) -> do
      bn <- getBounds a
      el <- map toReal `liftM` getElems a
      newListArray bn (map RR el) >>= return . (:[]) . AA
    _ -> error ("Simulate.fn_sample_Delta: could not parse arguments correctly")
  return ret  

fn_sample_Dir [val,dim] = do
  v <- evalE val
  d <- evalE dim
  showSimType v >>= \vs -> showSimType d >>= \ds -> 
    printVerboseLn (>=SuperTrace) $ "    sample_Dir: " ++ vs "" ++ ", " ++ ds ""
  ret <- case (v,d) of
    (II i,II j) -> lift (Stats.sample (Stats.SymDir j (fromIntegral i))) >>= newListArray (1,j+1) . map RR . (++[1]) >>= return . (:[]) . AA
    (RR i,II j) -> lift (Stats.sample (Stats.SymDir j i)               ) >>= newListArray (1,j+1) . map RR . (++[1]) >>= return . (:[]) . AA
    (AA a,_) -> do
      bn <- getBounds a
      el <- (init . map toReal) `liftM` getElems a
      l  <- lift $ Stats.sample (Stats.Dir el)
      newListArray bn (map RR (l++[1])) >>= return . (:[]) . AA
    _ -> error ("Simulate.fn_sample_Dir: could not parse arguments correctly")
  return ret  

fn_sample_Mult (val:_) = do
  v <- evalE val
  case v of
    (AA a) -> do
      (lo,_) <- getBounds a
      el <- map toReal `liftM` getElems a
      i  <- lift $ Stats.sample (Stats.Mult (init el))
      return [II (i-1+lo)]
    _ -> error ("Simulate.fn_sample_Mult: could not parse arguments correctly")

fn_sample_MultSym [lo,hi] = do
  (II lov) <- evalE lo
  (II hiv) <- evalE hi
  i <- lift $ Stats.sample (Stats.SymMult (hiv-lov+1))
  return [II (i+lov-1)]

fn_sample_OneParam dist [val] = do
  v <- evalE val
  let p = case v of { RR r -> r ; II i -> fromIntegral i ; _ -> error "Simulate.fn_sample_OneParam: got array" }
  r <- case dist of
         "Exp" -> lift (Stats.sample $ Stats.Exp p)   >>= return . RR
         "Bin" -> lift (Stats.sample $ Stats.Bin p)   >>= return . II . boolToInt
         "Poi" -> lift (Stats.sample $ Stats.Poi p)   >>= return . II
         "Gam" -> lift (Stats.sample $ Stats.Gam p 1) >>= return . RR
         "Nor" -> lift (Stats.sample $ Stats.Nor p 1) >>= return . RR
         _     -> error ("Simulate.fn_sample_OneParam: unknown distribution " ++ dist )
  return [r]

fn_sample_TwoParam dist (val1:val2:_) = do
  v1 <- evalE val1
  v2 <- evalE val2
  let p1 = case v1 of { RR r -> r ; II i -> fromIntegral i ; _ -> error ("Simulate.fn_sample_TwoParam(" ++ dist ++ "): got array") }
  let p2 = case v2 of { RR r -> r ; II i -> fromIntegral i ; _ -> error ("Simulate.fn_sample_TwoParam(" ++ dist ++ "): got array") }  
  r <- case dist of
         "Gam" -> lift (Stats.sample $ Stats.Gam p1 p2)
         "Bet" -> lift (Stats.sample $ Stats.Bet p1 p2)
         "Nor" -> lift (Stats.sample $ Stats.Nor p1 p2)
         _     -> error ("Simulate.fn_sample_TwoParam: unknown distribution " ++ dist )
  printVerboseLn (>=SuperTrace) $ "    sample_" ++ dist ++ show (p1,p2) ++ " --> " ++ show r
  return [RR r]


fn_mode_NorMV (mu:si2:_) = do
  (AA muV ) <- evalE mu
  (RR si2V) <- evalE si2
  bnd <- getBounds muV
  xx  <- newListArray bnd =<< getElems muV 

  showSimType (AA muV) >>= \vs -> showSimType (AA xx) >>= \xs -> 
    printVerboseLn (>=SuperTrace) $ "    mode_NorMV: " ++ vs "" ++ ", " ++ show si2V ++ " ==> " ++  xs ""

  return [AA xx]

fn_mode_Delta [val,dim] = do
  v <- evalE val
  d <- evalE dim
  showSimType v >>= \vs -> showSimType d >>= \ds -> 
    printVerboseLn (>=SuperTrace) $ "    mode_Delta: " ++ vs "" ++ ", " ++ ds ""
  ret <- case (v,d) of
    (II i,II j) -> return [II i]
    (RR i,II j) -> return [RR i]
    (AA a,_) -> do
      bn <- getBounds a
      el <- map toReal `liftM` getElems a
      newListArray bn (map RR el) >>= return . (:[]) . AA
    _ -> error ("Simulate.fn_mode_Delta: could not parse arguments correctly")
  return ret  

fn_mode_Dir [val,dim] = do
  v <- evalE val
  d <- evalE dim
  showSimType v >>= \vs -> showSimType d >>= \ds -> 
    printVerboseLn (>=SuperTrace) $ "    mode_Dir: " ++ vs "" ++ ", " ++ ds ""
  ret <- case (v,d) of
    (II i,II j) -> lift (return $ Stats.mode (Stats.SymDir j (fromIntegral i))) >>= newListArray (1,j+1) . map RR . (++[1]) >>= return . (:[]) . AA
    (RR i,II j) -> lift (return $ Stats.mode (Stats.SymDir j i)               ) >>= newListArray (1,j+1) . map RR . (++[1]) >>= return . (:[]) . AA
    (AA a,_) -> do
      bn <- getBounds a
      el <- (map toReal . init) `liftM` getElems a
      l  <- return $ (Stats.mode (Stats.Dir el) ++ [1])
      newListArray bn (map RR l) >>= return . (:[]) . AA
    _ -> error ("Simulate.fn_mode_Dir: could not parse arguments correctly")
  return ret  

fn_mode_Mult (val:_) = do
  v <- evalE val
  case v of
    (AA a) -> do
      (lo,_) <- getBounds a
      el <- (map toReal . init) `liftM` getElems a
      i  <- return $ Stats.mode (Stats.Mult el)
      return [II (i-1+lo)]
    _ -> error ("Simulate.fn_mode_Mult: could not parse arguments correctly")

fn_mode_MultSym [lo,hi] = do
  (II lov) <- evalE lo
  (II hiv) <- evalE hi
  i <- return $ Stats.mode (Stats.SymMult (hiv-lov+1))
  return [II (i+lov-1)]

fn_mode_OneParam dist [val] = do
  v <- evalE val
  let p = case v of { RR r -> r ; II i -> fromIntegral i ; _ -> error "Simulate.fn_mode_OneParam: got array" }
  r <- case dist of
         "Exp" -> return (Stats.mode $ Stats.Exp p)   >>= return . RR
         "Bin" -> return (Stats.mode $ Stats.Bin p)   >>= return . II . boolToInt
         "Poi" -> return (Stats.mode $ Stats.Poi p)   >>= return . II
         "Gam" -> return (Stats.mode $ Stats.Gam p 1) >>= return . RR
         "Nor" -> return (Stats.mode $ Stats.Nor p 1) >>= return . RR
         _     -> error ("Simulate.fn_mode_OneParam: unknown distribution " ++ dist )
  return [r]

fn_mode_TwoParam dist (val1:val2:_) = do
  v1 <- evalE val1
  v2 <- evalE val2
  let p1 = case v1 of { RR r -> r ; II i -> fromIntegral i ; _ -> error ("Simulate.fn_mode_TwoParam(" ++ dist ++ "): got array") }
  let p2 = case v2 of { RR r -> r ; II i -> fromIntegral i ; _ -> error ("Simulate.fn_mode_TwoParam(" ++ dist ++ "): got array") }  
  r <- case dist of
         "Gam" -> return (Stats.mode $ Stats.Gam p1 p2)   >>= return . RR
         "Bet" -> return (Stats.mode $ Stats.Bet p1 p2)   >>= return . RR
         "Nor" -> return (Stats.mode $ Stats.Nor p1 p2)   >>= return . RR
         _     -> error ("Simulate.fn_mode_TwoParam: unknown distribution " ++ dist )
  return [r]


fn_ldf_NorMV (_:xx:mu:si2:_) = do
  (AA xxV ) <- evalE xx
  (AA muV ) <- evalE mu
  si2V <- toReal `liftM` evalE si2
  showSimType (AA xxV) >>= \vs -> showSimType (AA muV) >>= \us -> 
    printVerboseLn (>=SuperTrace) $ "    ldf_NorMV: " ++ vs "" ++ " | " ++ us "" ++ ", " ++ show si2V
  x   <- map toReal `liftM` getElems xxV
  el  <- map toReal `liftM` getElems muV
  return [RR $ Stats.ldf (Stats.NorMV (init el) si2V) (init x)]


fn_ldf_Dir [_,xx,val,dim] = do
  AA xa <- evalE xx
  x <- map (\ (RR i) -> i) `liftM` getElems xa
  v <- evalE val
  d <- evalE dim
  showSimType v >>= \vs -> showSimType d >>= \ds -> 
    printVerboseLn (>=SuperTrace) $ "    ldf_Dir: " ++ show xx ++ "=" ++ show x ++ " | " ++ show val ++ "=" ++ vs "" ++ ", " ++ show dim ++ "=" ++ ds ""
  case (v,d) of
    (II i,II j) -> return [RR $ Stats.ldf (Stats.SymDir j (fromIntegral i)) (init x)]
    (RR i,II j) -> return [RR $ Stats.ldf (Stats.SymDir j i)                (init x)]
    (AA a,_) -> do
      bn <- getBounds a
      el <- map toReal `liftM` getElems a
      return [RR $ Stats.ldf (Stats.Dir (init el)) (init x)]
    _ -> error ("Simulate.fn_ldf_Dir: could not parse arguments correctly")

fn_ldf_Mult (_:xx:val:_) = do
  (II x) <- evalE xx
  v <- evalE val
  case v of
    (AA a) -> do
      (lo,_) <- getBounds a
      el <- map toReal `liftM` getElems a
      return [RR $ Stats.ldf (Stats.Mult (init el)) x]
    _ -> error ("Simulate.fn_ldf_Mult: could not parse arguments correctly")

fn_ldf_MultSym [_,x,lo,hi] = do
  (II x)   <- evalE x
  (II lov) <- evalE lo
  (II hiv) <- evalE hi
  return [RR $ Stats.ldf (Stats.SymMult (hiv-lov+1)) x]

fn_ldf_OneParam dist [_,xx,val] = do
  x <- evalE xx
  v <- evalE val
  let p = case v of { RR r -> r ; II i -> fromIntegral i ; _ -> error "Simulate.fn_ldf_OneParam: got array" }
  let r=case dist of
         "Exp" -> Stats.ldf (Stats.Exp p)   (toReal x)
         "Bin" -> Stats.ldf (Stats.Bin p)   (toBool x)
         "Poi" -> Stats.ldf (Stats.Poi p)   (case v of { II i -> i ; _ -> error "Simulate.fn_ldf_OneParam(Poi): got real" })
         "Gam" -> Stats.ldf (Stats.Gam p 1) (toReal x)
         "Nor" -> Stats.ldf (Stats.Nor p 1) (toReal x)
         _     -> error ("Simulate.fn_ldf_OneParam: unknown distribution " ++ dist )
  return [RR r]

fn_ldf_TwoParam dist [_,xx,val1,val2] = do
  (RR x) <- evalE xx
  v1 <- evalE val1
  v2 <- evalE val2
  let p1 = case v1 of { RR r -> r ; II i -> fromIntegral i ; _ -> error "Simulate.fn_ldf_TwoParam: got array" }
  let p2 = case v2 of { RR r -> r ; II i -> fromIntegral i ; _ -> error "Simulate.fn_ldf_TwoParam: got array" }  
  let r=case dist of
         "Gam" -> Stats.ldf (Stats.Gam p1 p2) x
         "Bet" -> Stats.ldf (Stats.Bet p1 p2) x
         "Nor" -> Stats.ldf (Stats.Nor p1 p2) x
         _     -> error ("Simulate.fn_ldf_TwoParam: unknown distribution " ++ dist )
  return [RR r]

duplicate (II i) = return (II i)
duplicate (RR r) = return (RR r)
duplicate (AA arr) = do
  (lo,hi) <- getBounds arr
  arr'    <- newArray_ (lo,hi)
  flip mapM_ [lo..hi] $ \i ->
    writeArray arr' i =<< duplicate =<< readArray arr i
  return (AA arr')

foldValue f z0 (II i) = return $ f (II i) z0
foldValue f z0 (RR i) = return $ f (RR i) z0
foldValue f z0 (AA a) = do
  (lo,hi) <- getBounds a
  a0 <- readArray a lo
  let hi' = case a0 of { AA _ -> hi ; _ -> hi-1 }
  foldM (\z i -> readArray a i >>= foldValue f z) z0 [lo..hi']

foldValue2 f z0 x y
  | isScalar x && isScalar y = return $ f x y z0
  | otherwise = do
  let AA a = x
  let AA b = y
  (lo1,hi1) <- getBounds a
  (lo2,hi2) <- getBounds b
  when ((lo1 /= lo2) || (hi1 /= hi2)) $ do
    error ("Simulate.foldValue2: mismatched bounds: " ++ show (lo1,hi1) ++ " and " ++ show (lo2,hi2))
  a0 <- readArray a lo1
  let hi' = case a0 of { AA _ -> hi1 ; _ -> hi1-1 }
  foldM (\z i -> do
           ai <- readArray a i
           bi <- readArray b i
           foldValue2 f z ai bi
        ) z0 [lo1..hi']

isScalar (AA _) = False
isScalar _ = True

toReal (RR r) = r
toReal (II i) = fromIntegral i
toReal (AA a) = error ("Simulate.toReal: trying to convert array into real")

isZero (II 0) = True
isZero (RR r) | r == 0 = True
isZero _ = False

toBool = not . isZero

instance MArray a e m => MArray a e (StateT s m) where
  getBounds = lift . getBounds
  newArray i = lift . newArray i
  newArray_ = lift . newArray_
  unsafeRead i = lift . DAB.unsafeRead i
  unsafeWrite i a = lift . DAB.unsafeWrite i a

showSimType (RR i) = return (shows i)
showSimType (II i) = return (shows i)
showSimType (AA a) = 
  getElems a >>= mapM showSimType >>= \ (l) -> return (showChar '[' . commaSep l . showChar ']')

instance Ord SimType where
  (AA _) `compare` _ = error "Simulate.compare(SimType): got array"
  _ `compare` (AA _) = error "Simulate.compare(SimType): got array"
  (ARG _) `compare` _ = error "Simulate.compare(SimType): got ARG"
  _ `compare` (ARG _) = error "Simulate.compare(SimType): got ARG"
  i `compare` j = toReal i `compare` toReal j


printVerboseLn v str = get >>= \s -> when (v $ verbosity s) $ lift (putStrLn str)
printVerbose   v str = get >>= \s -> when (v $ verbosity s) $ lift (putStr   str)

instance Show SimType where
  showsPrec _ (II i) = shows i
  showsPrec _ (RR i) = shows i
  showsPrec _ (AA _) = showString "AA"
  showsPrec _ (ARG i) = showString "ARG-" . shows i
