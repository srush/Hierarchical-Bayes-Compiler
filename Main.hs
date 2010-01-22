-----------------------------------------------------------------------------
-- |
-- Module      :  Main
-- Project     :  HBC
-- Copyright   :  (c) Hal Daume III
-- License     :  Open
-- 
-- Maintainer  :  Hal Daume III <me@hal3.name>
-- Stability   :  stable
-- Portability :  portable
--
-- Executable
--
-----------------------------------------------------------------------------

module Main where

import System
import System.IO
import Data.Char
import Data.List
import Data.Maybe
import Control.Monad
import Data.IORef
import qualified Data.Map as M
import Control.Exception

import Import
import Code
import Simulate
import Decl hiding (decls)
import Parse
import Data
import Core
import MkCore
import qualified Conjugacy
import qualified UnLift
import qualified Math
import Marginalize
import Type
import Data
import Control.Monad
import Control.Monad.State
import Util
import qualified CodeOpt

import qualified GenC(spec)

data DumpSpec = DumpLast | DumpBest | DumpNth Int

data SimArgs = Define    String SimType
             | Collapse  String
             | Maximize  String Bool  -- True means maximize, False means anneal
             | LoadD     FilePath String String [String] [Char]
             | LoadM     Bool FilePath String String String -- True means real valued
             | File      FilePath
             | Verbosity Verbosity
             | Iter      Int
             | Dump      DumpSpec [String]
             | Eval      [String]
             | DumpCore
             | Make

programName = "hbc"

outputTypes = [GenC.spec]


usage msg = do
  mapM_ (hPutStrLn stderr) $
    ["usage: " ++ programName ++ " simulate [options] <HIER FILE>"
    ,"   or: " ++ programName ++ " compile  [options] <HIER FILE> <OUTPUT FILE>"
    ,""
    ,"where:"
    ,""
    ,"  <HIER FILE> is either the name of a file containing a hierarchical"
    ,"  model, or '-' for stdin and (for compilation) <OUTPUT FILE> is the"
    ,"  name of the desired output file for the compiled code (the extension"
    ,"  of the output file is used to determine the language)."
    ,""
    ,"options are of the form:"
    ,"  --define <VAR> <VALUE>       to define a variable (which therefore won't"
    ,"                                 be sampled)"
    ,"  --collapse <VAR>             collapse (marginalize out/rao-blackwellize)"
    ,"                                 the given variable"
    ,"  --maximize <VAR>             maximize with respect to <VAR>, don't sample"
    ,"  --loadD <FILE> <VAR>* ';'    to load discrete data from <FILE>; it is"
    ,"                                 assumed to be in numeric form; the <VAR>"
    ,"                                 args should be: (1) the variable to store"
    ,"                                 the results in; (2) the variable to store"
    ,"                                 the highest read value in; (3..N) the"
    ,"                                 variables to store the dimensions (see"
    ,"                                 the user guide for details/examples)"
    ,"  --loadM <FILE> <V> <V> <V>   to load continuous data from <FILE>; the"
    ,"                                 first <VAR> is the matrix, the second"
    ,"                                 is the first dimension (number of lines),"
    ,"                                 the third is the second dimension (number"
    ,"                                 of values per line)"
    ,"  --loadMI <FILE> <V> <V> <V>  like loadM, but load integer values"
    ,"  --dump <SPEC> <VAR>* ';'     dump variables in list according to <SPEC>:"
    ,"                                 last -- dump after the final iteration"
    ,"                                 best -- dump the sample with highest ll"
    ,"                                 #    -- dump every # samples"
    ,"                                 all  -- dump all samples (equiv to '1')"
    ,"  --eval <VAR>* ';'            sample variables for evaluation every time"
    ,"                                 a dump is executed"
    ,"  --[verbosity]                where [verbosity] is one of:"
    ,"                                 silent, quiet, verbose, trace, supertrace"
    ,"  --iter <NUM>                 where [NUM] is how many iterations to run"
    ,"  --dumpcore                   dump internal representations during startup"
    ,""
    ,"for compilation you can also say:"
    ,"  --make                       build executable output (only for .c)"
    ,""
    ,"currently supported output formats are: " ++ unwords (map fst4 outputTypes)
    ]
  
  when (not $ null msg) $ hPutStrLn stderr $ "\n" ++ msg
  exitWith (ExitFailure 1)



readValue x = 
  case parseArg x of
    Just  i -> ARG i
    Nothing -> case readsPrec 0 x of
                 [(v,"")] -> II v
                 _ -> case readsPrec 0 x of
                        [(v,"")] -> RR v
                        _ -> error ("cannot parse value: " ++ x)

parseArgs ("--silent":xs) = Verbosity Silent : parseArgs xs
parseArgs ("--quiet":xs) = Verbosity Quiet : parseArgs xs
parseArgs ("--verbose":xs) = Verbosity Verbose : parseArgs xs
parseArgs ("--trace":xs) = Verbosity Trace : parseArgs xs
parseArgs ("--supertrace":xs) = Verbosity SuperTrace : parseArgs xs
parseArgs ("--iter":x:xs) = (Iter (read x)) : parseArgs xs
parseArgs ("--dumpcore":xs) = DumpCore : parseArgs xs
parseArgs ("--define":var:val:xs) = (Define var (readValue val)) : parseArgs xs
parseArgs ("--collapse":var:xs) = (Collapse var) : parseArgs xs
parseArgs ("--maximize":var:xs) = (Maximize var True) : parseArgs xs
parseArgs ("--anneal":var:xs) = (Maximize var False) : parseArgs xs
parseArgs ("--eval":rest) = (Eval vars) : parseArgs rest'
  where
    vars  = takeWhile (/=";") rest
    rest' = drop (length vars+1) rest
parseArgs ("--loadD":fn:var:high:rest) = 
  let dims = takeWhile (/=";") rest
      num  = length dims
      xs   = drop num rest
      seps = case num of
               0 -> ""
               1 -> ""
               2 -> "\n"
               3 -> "\n\t"
               4 -> "\n\t#"
               _ -> error ("cannot read data with more than 4 dimensions")
  in  (LoadD fn var high dims seps) : parseArgs (drop 1 xs)
parseArgs ("--loadM" :fn:var:n:d:xs) = (LoadM True  fn var n d) : parseArgs xs
parseArgs ("--loadMI":fn:var:n:d:xs) = (LoadM False fn var n d) : parseArgs xs
parseArgs ("--dump":spec:rest) =
  let vars = takeWhile (/=";") rest
      xs   = drop (length vars+1) rest
      sp   = case spec of
               "last" -> DumpLast
               "best" -> DumpBest
               "all"  -> DumpNth 1
               n      -> (read n::Int) `seq` DumpNth (read n)
  in  (Dump sp vars) : parseArgs xs
parseArgs ("--make":rest) = Make : parseArgs rest
parseArgs z = map File z

makeSampWarnings f = 
  when (all (\x -> case x of { Comment _ -> True ; _ -> False }) (body f)) $ do
    hPutStrLn stderr $ "Warning: no generated function body for " ++ name f
    mapM_ (\ (Comment s) -> hPutStrLn stderr $ "  " ++ s) (body f)
    hPutStrLn stderr ""

dumpInternal str z = do
  putStr $ "\n\n************************************* " ++ str ++ " *************************************\n\n"
  --putStrLn $ show z
  mapM_ print z
  putStrLn ""

partitionModule evals (MOD decls) = (MOD a, MOD b)
  where
    (a,b) = partition (not . (`elem` evals) . declLHS) decls
    declLHS (DECL  (LHS v _) _ _) = v
    declLHS (TDECL (LHS v _) _ _) = v

buildCore' str dump mod = do
  let mkcore = mkCore mod
  when dump $ dumpInternal (str++ "mkcore") [mkcore]

  let (core,defType0) = filterTypeDefinitions mkcore
  when dump $ dumpInternal (str++ "core") [core]
  when dump $ dumpInternal (str++ "defType0") defType0

  let core' = nameSPVars $ UnLift.simplify core
  when dump $ dumpInternal (str++ "core'") [core']
  when dump $ dumpInternal (str++ "core'typ") (M.toList $ getTypeMap defType0 core')

  let core''= inferMissingRanges (getTypeMap defType0 core') core'
  when dump $ dumpInternal (str++ "core''") [core'']
  when dump $ dumpInternal (str++ "core''typ") (M.toList $ getTypeMap defType0 core'')

  return (core, core'', defType0)

buildCore dump coll maxm mod0 evals = do
  hPutStrLn stderr $ "Building core module"
  when dump $ dumpInternal "mod0" [mod0]

  mod1 <- importAll mod0
  when dump $ dumpInternal "mod1" [mod1]

  let (mod,eval_mod) = partitionModule evals mod1
  when dump $ dumpInternal "mod" [mod]
  when dump $ dumpInternal "eval_mod" [eval_mod]

  (core, core'', defType0) <- buildCore' "" dump mod
  (eval_core, eval_core'', eval_defType0) <- buildCore' "eval_" dump eval_mod

  let prior = Math.simplify $ coreToPrior core''
  when dump $ dumpInternal "prior" [prior]

  when dump $ dumpInternal "coll" coll

  let lik   = removeSubF $ makeLikFunction prior (getGlobals core'') (getTypeMap defType0 core'') coll
  when dump $ dumpInternal "lik" [lik]

  let tm0   = getTypeMap defType0 prior -- core''  -- TODO: check this; was prior
  when dump $ dumpInternal "tm0" (M.toList tm0)

  let init  = removeSub $ [makeInitializeFunction prior d tm0 | d <- decls prior]
  when dump $ dumpInternal "init" [init]

  let dmp   = removeSub $ [makeDumpFunction       prior d tm0 | d <- decls prior]
  when dump $ dumpInternal "dmp"  dmp


  let eval_prior = Math.simplify $ coreToPrior eval_core''
  when dump $ dumpInternal "eval_prior" [eval_prior]
  let eval_tm0   = getTypeMap defType0 eval_prior
  when dump $ dumpInternal "eval_tm0" (M.toList eval_tm0)
  let eval_init  = removeSub $ [makeInitializeFunction eval_prior d eval_tm0 | d <- decls eval_prior]
  when dump $ dumpInternal "eval_init" [eval_init]
  let eval_samp  = removeSub $ [makeSampleFunction     d eval_tm0 [] Nothing | d <- decls eval_prior]
  when dump $ dumpInternal "eval_samp"  eval_samp
  let eval_dmp   = removeSub $ [makeDumpFunction       eval_prior d eval_tm0 | d <- decls eval_prior]
  when dump $ dumpInternal "eval_dmp"  eval_dmp


  let conj0 = nameSPVars $ Conjugacy.simplify core
  when dump $ dumpInternal "conj0" [conj0]

  let conj  = simplifyAllCore Nothing conj0
  when dump $ dumpInternal "conj" [conj]

  let typ   = getTypeMap defType0 conj0
  when dump $ dumpInternal "typ"  (M.toList typ)

  let (typ', marg, margIds, upd, warn) = marginalizeAll conj0 typ coll
  mapM_ (\s -> hPutStrLn stderr ("Warning: " ++ s)) warn

  when dump $ dumpInternal "marg" [marg]
  when dump $ dumpInternal "typ'" [typ']
  when dump $ dumpInternal "upd"  upd

  let marg' = simplifyAllCore (Just (M.keys typ')) marg
  when dump $ dumpInternal "marg'" [marg']

  let upd'  = [ u { variableRem = \sl -> simplifyAllCoreUpdate (Just $ M.keys typ') (variableRem u $ sl)
                  , variableAdd = \sl -> simplifyAllCoreUpdate (Just $ M.keys typ') (variableAdd u $ sl) }
              | u <- upd ]

  when dump $ dumpInternal "upd'"  upd'

  let typ'' = getTypeMap defType0 marg'
  when dump $ dumpInternal "typ''" [typ'']

  let samp  = [f | d@(Core.V var _,_,_)  <- decls $ unliftCore marg'
                 , let f = makeSampleFunction d typ'' upd' (var `lookup` maxm)
                 , not (("post_" ++ drop 9 (name f)) `elem` margIds)
                 ]
  when dump $ dumpInternal "samp" samp
  mapM_ makeSampWarnings samp

  let samp' = CodeOpt.opt $ removeSub $ removeID typ'' samp
  when dump $ dumpInternal "samp'" samp'

  let init' = map (makeMarginalInitialization typ'' samp') margIds ++
              [f | f <- init
                 , not (("post_" ++ drop 11 (name f)) `elem` margIds)]
  when dump $ dumpInternal "init'" init'

  return (typ'', lik, init', dmp, samp', eval_tm0, eval_init, eval_samp, eval_dmp)

getVars vt vars = M.filterWithKey (\k _ -> k `elem` vars) vt

printDump ll t = do
  putStrLn $ "== SAMPLE\t" ++ show ll
  flip mapM_ (M.assocs t) $ \ (var, val) ->
    showSimType val >>= \showVal ->
    putStrLn $ "== " ++ var ++ "\t" ++ showVal ""

makeDump _  (Dump _ []) _ _ = return ()
makeDump di (Dump (DumpNth n) vars) st ll = do
  (cnt,d) <- readIORef di
  writeIORef di (cnt+1,d)
  when ((cnt `mod` n) == (n-1)) $ printDump ll (getVars st vars)
makeDump di (Dump DumpLast vars) st ll = do
  (cnt,_) <- readIORef di
  writeIORef di (cnt, Just (ll, getVars st vars))
makeDump di (Dump DumpBest vars) st ll = do
  (cnt,d) <- readIORef di
  case d of
    Just (ll0,_) | ll0 > ll -> return ()
    _                       -> writeIORef di (cnt, Just (ll, getVars st vars))

simulate :: [SimArgs] -> IO ()
simulate [] = usage ""
simulate args = do
  fn  <- case last args of { File fn -> return fn ; _ -> usage "missing hierarchical filename" }
  hPutStrLn stderr $ "Loading module " ++ fn
  (mod,direct) <- loadHier fn
  simulate' ((parseArgs (direct ++ [""])) ++ init args) mod

simulate' args mod = do
  lD  <- flip mapM loadD $ \ (LoadD fn var high dims seps) -> do
           (varV, highV, dimsV) <- loadDiscrete seps fn
           return ((var,varV) : (high,highV) : zip dims dimsV)

  lM  <- flip mapM loadM $ \ (LoadM isReal fn var n d) -> do
           (varV, nV, dV) <- if isReal then loadMatrix fn else loadMatrixInt fn
           return [(var,varV), (n,nV), (d,dV)]

  let decls = vals ++ concat lD ++ concat lM

  (_, likF, initF, _, sampF, _, einitF, esampF, edumpF) <- buildCore dumpc coll maxm mod evals
  
  dumpInfo <- newIORef (0, Nothing)
  runM verb $ simAll numi likF initF sampF decls (makeDump dumpInfo dump) einitF esampF -- (makeDump dumpInfo edumpF)

  case dump of 
    Dump _ [] -> return ()
    Dump (DumpNth _) _ -> return ()
    _ -> do
      (_,d) <- readIORef dumpInfo
      case d of
        Nothing -> return ()
        Just (ll,v) -> printDump ll v
  return ()
  where
    verb  = last (Verbose : mapMaybe (\x -> case x of { Verbosity v -> Just v ; _ -> Nothing }) args)
    vals  = mapMaybe (\x -> case x of { Define var val -> Just (var,val) ; _ -> Nothing }) args
    loadD = mapMaybe (\x -> case x of { f@(LoadD {}) -> Just f ; _ -> Nothing }) args
    loadM = mapMaybe (\x -> case x of { f@(LoadM {}) -> Just f ; _ -> Nothing }) args
    numi  = last (100 : mapMaybe (\x -> case x of { Iter v -> Just v ; _ -> Nothing }) args)
    dump  = last ((Dump DumpLast []) : mapMaybe (\x -> case x of { d@(Dump {}) -> Just d ; _ -> Nothing }) args)
    dumpc = not $ null $ filter (\x -> case x of { DumpCore -> True ; _ -> False }) args
    coll  = mapMaybe (\x -> case x of { Collapse var -> Just var ; _ -> Nothing }) args
    maxm  = mapMaybe (\x -> case x of { Maximize var b -> Just (var,b) ; _ -> Nothing }) args
    evals = concatMap (\x -> case x of { Eval l -> l ; _ -> [] }) args

compile rawArgs args = 
  case find ((`isSuffixOf` fout) . fst4) outputTypes of
    Nothing -> usage "unknown output file type"
    Just (suff, run, reqFiles, reqPath) -> do
      hPutStrLn stderr $ "Loading module " ++ fin
      src <- readFile fin
      (mod, direct) <- loadHier fin
      includeDir <- getRequiredPaths reqPath
      qualFiles  <- mapM getQualifiedPath reqFiles
      compile' (src,rawArgs) includeDir qualFiles ((parseArgs (direct ++ ["",""])) ++ args) suff run mod
  where
    [File fin, File fout] = drop (length args - 2) args

compile' src includeDir qualFiles args suff run mod = do
--  case dump of { Dump DumpBest _ -> error "cannot compile with --dump best; use a different dumping strategy" ; _ -> return () }
  (typ, likF, initF, dumpF, sampF, etyp, einitF, esampF, edumpF) <- buildCore dumpc coll maxm mod evals
  let defaults = (vals, loadD, loadM, numi)
  
  let cmd = "gcc -O3 -lm " ++ unwords qualFiles ++ " " ++ (if null includeDir || includeDir == "." then "" else ("-I" ++ includeDir ++ " ")) ++ fout ++ " -o " ++ (init fout ++ "out")
  hPutStrLn stderr $ "Generating " ++ fout
  run src cmd defaults dumpc dump' fout typ likF initF dumpF sampF etyp einitF esampF edumpF
  when (make && suff==".c") $ do
    hPutStrLn stderr $ "Running: "++ cmd
    system cmd
    return ()
  where
    [File fin, File fout] = drop (length args - 2) args

    vals  = mapMaybe (\x -> case x of { Define var val -> Just (var,val) ; _ -> Nothing }) args
    loadD = mapMaybe (\x -> case x of { f@(LoadD fn var high dims seps) -> Just (var,(fn,high,dims,seps)) ; _ -> Nothing }) args
    loadM = mapMaybe (\x -> case x of { f@(LoadM isReal fn var n d) -> Just (var,(isReal,fn,n,d)) ; _ -> Nothing }) args
    numi  = last (100 : mapMaybe (\x -> case x of { Iter v -> Just v ; _ -> Nothing }) args)
    dumpc = not $ null $ filter (\x -> case x of { DumpCore -> True ; _ -> False }) args
    make  = not $ null $ filter (\x -> case x of { Make     -> True ; _ -> False }) args
    coll  = mapMaybe (\x -> case x of { Collapse var -> Just var ; _ -> Nothing }) args
    maxm  = mapMaybe (\x -> case x of { Maximize var b -> Just (var,b) ; _ -> Nothing }) args
    dump  = last ((Dump DumpLast []) : mapMaybe (\x -> case x of { d@(Dump {}) -> Just d ; _ -> Nothing }) args)
    dump' = case dump of
              Dump DumpLast    vars -> (-1, vars)
              Dump DumpBest    vars -> (-2, vars)
              Dump (DumpNth i) vars -> (fromIntegral i, vars)
    evals = concatMap (\x -> case x of { Eval l -> l ; _ -> [] }) args

runMain ("simulate":xs) = simulate    (parseArgs xs)
runMain ("compile" :xs) = compile  xs (parseArgs xs)
runMain _ = usage ""

main = hPutStrLn stderr hbcString >> getArgs >>= runMain

regressionTest = do
  exc <- newIORef []

  runMain' exc "--dump last z mu pi ; --loadM X x N dim --define K 2 mix_gauss.hier"
  runMain' exc "--dump last z ; --loadD testW w V D N ; --define K 2 LDA.hier"
  runMain' exc "--dump last z ; --loadD testW w V N   ; --define K 2 HMM.hier"
  runMain' exc "--dump last z ; --loadD testW w V D N ; --define K 2 LDA-HMM.hier"
  runMain' exc "chang.hier"
  runMain' exc "Hall.hier"
  runMain' exc "Hall2.hier"
  runMain' exc "schools.hier"
  runMain' exc "underlying.hier"
  runMain' exc "Chang.hier"
--  runMain' exc "SciRef.hier"
--  runMain' exc "LDA3.hier"
--  runMain' exc "LDA4.hier"

  putStrLn "\n\n\n\n\nDone!"
  e <- readIORef exc
  flip mapM_ (reverse e) (\ (cmd,err) -> putStrLn $ "Exception " ++ show err ++ " raise on " ++ cmd)

  where
    runMain' exc str0 = do
      let str = "simulate --iter 10 " ++ str0
      putStrLn ("Running: " ++ str)
      res <- try (runMain $ words str)
      res <- try $ return ()
      case res of
        Left err -> putStrLn ("Exception: " ++ show err) >> pushExc exc str err
        Right _  -> return ()
      putStrLn ""
      putStrLn ""

      let hier = reverse $ drop 5 $ reverse $ last $ words str0
      let str = "compile --iter 10 --make " ++ str0 ++ " " ++ hier ++ ".c"
      putStrLn ("Running: " ++ str)
      res <- try (runMain $ words str)
      case res of
        Left err -> putStrLn ("Exception: " ++ show err) >> pushExc exc str err
        Right _  -> do putStrLn ("\nRunning:")
                       system (hier ++ ".out")
                       system ("gprof " ++ hier ++ ".out > " ++ hier ++ ".prof")
                       return ()
      putStrLn ""
      putStrLn ""

    pushExc exc str err = readIORef exc >>= writeIORef exc . ((str,err):)


