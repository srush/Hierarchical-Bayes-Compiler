module Util where

import Data.List
import Control.Monad
import Debug.Trace

import Data.Generics
import Data.Typeable
import System.IO
--import System.FilePath
import Control.Exception
import System.Environment
--import System.Posix(isSymbolicLink,readSymbolicLink,getSymbolicLinkStatus)


hbcVersion :: (Int,Int)
hbcVersion = (0,7)

traceOn = False
mytrace str z | traceOn   = trace str z
              | otherwise = z

str `issueWarning` z = trace ("Warning: " ++ str) z

data Verbosity = Silent | Quiet | Verbose | Trace | SuperTrace deriving (Eq,Ord,Show)


number x = zip [0..] x

split a = ([x | (x,b) <- zip a bl,b], [x | (x,b) <- zip a bl,not b])
  where bl = unfoldr (\b -> Just (b,not b)) True

splitN n a = [[x | (x,i) <- zip a il, i==j] | j <- [0..(n-1)]]
  where il = unfoldr (\b -> Just (b,(b+1) `mod` n)) 0

replaceNth [] _ _ = []
replaceNth (_:xs) 0 y = y : xs
replaceNth (x:xs) n y = x : replaceNth xs (n-1) y

for lo hi f = flip mapM_ [lo..hi] f

boolToInt True = 1
boolToInt False = 0

linesOn :: Char -> String -> [String]
linesOn c s = case dropWhile (==c) s of
                "" -> []
                s' -> let (w,s'') = break (==c) s' 
                      in  w : linesOn c s''

putStrIf   b str = when b $ putStr   str
putStrIfLn b str = when b $ putStrLn str
printIf    b str = when b $ print    str

fst3 (a,b,c) = a
snd3 (a,b,c) = b
thr3 (a,b,c) = c

fst4 (a,b,c,d) = a
snd4 (a,b,c,d) = b
thr4 (a,b,c,d) = c
fth4 (a,b,c,d) = d

parseArg x
      | length x >= 7 &&
        "arg_{" `isPrefixOf` x &&
        last x == '}' &&
        all (`elem` ['0'..'9']) (init $ drop 5 x) = Just (init $ drop 5 x)
      | otherwise = Nothing

{-
findFile :: FilePath -> IO [FilePath]
findFile f0 = do
  sp     <- getSearchPath
--  root   <- getHBCRootDir
  hbcEnv <- try (getEnv "HBC")
  let sp'  = case hbcEnv of { Right p -> p:sp ; _ -> sp }
  let sp'' = nub . map dropTrailingPathSeparator $ ("." : {- root ++ -} sp')
  filterM containsHBC sp''
  where
    containsHBC z   = doesFileExist (z </> f0)
    doesFileExist z = do
      res <- try (openFile z ReadMode)
      case res of
        Left  e -> return False
        Right h -> hClose h >> return True

getRequiredPaths :: [FilePath] -> IO String
getRequiredPaths files = mapM findFile files >>= getRequiredPaths'
  where
    getRequiredPaths' dirs
      | Just i <- findIndex null dirs = error $ "cannot find required file " ++ (files !! i) ++ " in current path and $HBC enviornment variable"
      | (p:_)  <- intersectAll dirs   = return p
      | otherwise                     = return (foldr1 (\s z -> s ++ [searchPathSeparator] ++ z) $ findIntersection [] dirs)
    intersectAll = foldr1 intersect
    findIntersection acc [] = acc
    findIntersection acc (dirs:rest)
      | null (dirs `intersect` acc) = findIntersection (head dirs : acc) rest
      | otherwise                   = findIntersection acc rest

getQualifiedPath :: FilePath -> IO FilePath
getQualifiedPath file = findFile file >>= qualify
  where
    qualify [] = error $ "Util.getQualifiedPath: cannot find file " ++ file
    qualify (".":_) = return file
    qualify (p:_) = return (p </> file)
-}

findFile f = return [f]
getRequiredPaths _ = return ""
getQualifiedPath f = return f

joinl s [] = []
joinl s [x] = x
joinl s (x:xs) = x ++ s ++ joinl s xs

hbcVersionString = show (fst hbcVersion) ++ "." ++ show (snd hbcVersion) ++ (if fst hbcVersion < 1 then " beta" else "")
hbcString =
    "     __  ____   ____\n" ++
    "    / / / /  \\ / __/  HBC: The Hierarchical Bayes Compiler\n" ++
    "   / /_/ / / // /     http://hal3.name/HBC/\n" ++
    "  / __  / --</ /      \n" ++
    " / / / / /  / /___    Version " ++ hbcVersionString ++ "\n" ++
    " \\/ /_/____/\\____/    \n"
    


