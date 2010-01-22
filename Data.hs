-----------------------------------------------------------------------------
-- |
-- Module      :  Data
-- Project     :  HBC
-- Copyright   :  (c) Hal Daume III
-- License     :  Open
-- 
-- Maintainer  :  Hal Daume III <me@hal3.name>
-- Stability   :  stable
-- Portability :  portable
--
-- Loading of data from simple file formats
--
-----------------------------------------------------------------------------

module Data where

import Simulate(SimType(..), showSimType)
import Data.Maybe
import Data.List
import Debug.Trace 
import Control.Monad
import Control.Monad.State
import Data.Array.IO
import Util

loadDiscrete :: [Char] -> FilePath -> IO (SimType, SimType, [SimType])
loadDiscrete seps filepath = do
  txt     <- readFile filepath
  (w, mx) <- makeSeps seps txt
  d       <- getDims w
  return (w, mx, d)
  where
    makeSeps []     t = newListArray (1,length w) w' >>= \a -> return (AA a, maximum w')
      where w  = words t
            w' = map (II . read) w
    makeSeps (c:cs) t = do
      arr <- mapM (makeSeps cs) t'
      a   <- newListArray (1,length t') (map fst arr)
      return (AA a, maximum (map snd arr))
      where t' = linesOn c t

loadMatrix :: FilePath -> IO (SimType, SimType, SimType)
loadMatrix filepath = do
  mat <- (map (map (RR . read) . words) . lines) `liftM` readFile filepath
  let n = length mat
  let d = maximum (map length mat)
  a <- newListArray (1,n) =<< mapM (makeVector d) mat
  return (AA a, II n, II d)
  where
    makeVector d vals = return . AA =<< newListArray (1,d) (vals ++ rest)
      where rest = replicate (d - length vals) (RR 0)

loadMatrixInt :: FilePath -> IO (SimType, SimType, SimType)
loadMatrixInt filepath = do
  mat <- (map (map (II . read) . words) . lines) `liftM` readFile filepath
  let n = length mat
  let d = maximum (map length mat)
  a <- newListArray (1,n) =<< mapM (makeVector d) mat
  return (AA a, II n, II d)
  where
    makeVector d vals = return . AA =<< newListArray (1,d) (vals ++ rest)
      where rest = replicate (d - length vals) (II 0)

getDims :: SimType -> IO [SimType]
getDims (II _) = return [II 0]
getDims (RR _) = return [II 0]
getDims (AA a) = do
  (lo,hi)  <- getBounds a
  let myDim = II (hi-lo+1)
  index0   <- readArray a lo
  rest     <- case index0 of
                (AA _) -> do
                  dims <- mapM getDims =<< getElems a
                  mapM (\d -> return . AA =<< newListArray (lo,hi) d) (transpose dims)
                _      -> return []
  return (myDim : rest)

