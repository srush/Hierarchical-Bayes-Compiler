-----------------------------------------------------------------------------
-- |
-- Module      :  Stats
-- Project     :  HBC
-- Copyright   :  (c) Hal Daume III
-- License     :  Open
-- 
-- Maintainer  :  Hal Daume III <me@hal3.name>
-- Stability   :  stable
-- Portability :  portable
--
-- Statistics package for implementing ldf and sampling functions
--
-----------------------------------------------------------------------------

module Stats where

import System.Random
import Control.Monad
import Data.List

import Data.IORef
import System.IO.Unsafe

data Exp     = Exp     Double          deriving (Eq,Ord,Show)
data Bin     = Bin     Double          deriving (Eq,Ord,Show)
data Gam     = Gam     Double   Double deriving (Eq,Ord,Show)
data Poi     = Poi     Double          deriving (Eq,Ord,Show)
data Bet     = Bet     Double   Double deriving (Eq,Ord,Show)
data Nor     = Nor     Double   Double deriving (Eq,Ord,Show)
data NorMV   = NorMV   [Double] Double deriving (Eq,Ord,Show)
data Dir     = Dir     [Double]        deriving (Eq,Ord,Show)
data SymDir  = SymDir  Int      Double deriving (Eq,Ord,Show)
data Mult    = Mult    [Double]        deriving (Eq,Ord,Show)
data SymMult = SymMult Int             deriving (Eq,Ord,Show)

zero = -1/0

epsilonValue = unsafePerformIO $ newIORef (1e-10 :: Double)

eps  :: IO Double -- get epsilon
eps  = readIORef epsilonValue

boundLo :: Double -> IO Double
boundLo a = eps >>= \e -> return $ max e a

boundHi :: Double -> IO Double
boundHi a = eps >>= \e -> return $ min (1-e) a

bound   :: Double -> IO Double
bound   a = eps >>= \e -> return $ max e (min (1-e) a)

class Stats a b | a -> b where
  sample   :: a -> IO b
  ldf      :: a -> b -> Double
  mode     :: a -> b

instance Stats Poi Int where
  sample (Poi la) = sample' 0 1
    where 
      l = exp (-la)
      sample' k p = do
        u <- randomRIO (0::Double,1)
        let p' = p * u
        if p' < l
          then return  (k+1)
          else sample' (k+1) p'
  ldf (Poi la) x = - factln (fromIntegral x) - la - (fromIntegral x) * log la
  mode (Poi la) = floor (la - 1e-10)

instance Stats SymMult Int where
  sample (SymMult dim) = randomRIO (1,dim)
  ldf (SymMult dim) i
    | i < 1 || i > dim = 0
    | otherwise        = -log(fromIntegral dim)
  mode _ = 1 -- arbitrary

instance Stats Mult Int where
  sample (Mult l) = do
    r <- randomRIO (0, sum l)
    return (sample' 1 r l)
    where
      sample' i r []  = error "Stats.sample(Mult): empty list"
      sample' i r [x] = i
      sample' i r (x:xs) | r-x <= 0 = i
                         | otherwise = sample' (i+1) (r-x) xs
  ldf (Mult l) i
    | i < 1 || i > length l = (-1/0)
    | otherwise = log(l !! (i-1) / sum l)

  mode (Mult l) = snd $ maximum $ zip l [1..]

instance Stats SymDir [Double] where
  sample (SymDir i val) = sample (Dir (replicate i val))
  ldf (SymDir i val) = ldf (Dir (replicate i val))
  mode (SymDir i _) = replicate i (1 / (fromIntegral i))

instance Stats Dir [Double] where
  sample (Dir alpha) = do
    th <- mapM (\a -> sample (Gam a 1)) alpha
    mapM bound (map (/sum th) th)

  ldf (Dir alpha) l
    | length alpha /= length l = error ("Stats.ldf(Dir): dimension mismatch")
    | otherwise = norm + sum (zipWith (\a th -> (a-1) * log(boundTh (th/sum l))) alpha l)
    where norm = gammaln(sum alpha) - sum (map gammaln alpha)
          boundTh th = max (1-1e-10) $ min (1e-10) th

  mode (Dir alpha) = map (/ sum alpha) alpha

instance Stats Gam Double where
  sample (Gam a b) 
    | a < 1 = do { g <- sample (Gam (a+1) b) ; u <- randomIO ; boundLo (g*(u**(1/a))) }
    | otherwise = sample' >>= boundLo
    where
      d = a - 1/3
      c = 1/3/sqrt d
      sample' = do
        x <- rand_stdnormal
        u <- randomIO
        let v = (1+c*x) * (1+c*x) * (1+c*x)
        if v > 0 && log(u) < 0.5*x*x + d - d*v + d*log v
          then return (d*v/b)
          else sample'
  ldf (Gam a b) x | x < 0 = zero
                  | otherwise = norm + (a-1) * log x - x / b
    where norm = -a * log b - gammaln a

  mode (Gam a b) = if a > 1 then (a-1)*b else a*b  -- give mean if the mode doesn't exist

instance Stats Bet Double where
  sample (Bet a b) = do
    x <- sample (Gam a 1)
    y <- sample (Gam b 1)
    bound (x / (x+y))
  ldf (Bet a b) x | x < 0 || x > 1 = zero
                  | otherwise = norm + (a-1)*log x + (b-1)*log (1-x)
    where norm = gammaln(a+b) - gammaln a - gammaln b
  mode (Bet a b)
    | a > 1 && b > 1 = (a-1) / (a+b-2)
    | otherwise = a / (a+b) -- give mean if mode doesn't exist

instance Stats Bin Bool where
  sample (Bin pi) = randomIO >>= return . (<=pi)
  ldf (Bin pi) x | x = log pi
                 | otherwise = log (1-pi)
  mode (Bin pi) = pi > 0.5

instance Stats Nor Double where
  sample (Nor mu si2) = rand_stdnormal >>= return . (+mu) . (*si2)
  ldf (Nor mu si2) x = norm - 0.5 * (x-mu) * (x-mu) / si2
    where norm = -0.5 * log(2*pi*si2)
  mode (Nor mu _) = mu

instance Stats NorMV [Double] where
  sample (NorMV mu si2) = do
    x <- sequence $ replicate (length mu) rand_stdnormal
    return (zipWith (\x m -> m + x*si2) x mu)
  ldf (NorMV mu si2) x | length x /= length mu = error "Stats.ldf(NorMV): dimension mismatch"
                       | otherwise = norm - 0.5 * d / si2
    where d    = sum $ zipWith (\a b -> (a-b) * (a-b)) x mu
          dim  = fromIntegral $ length mu
          norm = -dim/2 * log(2*pi*si2)
  mode (NorMV mu _) = mu

instance Stats Exp Double where
  sample (Exp la) = randomIO >>= \u -> boundLo (-log(u)/la)
  ldf (Exp la) x | x < 0 = error "Stats.sample(Exp): x < 0"
                 | otherwise = norm - la * x
    where norm = log la
  mode (Exp _) = 0

-----------------------------------------------------------------------------



{-

class Stats a b => MaxLik a b where
  maxLik :: [b] -> a

class (Stats a b, MaxLik a b, Stats c d) => Conjugate a b c d where
  conjugate :: c -> [b] -> c

instance MaxLik Poi Int where
  maxLik k = Poi (fromIntegral (sum k) / fromIntegral (length k))

instance MaxLik Mult Int where
  maxLik k = Mult [genericLength [i | i <- k, i==j] / n | j <- [1..maximum k]]
    where n = genericLength k

instance MaxLik Bin Bool where
  maxLik x = Bin (genericLength (filter id x) / genericLength x)

instance MaxLik Nor Double where
  maxLik x = Nor mu si2
    where
      mu  = mean x
      si2 = (sum $ map (\x -> (x-mu)*(x-mu)) x) / (genericLength x - 1)

instance MaxLik NorMV [Double] where
  maxLik x = NorMV mu si2
    where
      dim = length (head x)
      mu  = [mean (map (!!i) x) | i <- [0..dim-1]]
      si2 = (sum [(a-m)*(a-m) | y <- x, (a,m) <- zip y mu]) / ((fromIntegral dim) * (genericLength x - 1))

instance MaxLik Exp Double where
  maxLik x = Exp (mean x)

instance Conjugate Poi Int Gam Double where
  conjugate (Gam a b) x = Gam (a + fromIntegral (sum x)) (b + genericLength x)

-}

factln = gammaln . (+1)

gammaln n 
  | n < 0     = error ("Stats.gammaln: input < 0")
  | n >= 2.1  = -(n-1) + (n-1)*log(n-1) + 0.5 * log((2*(n-1)+1/3)*pi)
  | otherwise = gammaln(n+1) - log(n)

digamma k 
  | k >= 8    = log(k) - (1+(1-(1/10-1/(21*k*k))/k/k)/6/k)/2/k
  | otherwise = digamma(k+1) - 1/k

trigamma k
  | k >= 8    = (1+(1+(1-(1/5-1/7/k/k)/k/k)/3/k)/2/k)/k
  | otherwise = trigamma(k+1) + 1/k/k

rand_stdnormal :: IO Double
rand_stdnormal =
  ((\x -> x-6) . sum) `liftM` sequence (replicate 12 randomIO)

mean l = sum l / genericLength l
var  l = sum (map (\x -> (x-mu)*(x-mu)) l) / genericLength l
  where mu = mean l

addLog x y
  | x == zero  = y
  | y == zero  = x
  | x - y > 16 = x
  | x > y      = x + log(1 + exp(y-x))
  | y - x > 16 = y
  | otherwise  = y + log(1 + exp(x-y))

addLogs = foldr addLog zero

