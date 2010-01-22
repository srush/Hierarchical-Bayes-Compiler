-----------------------------------------------------------------------------
-- |
-- Module      :  Math
-- Project     :  HBC
-- Copyright   :  (c) Hal Daume III
-- License     :  Open
-- 
-- Maintainer  :  Hal Daume III <me@hal3.name>
-- Stability   :  stable
-- Portability :  portable
--
-- Simplify mathematical expressions
--
-----------------------------------------------------------------------------

module Math where

import Core
import Data.Generics hiding ((:*:))
import Data.Typeable


simplify (Core dl) = Core [(v,simplifyDist d,r) | (v,d,r) <- dl]

simplifyDist d0 | d0 == d = d
                | otherwise = simplifyDist d
  where d = simplifyDist0 d0

simplifyDist0 (Dist v i el) = Dist v i $ map simplifyExpr el
simplifyDist0 (a :*: b) = simplifyDist0 a :*: simplifyDist0 b
simplifyDist0 (a :^: e) | isOne e = simplifyDist0 a
                        | otherwise = simplifyDist0 a :^: simplifyExpr e
simplifyDist0 (Prod r d spv) = Prod r (simplifyDist0 d) spv

simplifyExprMany e = let e' = everywhere (mkT simplifyExpr) e in if e == e' then e else simplifyExprMany e'
simplifyExpr = equality . arithIdent

-- replace "a=a" with 1 and "a~=a" with 0
equality (Func "="  [a,b]) | a == b = Con (I 1)
equality (Func "<=" [a,b]) | a == b = Con (I 1)
equality (Func ">=" [a,b]) | a == b = Con (I 1)
equality (Func "~=" [a,b]) | a == b = Con (I 0)
equality (Func "<"  [a,b]) | a == b = Con (I 0)
equality (Func ">"  [a,b]) | a == b = Con (I 0)
equality (Func f el) = Func f $ map equality el
equality (SP b r e spv) = SP b r (equality e) spv
equality e = e

-- replace "1*a" and "a*1" with a; "0+a" and "a+0" with a; etc
arithIdent (Func "+"  [a,b]) | isZero a = b
                             | isZero b = a
arithIdent (Func ".+" [a,b]) | isZero a = b
arithIdent (Func "-"  [a,b]) | isZero a = b
arithIdent (Func "*"  [a,b]) | isOne  a = b
                             | isOne  b = a
                             | isZero a = a
                             | isZero b = b
arithIdent (Func ".*" [a,b]) | isOne  a = b
arithIdent (Func "/"  [a,b]) | isOne  b = a
                             | isZero a = a
arithIdent (Func "^"  [a,b]) | isOne  b = a
arithIdent (Func f el) = Func f $ map arithIdent el
arithIdent (SP b r e spv) = SP b r (arithIdent e) spv
arithIdent e = e

isZero (Con (I 0)) = True
isZero (Con (R 0)) = True
isZero _ = False

isOne (Con (I 1)) = True
isOne (Con (R 1)) = True
isOne _ = False
