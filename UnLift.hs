-----------------------------------------------------------------------------
-- |
-- Module      :  UnLift
-- Project     :  HBC
-- Copyright   :  (c) Hal Daume III
-- License     :  Open
-- 
-- Maintainer  :  Hal Daume III <me@hal3.name>
-- Stability   :  stable
-- Portability :  portable
--
-- Removal of unnecessary lifting
--
-----------------------------------------------------------------------------

module UnLift where

import Core

import Data.List
import Data.Maybe
import Control.Monad
import Debug.Trace

simplify :: Core -> Core
simplify (Core dl) = Core [(v,unlift d,r) | (v,d,r) <- dl]

unlift :: Dist -> Dist
-- the first is the only interesting case
unlift (Prod r@(Range rid _ _) (d :^: e0@(Func f [Var (V vid []),e])) spv)
  | f == "=" && rid == vid = 
  case replaceVarRemove (V vid []) e d of
    Nothing -> Prod r ((unlift d) :^: e0) spv
    Just d' -> d'
unlift (Dist v id el) = Dist v id (map unliftE el)
unlift (a :*: b) = unlift a :*: unlift b
unlift (a :^: e) = unlift a :^: e
unlift (Prod r d spv) = Prod r (unlift d) spv

unliftE :: Expr -> Expr
unliftE (SP False r@(Range rid _ _) e spv) 
  | Just e' <- variableInFunction rid False "*"  [True ,True] e = replaceVarExpr (V rid []) e' e
  | Just e' <- variableInFunction rid False ".*" [True ,True] e = replaceVarExpr (V rid []) e' e
  | otherwise = SP False r (unliftE e) spv
unliftE (SP True  r@(Range rid _ _) e spv)
  | Just e' <- variableInFunction rid True  "^"  [False,True] e = replaceVarExpr (V rid []) e' e
  | Just e' <- variableInFunction rid True ".^"  [False,True] e = replaceVarExpr (V rid []) e' e
  | otherwise = SP True r (unliftE e) spv
unliftE (Func i el) = Func i $ map unliftE el
unliftE e = e

variableInFunction id sp skip ent (SP b r e _)
  | b == sp   = variableInFunction id sp skip ent e
  | otherwise = Nothing
variableInFunction id sp skip ent (Func f el)
  | f == skip = msum $ zipWith (\b e -> if b then variableInFunction id sp skip ent e else Nothing) ent el
  | f == "="  = 
      case el of
        [Var (V i []),b] | i == id -> Just b
        [a,Var (V i [])] | i == id -> Just a
        _ -> Nothing
variableInFunction _ _ _ _ _ = Nothing

