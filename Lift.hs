-----------------------------------------------------------------------------
-- |
-- Module      :  Lift
-- Project     :  HBC
-- Copyright   :  (c) Hal Daume III
-- License     :  Open
-- 
-- Maintainer  :  Hal Daume III <me@hal3.name>
-- Stability   :  stable
-- Portability :  portable
--
-- Perform index lifting on declarations
--
-----------------------------------------------------------------------------
module Lift(lift) where

import Decl
import Util
import Data.List

-- | lift takes a module and lifts *all* variables.  note that it does
-- | *not* fill in ranges -- this can only happen after type-checking.
-- | instead, it sets the range to be 'VAR ""' on both low and high
-- | ends.

lift :: MOD -> MOD
lift (MOD decls) = MOD $ map (uncurry liftDecl) $ number decls

liftDecl ii (DECL lhs (RHS d el lift) rl) = DECL lhs (RHS d el' lift') rl
  where
    storeN      = splitN (length el) [("*" ++ show ii ++ "*" ++ show kk ++ "*") | kk <- [0..]]
    (lift',el') = mapAccumL (\lift (s,e) -> liftExpr s lift e) lift (zip storeN el)
liftDecl _ d = d

-- | the real work happens in liftExpr

liftExpr :: [VAR] -> [(EXPR,EXPR)] -> EXPR -> ([(EXPR,EXPR)], EXPR)
liftExpr store acc (VAR v) = (acc, VAR v)
liftExpr store acc (IND v el) 
--  | mytrace (show (IND v el, acc, (acc', el'), (findIndex (not . simple) el'))) False = undefined
  | otherwise = 
  case findIndex (not . simple) el' of
    Nothing -> (acc, IND v el)
    Just i  -> liftExpr ss ((VAR s, el'!!i):acc') (IND v (replaceNth el' i (VAR s)))   -- this can be made much more efficient; O(N^2) to O(N)
  where
    ((s:ss):storeN) = splitN (1+length el) store
    (acc', el')     = mapAccumL (\acc (s,e) -> liftExpr s acc e) acc (zip storeN el)
liftExpr store acc (FN v el) = (acc', FN v el')
  where { storeN = splitN (length el) store ; (acc', el') = mapAccumL (\acc (s,e) -> liftExpr s acc e) acc (zip storeN el) }
liftExpr store acc (SUMPP b (RANGE v lo hi) e) = (acc''', SUMPP b (RANGE v lo' hi') e')
  where
    [store0,store1,store2] = splitN 3 store
    (acc'  , lo') = liftExpr store0 acc   lo
    (acc'' , hi') = liftExpr store1 acc'  hi
    (acc''', e' ) = liftExpr store2 acc'' e
liftExpr store acc (CONST c) = (acc, CONST c)
liftExpr store acc (CASE cv cs) = (acc', CASE cv' cs')
  where
    (storeCV:storeDF:storeCS) = splitN (2+length cs) store
    (accCV, cv') = liftExpr storeCV acc   cv
    (acc' , cs') = mapAccumL (\acc (s,(e,f)) -> 
                                  let [se,sf]   = splitN 2 s
                                      (acc' ,e') = liftExpr se acc  e
                                      (acc'',f') = liftExpr sf acc' f
                                  in  (acc'', (e',f'))
                             ) accCV (zip storeCS cs)

simple (VAR _)    = True
simple (IND _ []) = True
simple (FN "+" [VAR   _, CONST _]) = True
simple (FN "+" [CONST _, CONST _]) = True
simple (FN "+" [CONST _, VAR   _]) = True
simple (FN "-" [VAR   _, CONST _]) = True
simple (FN "-" [CONST _, CONST _]) = True
simple (FN "-" [CONST _, VAR   _]) = True
simple (CONST _)  = True
simple _          = False

