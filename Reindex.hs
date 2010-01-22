-----------------------------------------------------------------------------
-- |
-- Module      :  Reindex
-- Project     :  HBC
-- Copyright   :  (c) Hal Daume III
-- License     :  Open
-- 
-- Maintainer  :  Hal Daume III <me@hal3.name>
-- Stability   :  stable
-- Portability :  portable
--
-- Implementation of the reindexing of RHSs to account for different
-- appearances of the variable we care about.  We assume that this step 
-- is performed *after* lifting; this means that (a) we have to handle 
-- lifts (bad), and (b) we can assume all INDs are semi-simple (good).
--
-----------------------------------------------------------------------------

module Reindex(reindex) where

import Decl
import Util
import Data.Maybe
import Debug.Trace
import Data.List
import Data.Generics hiding ((:*:))
import Data.Generics.Basics
import Data.Generics.Schemes

reindex :: DECL -> DECL -> EXPR -> ((VAR, [EXPR]), RHS, [RANGE])
reindex d0l@(DECL (LHS v0 ix0) _ _) d0r@(DECL (LHS v1 ix1) (RHS dist el lift) ranges) e0 
  | mytrace ("\nd0l=" ++ show d0l) False = undefined
  | mytrace ("\nd0r=" ++ show d0r) False = undefined
  | mytrace ("\ne0=" ++ show e0) False = undefined
  | mytrace ("\nix0=" ++ show ix0) False = undefined
  | mytrace ("\nix1=" ++ show ix1) False = undefined
  | mytrace ("\nixMap=" ++ show ixMap) False = undefined
  | mytrace ("\nixMap'=" ++ show ixMap') False = undefined
  | mytrace ("\nres=" ++ show res) False = undefined
  | mytrace ("\nremProd=" ++ show remProd) False = undefined
  | mytrace ("\nel'=" ++ show (map (removeProducts remProd) el)) False = undefined
  | mytrace ("\nlift'=" ++ show (map (removeProducts remProd) lift)) False = undefined
  | otherwise = res
  where
    res = ((v1, map (applyMap ixMap'.VAR) ix1), rhs', ranges')

    remProd = map fst ixMap -- remove any products that include variables that are getting renamed

    -- anything that appears in ix0 that doesn't appear on the LHS of ixMap needs
    -- to also be re-indexed
    ixMap'= ixMap ++ [(v, VAR ("ri_" ++ v))
                     | v <- ix0
                     , not (v `elem` map fst ixMap)]

    ixMap = 
      case e0 of
        VAR v | null (ix0 `intersect` ix1) -> []   -- TODO: not sure if this is correct!
        IND v ix {- | length ix == length ix0 -} -> 
          mapMaybe id (zipWith findIndexMap ix0 ix)
--          mapMaybe id $ zipWith (\i0 z -> case z of { Just zz -> Just (findIndexMap i0 zz) ; _ -> Nothing }) ix0 ix'
         -- we only want to include in ix the variables that also appear in ix1
--          where ix' = map (\i -> case i of
--                                   VAR v | v `elem` ix1 -> Just i
--                                   _ -> Nothing) ix


        _ -> error ("Reindex.reindex: cannot compute index map (" ++ show v0 ++ ") for " ++ show ix0 ++ " and (" ++ show v1 ++ ") " ++ show e0 ++ " versus " ++ show (v1,ix1))

    rhs'    = RHS dist (map (applyMap ixMap' . removeProducts remProd) el) (map (applyMapLift ixMap') lift)
    ranges' = map (applyMapRange ixMap') ranges
reindex _ (DECL (LHS v1 ix1) rhs ranges) e0 = ((v1, map VAR ix1), rhs, ranges)

-- simple examples: 
--    findIndexMap n m --> (n,m)
--    findIndexMap n n+1 --> (n, n-1)
--    findIndexMap n m+1 --> (m, n-1)
findIndexMap :: VAR -> EXPR -> Maybe (VAR, EXPR)
findIndexMap v0 e = findIndexMap' e (VAR v0)
  where
    findIndexMap' (VAR v) e0 = Just (v, e0)
    findIndexMap' (FN "exp" [a]) e0 = findIndexMap' a (FN "log" [e0])
    findIndexMap' (FN "log" [a]) e0 = findIndexMap' a (FN "exp" [e0])
    findIndexMap' f@(FN op  [a,b]) e0
      | mytrace (show ("findIndexMap'", f, e0, hasVar a, hasVar b, op)) False = undefined
      | hasVar a && hasVar b        = error ("Reindex.findIndexMap':: both L and R have variables in " ++ show f)
      | not (hasVar a || hasVar b)  = error ("Reindex.findIndexMap':: neither L nor R have variables in " ++ show f)
      | hasVar a && op == "+"       = findIndexMap' a (FN "-" [e0,b])
      | hasVar b && op == "+"       = findIndexMap' b (FN "-" [e0,a])
      | hasVar a && op == "-"       = findIndexMap' a (FN "+" [e0,b])
      | hasVar b && op == "-"       = findIndexMap' b (FN "+" [a,e0])
      | otherwise                   = error ("Reindex.findIndexMap':: cannot invert function in " ++ show f)
      where
        hasVar = not . null . exprIds
    findIndexMap' v        e0      = Nothing -- error ("Reindex.findIndexMap':: cannot map " ++ show v)

applyMap :: [(VAR,EXPR)] -> EXPR -> EXPR
applyMap m (VAR v) = fromMaybe (VAR v) $ lookup v m
applyMap m (IND v el)
  | v `elem` map fst m = error ("Reindex.applyMap: map contains indexed variable '" ++ show v ++ "'; maybe lifting failed")
  | otherwise          = IND v $ map (applyMap m) el
applyMap m (FN f el) = FN f $ map (applyMap m) el
applyMap m (SUMPP b r e) = SUMPP b (applyMapRange m r) (applyMap m e)
applyMap m (CONST c) = CONST c
applyMap m (CASE cv cs) = CASE (applyMap m cv) (map (\ (e,f) -> (applyMap m e, applyMap m f)) cs)

applyMapRange m r0@(RANGE v lo hi)
  | Just (VAR v') <- lookup v m = RANGE v' lo' hi'
  | Nothing       <- lookup v m = RANGE v  lo' hi'
  | otherwise                   = RANGE v  lo' hi'
--  | otherwise                   = error $ "Reindex.applyMapRange: map contains range variable in non-variable form: map=" ++ show m ++ " range=" ++ show r0
  where
    lo' = applyMap m lo
    hi' = applyMap m hi

--applyMapRange m (RANGE v lo hi) = RANGE (v {-fromMaybe v $ lookup v m -}) (applyMap m lo) (applyMap m hi)  -- todo: fix this; apply change in index to ranges!
--  | v `elem` map fst m = error ("Reindex.applyMapRange: map contains range variable " ++ show v)
--  | otherwise          = RANGE v (applyMap m lo) (applyMap m hi)

--applyMapLift m (VAR v,e) | v `elem` map fst m = (VAR "?", applyMap
applyMapLift m (v,e) = (applyMap m v, applyMap m e)
--  | v `elem` map fst m = error ("Reindex.applyMapLift: map contains lifted variable " ++ show v)
--  | otherwise          = (v, applyMap m e)

removeProducts remProd = everywhere (mkT removeProducts')
  where
    removeProducts' (SUMPP True (RANGE v _ _) e)
      | v `elem` remProd = e
    removeProducts' e = e
