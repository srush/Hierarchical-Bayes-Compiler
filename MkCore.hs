-----------------------------------------------------------------------------
-- |
-- Module      :  MkCore
-- Project     :  HBC
-- Copyright   :  (c) Hal Daume III
-- License     :  Open
-- 
-- Maintainer  :  Hal Daume III <me@hal3.name>
-- Stability   :  stable
-- Portability :  portable
--
-- Perform all operations necessary to convert DECL to Core
--
-----------------------------------------------------------------------------

module MkCore where -- (mkCore, coreToPrior) where

import Decl
import Core
import Util
import Blanket
import Reindex
import Lift
import Translate
import Data.Maybe

import qualified Math (simplify)
import qualified UnLift (simplify)

-- mkCore assumes that imports have already been loaded, renamed and added
-- to the module
mkCore :: MOD -> Core
mkCore mod
  | mytrace ("\n[lMod=" ++ show lMod ++ "]\n") False = undefined
  | mytrace ("\n[blankets=" ++ show blankets ++ "]\n") False = undefined
  | mytrace ("\n[reInd=" ++ show reInd ++ "]\n") False = undefined
  | mytrace ("\n[ranges=" ++ show ranges ++ "]\n") False = undefined
  | otherwise = fiddleSP $ Core (zipWith3 mkTranslation decls reInd ranges)
  where
    -- first, perform lifting
    lMod@(MOD decls) = lift mod
    nn = length decls

    -- second, identify markov blankets
    blankets = map (blanket lMod) [0..(nn-1)]

    -- third, reindex all blankets
    reInd = zipWith (\l j -> map (\ (i,e) -> reindex (decls!!j) (decls!!i) e) l) blankets [0..]

    -- extract ranges
    ranges = map (\d -> case d of { DECL _ _ r -> r ; TDECL _ _ r -> r ; _ -> [] }) decls
--zipWith (\d (i,e) -> map (reindex d.snd)) decls blankets

coreToPrior :: Core -> Core
coreToPrior core = Core (mapMaybe coreToPrior' dl)
  where
    Core dl = unliftCore core

    coreToPrior' (var, dist, rl) =
      case findPriorDist var dist of
        [] -> Nothing
        l  -> Just (var, foldr1 (:*:) l, rl)
    findPriorDist var d@(Dist v _ _) 
      | v == var  = [d]
      | otherwise = []
    findPriorDist var (a :*: b)  = findPriorDist var a ++ findPriorDist var b
    findPriorDist var (a :^: _)  = findPriorDist var a
    findPriorDist var (Prod _ d _) = findPriorDist var d

{-
lMod@(MOD decls) = lift TestLDA.ldaMOD
nn = length decls
blankets = map (blanket lMod) [0..(nn-1)]
reInd = zipWith (\l j -> map (\ (i,e) -> reindex (decls!!j) (decls!!i) e) l) blankets [0..]
-}

mkTranslation :: DECL -> [((VAR, [EXPR]), RHS, [RANGE])] -> [RANGE] -> (Var, Dist, [Range])
mkTranslation (DECL (LHS v0 ind0) rhs ranges) rhsL range0 =
  (var0, foldr (:*:) prior $ map (mkRHS range0 ranges) rhsL, map translateRange range0)
  where
    var0  = V v0 (map (\i -> Id i Nothing) ind0)
    prior = rhsToPrior var0 rhs
mkTranslation (TDECL (LHS v0 ind0) (numDist,typ,el) ranges) _ range0 = (var0, Dist var0 (typ:numDist0) el', map translateRange range0)
  where
    numDist0 = if numDist == 0 then "" else show numDist
    var0  = V v0 (map (\i -> Id i Nothing) ind0)
    el'   = map translateExpr el
mkTranslation decl rhsL range0 = error $ "MkCore.mkTranslation: cannot process decl " ++ show decl ++ " with rhs " ++ show rhsL ++ " and range " ++ show range0

rhsToPrior var0 (RHS dist e lift) = addLift [] lift (Dist var0 dist $ map translateExpr e)

mkRHS :: [RANGE] -> [RANGE] -> ((VAR, [EXPR]), RHS, [RANGE]) -> Dist
mkRHS priorRange ranges0 ((v,ind), RHS dist e lift, ranges) = foldr addRange post unR
  where
    qual = [v | RANGE v _ _ <- priorRange]
    var0 = V v (map translateSExpr ind)
    post = addLift qual lift (Dist var0 dist $ map translateExpr e)
    unR  = filter (unqualifiedRanges ranges0) ranges

addLift :: [VAR] -> LIFT -> Dist -> Dist
addLift preQual lift d 
  | mytrace ("addLift " ++ show (lift,d)) False = undefined
  | otherwise = foldr addLiftProd (foldr addLiftExp d lift) lift'
  where
    lift' = [(l,r) | (l,r) <- lift, case l of { VAR v -> not (v `elem` preQual) ; _ -> True }]

    addLiftProd (v,_) d = Prod (unkRange v) d ""
    addLiftExp  (v,e) d = d :^: (Func "=" [translateExpr v, translateExpr e])

--    addLift' (v,e) d = 
--      Prod (unkRange v) (d :^: (Func "=" [translateExpr v, translateExpr e])) ""
    unkRange v = Range (head $ exprVars v) unkV unkV

unqualifiedRanges :: [RANGE] -> RANGE -> Bool
unqualifiedRanges l r = not (rangeLHS r `elem` map rangeLHS l)
  where rangeLHS (RANGE v _ _) = v

addRange :: RANGE -> Dist -> Dist
addRange r d = Prod (translateRange r) d ""


simplifyAllCore Nothing = unliftCoreE . unliftCore . fixOffsets . Math.simplify . UnLift.simplify
simplifyAllCore (Just glob) = removeExtraSums glob . simplifyAllCore Nothing

simplifyAllCoreE glob e = e'
  where
    c0 = Core [(V "" [],Dist (V "" []) "" [e],[])]
    Core [(_,Dist _ _ [e'],_)] = simplifyAllCore glob c0

simplifyAllCoreUpdate glob (rl,Var v,e) 
  | mytrace (show ("simplifyAllCoreUpdate",(glob,rl,v,e),(c0,c1,c2),(e',rl',v'))) True = (rl',v',e')
  where
    c0 = Core [(V "" [], addProducts 1 rl (Dist (V "" []) "" [e]), [])]
    c1 = simplifyAllCore Nothing c0
    c2@(Core [(_, d', _)]) = removeExtraSums (fromJust glob) c1

    (rl',e',v') = remProducts d'

    addProducts n [] d = d :*: Dist (V "" []) "" [Var v]
    addProducts n (r:rl) d = Prod r (addProducts (n+1) rl d) ("addP" ++ show n)

    remProducts (Prod r d _) = let (rl,e,v) = remProducts d in (r:rl, e, v)
    remProducts ((Dist _ _ [e]) :*: (Dist _ _ [v]))  = ([], e, v)


