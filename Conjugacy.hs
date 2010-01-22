-----------------------------------------------------------------------------
-- |
-- Module      :  Conjugacy
-- Project     :  HBC
-- Copyright   :  (c) Hal Daume III
-- License     :  Open
-- 
-- Maintainer  :  Hal Daume III <me@hal3.name>
-- Stability   :  stable
-- Portability :  portable
--
-- Implementation of conjugacy simplification
--
-----------------------------------------------------------------------------

module Conjugacy where

import Core

import Data.List
import Data.Maybe
import Control.Monad
import Util
import qualified UnLift
import Math

-- to allow for user-defined conjugacy rules
data Conjugate = Conjugate { prior :: Id
                           , likelihood :: Id
                           , posterior  :: Id   -- allow distribution switching, eg., DirSym -> Dir
                           , matching   :: Int  -- which expression index in the posterior has to match the prior parameter
                           , idxdelta   :: Int  -- difference in # of indices between prior on posterior.  eg. Gam(a_k) vs Dir(a) --> idxdelta = 1 because
                                                --              there should be one more index on the prior
                           , suffstats  :: [SExpr] -> [Expr] -> Lik -> [Expr]
                           }

-- type of likelihoods
type Lik = [([Range],Maybe [Expr],Dist,[Expr])]
          -- (rl,Nothing,d,el) means prod_rl d^(prod el)
          -- (rl,Just e ,d,el) means prod_rl d'^(prod el)
          --       where d' is the same as d, but the LHS is e

-- standard rules
conjugacyRules =
    [ Conjugate { prior      = "Dir"
                , likelihood = "Mult"
                , posterior  = "Dir"
                , matching   = 0
                , idxdelta   = 0
                , suffstats  = const conjDirMult
                }
    , Conjugate { prior      = "DirSym"
                , likelihood = "Mult"
                , posterior  = "Dir"
                , matching   = 0
                , idxdelta   = 0
                , suffstats  = const conjDirSymMult
                }
    , Conjugate { prior      = "PY"
                , likelihood = "Mult"
                , posterior  = "PY"
                , matching   = 0
                , idxdelta   = 0
                , suffstats  = const conjPYMult
                } 
    , Conjugate { prior      = "NorMV"
                , likelihood = "NorMV"
                , posterior  = "NorMV"
                , matching   = 0
                , idxdelta   = 0
                , suffstats  = const (conjNorNor True)
                }
    , Conjugate { prior      = "Nor"
                , likelihood = "Nor"
                , posterior  = "Nor"
                , matching   = 0
                , idxdelta   = 0
                , suffstats  = const (conjNorNor False)
                }
    , Conjugate { prior      = "Gam"
                , likelihood = "Exp"
                , posterior  = "Gam"
                , matching   = 0
                , idxdelta   = 0
                , suffstats  = const conjGamExp
                }
    , Conjugate { prior      = "Bet"
                , likelihood = "Bin"
                , posterior  = "Bet"
                , matching   = 0
                , idxdelta   = 0
                , suffstats  = const conjBetBin
                }
    , Conjugate { prior      = "Gam"
                , likelihood = "DirSym"
                , posterior  = "Gam"
                , matching   = 0
                , idxdelta   = 0
                , suffstats  = const conjGamDirSym
                }
    , Conjugate { prior      = "Gam"
                , likelihood = "Dir"
                , posterior  = "Gam"
                , matching   = 0
                , idxdelta   = 1
                , suffstats  = conjGamDir
                }
    , Conjugate { prior      = "Gam"
                , likelihood = "Poi"
                , posterior  = "Gam"
                , matching   = 0
                , idxdelta   = 0
                , suffstats  = const conjGamPoi
                }
    , Conjugate { prior      = "IG"
                , likelihood = "NorMV"
                , posterior  = "IG"
                , matching   = 1
                , idxdelta   = 0
                , suffstats  = const (conjGamNor True)
                }
    , Conjugate { prior      = "IG"
                , likelihood = "Nor"
                , posterior  = "IG"
                , matching   = 1
                , idxdelta   = 0
                , suffstats  = const (conjGamNor False)
                }
    , Conjugate { prior      = "IG"
                , likelihood = "Gam"
                , posterior  = "IG"
                , matching   = 1   -- match the rate parameter
                , idxdelta   = 0
                , suffstats  = const conjIGGam
                } 
    ]


conjDirMult [al,len] lik 
--  | mytrace (show ("conjDirMult:", al,len,lik)) True 
  = [Func "+" [al, foldr1 (\a b -> Func "+" [a,b]) $ map conj lik], len]
  where
    conj (rl, Nothing, Dist v _ _, el) = foldr makeSum (foldr makeProd' v0 el) rl
      where v0 = Func "IDR" [Var v, Con (I 1), len]
    
conjDirSymMult [al,len] lik = [Func "+" [al0, foldr1 (\a b -> Func "+" [a,b]) $ map conj lik], len]
  where
    al0 = Func "vec" [al, Con (I 1), len]
    conj (rl, Nothing, Dist v _ _, el) = foldr makeSum (foldr makeProd' v0 el) rl
      where v0 = Func "IDR" [Var v, Con (I 1), len]

conjPYMult [al,de,len] lik = [al, de, len, foldr1 (\a b -> Func "+" [a,b]) $ map conj lik]
  where
    plusOne x = Func "+" [x, Con (I 1)]
    conj (rl, Nothing, Dist v _ _, el) = foldr makeSum (foldr makeProd' v0 el) rl
      where v0 = Func "IDR" [Var v, Con (I 1), plusOne len]

{-
conjPYMult [al,de,len] lik = [Func "+" [al0, foldr1 (\a b -> Func "+" [a,b]) $ map conj lik], de, len]
  where
    one = Con (I 1)
    zero = Con (R 0)
    plusOne x = Func "+" [x, one]
    al0 = Func "+" [ Func "vec" [Func "-" [zero, de], one, plusOne len]
                   , Func ".*" [Func "+" [al, Func "*" [de, len]]
                               ,Func "IDR" [plusOne len, one, plusOne len]]]
    conj (rl, Nothing, Dist v _ _, el) = foldr makeSum (foldr makeProd' v0 el) rl
      where v0 = Func "IDR" [Var v, Con (I 1), plusOne len]
-}

conjGamDirSym [a,b] lik = [a, b']
  where
    b' = Func "/" [one, Func "-" [Func "/" [one, b], Func "/" [one, foldr conj (Con (R 0)) lik]]]
    one   = Con (R 1)
    conj (rl, Nothing, Dist v _ [_,dim], el) d0 = 
      Func "+" [d0, foldr makeLogSum (foldr makeProd (sumlog dim v) el) rl]
    makeLogSum r e = SP False r e ""
    sumlog dim v0@(V v vl) = SP False (Range "cgds" (Con (I 1)) dim) (Func "log" [Func ".*" [norm,v1]]) ""
      where 
        norm = Func "/" [one, Func "sub" [Var (V v vl), Func "+" [dim, Con (I 1)]]]
--        norm = Func "/" [one, Var (V v (vl ++ [fromJust $ exprToSExpr dim]))]
            -- Func "/" [one, SP False (Range "cgds_norm" (Con (I 1)) dim) v1' ""]
        v1   = Var (V v (vl ++ [Id "cgds"      Nothing]))
--        v1'  = Var (V v (vl ++ [Id "cgds_norm" Nothing]))

conjGamDir idx0 [a,b] lik = [a, b']
  where
    b' = Func "/" [one, Func "-" [Func "/" [one, b], Func "/" [one, foldr conj (Con (R 0)) lik]]]
    one   = Con (R 1)
    conj (rl, Nothing, Dist v _ [_,dim], el) d0 = 
      Func "+" [d0, foldr makeLogSum (foldr makeProd (sumlog dim v) el) rl]
    makeLogSum r e = SP False r e ""
    sumlog dim v0@(V v vl) = Func "log" [Func ".*" [norm,v1]]
      where 
        norm = Func "/" [one, Func "sub" [Var (V v vl), Func "+" [dim, Con (I 1)]]]
--        norm = Func "/" [one, SP False (Range "cgds_norm" (Con (I 1)) dim) v1' ""]
        v1   = Var (V v (vl ++ idx0)) -- [Id "cgds"      Nothing]))
--        v1'  = Var (V v (vl ++ [Id "cgds_norm" Nothing]))

makeSum  r e  = SP False r e ""
makeProd  e0 e = Func  "*" [e0, e]
makeProd' e0 e = Func ".*" [e0, e]

conjGamNor isMultivar [al,be] lik = [al', be']
  where
    al' = Func "+" [al, Func "/" [n   , Con (R 2)]]
    be' = Func "+" [be, Func "/" [sumx, Con (R 2)]]

    sumx = foldr1 (\a b -> Func "+" [a,b]) $ map (makePost True ) lik
    n    = foldr1 (\a b -> Func "+" [a,b]) $ map (makePost False) lik

    one = Con (R 1)

    makePost True  (rl, Nothing, Dist v _ (mu:_), el) = foldr makeSum (foldr makeProd' (d mu $ Var v) el) rl
    makePost False (rl, Nothing, Dist v _ _     , el) = foldr makeSum (foldr makeProd  one            el) rl

    d mu e 
      | isMultivar = Func "sqrDiff" [e,mu]
      | otherwise  = Func "*" [Func "-" [e,mu], Func "-" [e,mu]]
--      | isMultivar = Func "sum" [Func "*" [Func "-" [e,mu], Func "-" [e,mu]]]
--      | otherwise  = Func "*" [Func "-" [e,mu], Func "-" [e,mu]]


{-
conjNorNor isMultivar (mu0:si0:rest) lik 
  | length all_si /= 1 = error ("Conjugacy.conjNorNor: not all likelihood variances are the same... this is fixable, but not yet implemented")
  | length all_mu /= 1 = error ("Conjugacy.conjNorNor: not all likelihood means are the same... this is fixable, but not yet implemented")
  | otherwise = (mu' : rho' : rest)
  where
    all_si = nub [si | (_,_,Dist _ _ (_:si:_),_) <- lik]
    all_mu = nub [si | (_,_,Dist _ _ (mu:_:_),_) <- lik]
    si     = head all_si

    --   = (1/si0 + n/si)^(-1); n = sum_...
    rho' = Func "^" [Func "+" [Func "/" [one, si0]
                              ,Func "*" [Func "/" [one, si], n]]
                    ,Con (R (-1))]

    times = if isMultivar then ".*" else "*"

    --   = rho' * (mu0/si0 + (1/si) sum x)
    mu'  = Func times [rho'
                      ,Func "+" [Func times [Func "/" [one, si0], mu0]
                                ,Func times [Func "/" [one, si ], sumx]]]

    sumx = foldr1 (\a b -> Func "+" [a,b]) $ map (makePost True ) lik
    n    = foldr1 (\a b -> Func "+" [a,b]) $ map (makePost False) lik

    -- helpers
    one = Con (R 1)

    makePost True  (rl, Nothing, Dist v _ _, el) = foldr makeSum (foldr makeProd' (Var v) el) rl
    makePost False (rl, Nothing, Dist v _ _, el) = foldr makeSum (foldr makeProd  one     el) rl
-}

conjNorNor isMultivar (mu0:si0:rest) lik 
  | mytrace (show ("conjNorNor", mu0, si0, rest, lik)) True
  = (mu' : rho' : rest)
  where
    --   = (1/si0 + sum_n 1/si_n)^{-1}
    rho' = Func "^" [Func "+" [Func "/" [one, si0], sum_si]
                    ,Con (R (-1))]

    times = if isMultivar then ".*" else "*"

    --   = rho' * [ mu0/si0 + sum_n (x_n/si_n) ]
    mu'  = Func times [rho' ,Func "+" [Func times [Func "/" [one, si0], mu0], sum_x]]

    sum_x  = foldr1 (\a b -> Func "+" [a,b]) $ map (makePost True ) lik
    sum_si = foldr1 (\a b -> Func "+" [a,b]) $ map (makePost False) lik

    -- helpers
    one = Con (R 1)

    makePost useX inp@(rl, newLHS, Dist oldLHS _ (_:oldsi2:_), el) = mytrace (show ("makePost", (useX,inp), (lhs,numer,val))) $ foldr makeSum (foldr makeProd' val el) rl
      where
        (lhs,si2) = case newLHS of { Just [lhs,si2] -> (lhs,if useX then si2 else oldsi2) ; _ -> (Var oldLHS,oldsi2) }
        numer = if useX then lhs else Con (R 1)
        over  = Func "/" [Con (R 1), si2]
        val   = if useX then Func times [over, numer] else over


conjGamExp [al,be] lik = [al',be']
  where
    al' = Func "+" [al, n]
    be' = Func "/" [be, Func "+" [one, Func "*" [be, sumx]]]

    sumx = foldr1 (\a b -> Func "+" [a,b]) $ map (makePost True ) lik
    n    = foldr1 (\a b -> Func "+" [a,b]) $ map (makePost False) lik

    one = Con (R 1)

    makePost True  (rl, Nothing, Dist v _ _, el) = foldr makeSum (foldr makeProd' (Var v) el) rl
    makePost False (rl, Nothing, Dist v _ _, el) = foldr makeSum (foldr makeProd  one     el) rl

conjGamPoi [al,be] lik = [al', be']
  where
    al' = Func "+" [al, sumx]
--    be' = Func "/" [be, Func "+" [one, Func "*" [be, n]]]
    be' = Func "/" [one, Func "+" [Func "/" [one, be], n]]

    sumx = foldr1 (\a b -> Func "+" [a,b]) $ map (makePost True ) lik
    n    = foldr1 (\a b -> Func "+" [a,b]) $ map (makePost False) lik

    one = Con (R 1)

    makePost True  (rl, Nothing, Dist v _ _, el) = foldr makeSum (foldr makeProd' (Var v) el) rl
    makePost False (rl, Nothing, Dist v _ _, el) = foldr makeSum (foldr makeProd  one     el) rl


conjBetBin [al,be] lik = [foldr (conj True ) al lik
                         ,foldr (conj False) be lik]
  where
    conj b (rl, Nothing, Dist v _ _, el) d0 = Func "+" [d0, foldr makeSum (foldr makeProd v0 (if not b then map notit el else el)) rl]
      where v0 = (if b then id else notit) $ Var v
    notit e = Func "-" [Con (R 1), e]

conjIGGam [a,b] lik = [a',b']
  where
    -- a' = a + alpha*n , b' = b / (1 + b * sum x_i)
    -- where n = # of data points, x_i is the ith data point (up to n)
    a' = Func "+" [a, Func "*" [n, alpha]]
    b' = Func "/" [b, Func "+" [one, Func "*" [b, sumx]]]

    alpha = case lik of { ((_, Nothing, Dist _ _ (alpha:_),_):_) -> alpha }

    one  = Con (R 1)

    sumx = foldr1 (\a b -> Func "+" [a,b]) $ map (makePost True ) lik
    n    = foldr1 (\a b -> Func "+" [a,b]) $ map (makePost False) lik

    makePost True  (rl, Nothing, Dist v _ _, el) = foldr makeSum (foldr makeProd' (Var v) el) rl
    makePost False (rl, Nothing, Dist v _ _, el) = foldr makeSum (foldr makeProd' one     el) rl


simplify :: Core -> Core
simplify (Core l) = Core [(v,applyConjugacy conjugacyRules d,r) | (v,d,r) <- l]

applyConjugacy :: [Conjugate] -> Dist -> Dist
applyConjugacy rules d 
  | null pr_lik = d
  | otherwise   = applyConjugacy rules post
  where
    pr_lik = [ (priorDist0, prior, (idx0,lik,rest))
                   | (priorDist0,priorConj) <- findPrior conjugacyRules d
                   , let prior = (stripPrior $ UnLift.unlift priorDist0, priorConj)
                   , let (idx0,lik,rest) = findLikelihood prior d
                   , mytrace (show ("prior=", fst prior, "likelihood=", idx0,lik,rest)) True
                   , not (null lik)
                   , isJust rest
             ]
    (pr0,pr,lik) = head pr_lik
    post     = computePosterior pr0 pr lik

stripPrior (Prod _ d _) = stripPrior d
stripPrior (a :^: _) = stripPrior a
stripPrior d = d

findPrior :: [Conjugate] -> Dist ->  [(Dist, Conjugate)]
findPrior rules d@(Dist _ id _) = [(d,r) | r <- rules, prior r == id]
findPrior rules (a :*: b) = findPrior rules a `mplus`  findPrior rules b
findPrior rules (a :^: e) = [(d :^: e, c) | (d,c) <- findPrior rules a]
findPrior rules (Prod r d spid) = [(Prod r d' spid, c) | (d',c) <- findPrior rules d]

findLikelihood :: (Dist, Conjugate) -> Dist -> ([SExpr], Lik, Maybe Dist) -- second is what remains
findLikelihood (Dist priorParam priorId _, conj) d@(Dist likLHS id el)

  | id == likelihood conj,
    matching conj < length el,
    Just (idx0,el') <- matchVariable (idxdelta conj) priorParam (el !! matching conj) = (idx0, [([],Nothing,d,el')], Nothing)
{-    case matchVariable (idxdelta conj) priorParam (el !! matching conj) of
      Nothing  -> ([], [], Just d)
      Just (idx0,el') -> (idx0, [([],Nothing,d,el')], Nothing) -}


-- we special case Gaussian likelihoods that match on inverted means
  | id == likelihood conj,
    priorId == "Nor", id == "Nor",
    priorParam /= likLHS,
    matching conj == 0, length el == 2, idxdelta conj == 0,
    Just (likLHS', si2') <- invertGaussian priorParam likLHS (el!!0) (el!!1) =  -- match variable will return Just ([], []) on matchVariable 0 priorParam (Var priorParam)

      mytrace (show ("findLikelihood-Nor", (priorParam, priorId), d, "likLHS", (likLHS,likLHS'), "mu", el!!0, "si2", (el!!1,si2')))

--      ([], [([], Just [likLHS',el!!1], Dist likLHS id [el!!0, si2'], [])], Nothing)
        ([], [([], Just [likLHS',el!!1], Dist (V "" []) id [el!!0,si2'], [])], Nothing)

  | otherwise = ([], [], Just d)
findLikelihood dc (a :*: b) = (idx0A++idx0B,likA++likB, restA `distTimes` restB)
  where (idx0A,likA,restA) = findLikelihood dc a
        (idx0B,likB,restB) = findLikelihood dc b
findLikelihood dc (a :^: e) = (idx0, map (\ (r,me,d,el) -> (r,me,d,e:el)) lik, liftM (:^:e) rest)
  where (idx0,lik,rest) = findLikelihood dc a
findLikelihood dc (Prod range d spid) = (idx0, map (\ (r,me,d,el) -> (range:r,me,d,el)) lik, liftM (\d -> Prod range d spid) rest)
  where (idx0,lik,rest) = findLikelihood dc d

matchVariable 0 v e | Var v == e = Just ([], [])
matchVariable delta (V pid pse) (Var (V eid ese))
  | pid == eid && length pse == length ese + delta 
 && drop delta pse == ese
  = Just (take delta pse, zipWith (\p e -> Func "=" [sexprToExpr p,sexprToExpr e]) (drop delta pse) ese)
matchVariable delta v (Case cv cs) 
  | length csInd == 1                              = Just (vidx0, (Func "=" [cv, fst (cs !! head csInd)]) : el')
--  | length csInd >  1                              = Just (vidx0, mkOr $ map (\nn -> let Just (_,el') = csMatch !! nn
--                                                                                     in  (Func "=" [Var cv, fst (cs !! nn)]) : el') csInd)
  where
    csMatch = map (matchVariable delta v . snd) cs
    -- we (temporarily) have to make sure that only one of the options matches
    csInd   = findIndices isJust csMatch
    -- look at the results of that one match
    Just (vidx0,el') = csMatch !! (head csInd)
    -- helper functions
    mkOr = foldr1 (\a b -> Func "||" [a,b])

{-
matchVariable True delta v (Fun "+" [a,b])
  | isNothing bVar, Just (idx0,el') <- aVar
  where
    aVar = matchVariable True delta v a
    bVar = matchVariable True delta v b
-}

matchVariable _ _ _ = Nothing

{-
matchVariable v e | Var v == e = Just []
matchVariable (V pid pse) (Var (V eid ese))
  | pid == eid && length pse == length ese = Just (zipWith (\p e -> Func "=" [sexprToExpr p,sexprToExpr e]) pse ese)
matchVariable _ _ = Nothing
-}

computePosterior :: Dist -> (Dist, Conjugate) -> ([SExpr], Lik, Maybe Dist) -> Dist
computePosterior _ _ (_,_,Nothing) = error ("Conjugacy.computePosterior: Maybe Dist is Nothing; at least the prior should be there")
computePosterior prior0 (prior@(Dist id0 _ el0), conj) (idx0, lik, Just rest) 
--  | mytrace (show ("computePosterior", prior0, prior, idx0, lik, Just rest)) True
  = fromJust ((rest `distWithout` prior0) `distTimes` Just (Dist id0 (posterior conj) ((suffstats conj) idx0 el0 lik)))


-- invertGaussian is used for things like Nor(y | w*x+b, si^2), where we
-- need to convert this into Nor((y-b)/x | w, si^2/x^2) so that conjugacy
-- can be applied.  invertGaussian takes the variable we wish to isolate,
-- the variable on the LHS, the expression for the mean and the expression
-- for the variance and (maybe) returns the new LHS and variance (the
-- assumption is that the new mean will be the desired mean).  thus,
-- in the above example:
--    invertGaussian w y w*x+b si2 --> Just ((y-b)/x, si2/x^2)
invertGaussian :: Var -> Var -> Expr -> Expr -> Maybe (Expr, Expr)
invertGaussian var0 lhs mu si2
  | Just (m,a) <- findMultAdd var0 mu,
    let m' = simplifyExprMany m,
    let a' = simplifyExprMany a,
    not (isZero m')
    = mytrace (show ("invertGaussian", (var0,lhs,mu,si2), (m,a), (m',a')))
              Just (Func "/" [Func "-" [Var lhs,a'], m'], Func "/" [si2,m']) -- Func "*" [m',m']])
  | otherwise                         = Nothing


-- for invertGaussian, we want to take an arbitrary Expr and a variable
-- that occurs in that Expr, and return a multiplicative and additive
-- term.  so findMultAdd var expr --> (m,a) means that expr is equivalent
-- to m*var+a
findMultAdd var0 (Var v)
  | var0 == v = Just (Con (R 1), Con (R 0))
  | otherwise = Just (Con (R 0), Var v)
findMultAdd var0 (Con c) = Just (Con (R 0), Con c)
findMultAdd var0 (Func "+" [e1,e2])
  | Just (m1,a1) <- findMultAdd var0 e1
  , Just (m2,a2) <- findMultAdd var0 e2 = Just (Func "+" [m1,m2], Func "+" [a1,a2])
  | otherwise                           = Nothing
findMultAdd var0 (Func "-" [e1,e2])
  | Just (m1,a1) <- findMultAdd var0 e1
  , Just (m2,a2) <- findMultAdd var0 e2 = Just (Func "-" [m1,m2], Func "-" [a1,a2])
  | otherwise                           = Nothing
findMultAdd var0 (Func "*" [e1,e2])  -- only works if m1 or m2 is zero
  | Just (m1,a1) <- findMultAdd var0 e1
  , Just (m2,a2) <- findMultAdd var0 e2
  , m1 == Con (R 0)                     = Just (Func "*" [a1,m2], Func "*" [a1,a2])
  | Just (m1,a1) <- findMultAdd var0 e1
  , Just (m2,a2) <- findMultAdd var0 e2
  , m2 == Con (R 0)                     = Just (Func "*" [a2,m1], Func "*" [a1,a2])
  | otherwise                           = Nothing
findMultAdd var0 (Func "/" [e1,e2])  -- only works if m2 is zero
  | Just (m1,a1) <- findMultAdd var0 e1
  , Just (m2,a2) <- findMultAdd var0 e2
  , m2 == Con (R 0)                     = Just (Func "/" [m1,a2], Func "/" [a1,a2])
  | otherwise                           = Nothing
findMultAdd var0 (SP False r e spid)
  | Just (m,a) <- findMultAdd var0 e    = Just (SP False r m (spid ++ "_m"), SP False r a (spid ++ "_m"))
findMultAdd _ _ = Nothing


-- let Just (m,a) = findMultAdd (V "w" []) (Func "+" [Func "*" [Var (V "x" []), Var (V "w" [])], Var (V "b" [])])
-- let Just (m,a) = findMultAdd (V "w" [Id "d" Nothing]) (Func "+" [Var (V "b" []), SP False (Range "d" (Con (I 1)) (Var (V "D" []))) (Func "*" [Var (V "x" [Id "d" Nothing]), Var (V "w" [Id "d" Nothing])]) "spid"])
-- (simplifyExprMany m, simplifyExprMany a)

-- if w ~ Nor(mu,si2)
--    y ~ Nor(w*x,rho2)

-- then

-- p(y|w,x,rho2) 
--   = (2 pi rho2)^{-1/2} exp[ - 1/(2 rho2) (w*x - y)^2 ]
--   = (2 pi rho2)^{-1/2} exp[ - 1/(2 rho2) (w*x - x*y/x)^2 ]
--   = (2 pi rho2)^{-1/2} exp[ - 1/(2 rho2) x^2 (w - y/x)^2 ]
--   = (2 pi rho2)^{-1/2} exp[ - 1/(2 (rho2/x^2)) (w - y/x)^2 ]
