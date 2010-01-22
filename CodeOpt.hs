----------------------------------------------------------------------------
-- |
-- Module      :  CodeOpt
-- Project     :  HBC
-- Copyright   :  (c) Hal Daume III
-- License     :  Open
-- 
-- Maintainer  :  Hal Daume III <me@hal3.name>
-- Stability   :  stable
-- Portability :  portable
--
-- Perform simple code optimizations
--
-----------------------------------------------------------------------------

module CodeOpt where

import Type
import Core(Const(..))
import qualified Core as C
import qualified Data.Map as M
import Data.Maybe
import Data.Char
import Data.List
import Debug.Trace 
import Control.Monad
import Control.Monad.State
import Util
import Code
import Data.Generics hiding ((:*:))
import Data.Typeable
import Data.Generics.Basics
import Data.Generics.Schemes


opt :: Code -> Code
opt code 
  | code' == code = code
  | otherwise     = opt code'
  where code' = 
            removeSub .
            map removeDanglingVecVars .
            removeSub .
            flatten . everywhere (mkT removeUnnecessaryVecVars) .
--            flatten . everywhere (mkT liftLoop) .
            flatten . everywhere (mkT smooth_Mult) .
            flatten . everywhere (mkT lift_Mult_case) .
            flatten . everywhere (mkT smooth_Mult_call) .
            flatten . everywhere (mkT lift_Mult_call) .
            everywhere (mkT removeIdLoop) $
--            everywhere (mkT orderMath   ) .
--            everywhere (mkT simplifyMath) $
            code
        flatten = map (\f -> f { body = flattenSeqs $ body f })

-- we're often left with things like:
--    For i = ... do
--      x_{..., i, ...} += v * [i=q]
-- (or where we have assignment instead of increment)
--
-- we want to replace these with
--    x_{..., q, ...} += v
removeIdLoop :: Statement -> Statement
removeIdLoop s@(Loop idx _ _ [Assn (V var sub) e]) =
  case (findIndices (==(Var (V idx []))) sub, extractEquality idx e) of
    ([subIdx], (Just id,Just enew)) -> Assn (V var (replaceNth sub subIdx id)) enew
    _ -> s
removeIdLoop s@(Loop idx _ _ [Incr (V var sub) e]) =
  case (findIndices (==(Var (V idx []))) sub, extractEquality idx e) of
    ([subIdx], (Just id,Just enew)) -> Incr (V var (replaceNth sub subIdx id)) enew
    _ -> s
removeIdLoop s = s

-- orderMath assembles expressions on the "proper" side to be simplified
orderMath (Fun f0 [Fun f1 [a,b], c])
  | isOp f0 && f0 == f1 = (Fun f0 [Fun f1 [a',b'], c'])
  where 
    isOp x = x `elem` ["+","-","*","/"]  -- ".+",".-",".*","./",can't because vecs have to be on LHS
    [a',b',c'] = sort [a,b,c]
orderMath (Fun f0 [a, Fun f1 [b,c]])
  | isOp f0 && f0 == f1 = (Fun f0 [Fun f1 [a',b'], c'])
  where 
    isOp x = x `elem` ["+","-","*","/"] -- ".+",".-",".*","./",
    [a',b',c'] = sort [a,b,c]
orderMath e = e

-- simplifyMath removes multiplication by 1, exponentiation by 1 and zero, and addition of zero
simplifyMath (Fun  "*" [Con (C.I 1),e]) = e
simplifyMath (Fun ".*" [Con (C.I 1),e]) = e
simplifyMath (Fun  "*" [e,Con (C.I 1)]) = e
simplifyMath (Fun ".*" [e,Con (C.I 1)]) = e
simplifyMath (Fun  "*" [Con (C.R 1),e]) = e
simplifyMath (Fun ".*" [Con (C.R 1),e]) = e
simplifyMath (Fun  "*" [e,Con (C.R 1)]) = e
simplifyMath (Fun ".*" [e,Con (C.R 1)]) = e

simplifyMath (Fun  "^" [e,Con (C.I 1)]) = e
simplifyMath (Fun ".^" [e,Con (C.I 1)]) = e
simplifyMath (Fun  "^" [e,Con (C.R 1)]) = e
simplifyMath (Fun ".^" [e,Con (C.R 1)]) = e

simplifyMath (Fun  "+" [Con (C.I 0),e]) = e
simplifyMath (Fun ".+" [Con (C.I 0),e]) = e
simplifyMath (Fun  "+" [e,Con (C.I 0)]) = e
simplifyMath (Fun ".+" [e,Con (C.I 0)]) = e
simplifyMath (Fun  "+" [Con (C.R 0),e]) = e
simplifyMath (Fun ".+" [Con (C.R 0),e]) = e
simplifyMath (Fun  "+" [e,Con (C.R 0)]) = e
simplifyMath (Fun ".+" [e,Con (C.R 0)]) = e

simplifyMath (Fun  "-" [e,Con (C.I 0)]) = e
simplifyMath (Fun ".-" [e,Con (C.I 0)]) = e
simplifyMath (Fun  "-" [e,Con (C.R 0)]) = e
simplifyMath (Fun ".-" [e,Con (C.R 0)]) = e

simplifyMath (Fun  "+" [Con c, Con d])  = Con (c + d)
simplifyMath (Fun ".+" [Con c, Con d])  = Con (c + d)
simplifyMath (Fun  "-" [Con c, Con d])  = Con (c - d)
simplifyMath (Fun ".-" [Con c, Con d])  = Con (c - d)
simplifyMath (Fun  "*" [Con c, Con d])  = Con (c * d)
simplifyMath (Fun ".*" [Con c, Con d])  = Con (c * d)
simplifyMath (Fun  "/" [Con c, Con d])  = Con (c / d)
simplifyMath (Fun "./" [Con c, Con d])  = Con (c / d)
simplifyMath (Fun  "^" [Con c, Con d])  = Con (c ** d)
simplifyMath (Fun ".^" [Con c, Con d])  = Con (c ** d)

simplifyMath e = e

-- extractEquality idx e returns (id,enew) if the only occurance of
-- idx in e is in a product with an equality.  id is the thing it is
-- in equality to, enew is the entire expression with the equality
-- replaced by "1"
extractEquality idx e@(Var (V id sl)) | id == idx = (Nothing,Nothing)
                                      | otherwise = (Nothing,Just e)
extractEquality idx e@(Con _) = (Nothing, Just e)
extractEquality idx e@(Fun "=" [Var (V id []), eq])
  | id == idx = case extractEquality idx eq of
                  (Nothing, Just eq') -> (Just eq', Just (Con (C.R 1)))
                  _ -> (Nothing, Just e)
extractEquality idx e@(Fun fn [a,b])
  | fn `elem` ["+","-","*","/",".+",".-",".*","./"] =
  case (extractEquality idx a, extractEquality idx b) of
    ((Nothing,Just a'), (Nothing,Just b')) -> (Nothing, Just (Fun fn [a',b']))
    ((Just id,Just a'), (Nothing,Just b')) -> (Just id, Just (Fun fn [a',b']))
    ((Nothing,Just a'), (Just id,Just b')) -> (Just id, Just (Fun fn [a',b']))

    ((Nothing,Just _ ), (Nothing,Nothing)) -> (Nothing, Just e)
    ((Nothing,Nothing), (Nothing,Just _ )) -> (Nothing, Just e)

    ((Just id,Just a'), (Nothing,Nothing)) -> (Just id, Just (Fun fn [a',b ]))
    ((Nothing,Nothing), (Just id,Just b')) -> (Just id, Just (Fun fn [a ,b']))

    _ -> (Nothing,Nothing)
extractEquality idx _ = (Nothing,Nothing)


-- liftLoop takes loops up to the highest level possible.  what it
-- actually does is just lift one level, since we know that it will
-- get applied until it can't be applied any more.  we look for things
-- like:
--
--   Loop i ilo ihi [ ... ; z := Z0 ; Loop j jlo jhi [z := incr] ; ...]
--
-- where "incr" and "Z0" don't depend on i.  we replace this with:
--
--   z := Z0
--   Loop j jlo jhi [z := incr]
--   Loop i ilo ihi [... ; ...]
-- 
-- we assume everything has been flattened
liftLoop (Loop i ilo ihi ibody)
  | Just (assn, loop, rest) <- findSimpleAssign [i] ibody = assn `Seq` loop `Seq` Loop i ilo ihi rest
  where
    -- "deps" are things we're *not* allowed to depend on
    findSimpleAssign deps [] = Nothing
    findSimpleAssign deps ((assn@(Assn z z0)):(loop@(Loop j jlo jhi [Incr z' incr])):rest) 
      | z == z' && not (any (`varDependsOn` deps) (codeIdsV z ++ codeIdsE z0 ++ codeIdsE jlo ++ codeIdsE jhi ++ codeIdsE incr))
          = Just (assn, loop, rest)
    findSimpleAssign deps (s:ss) =
      case findSimpleAssign deps' ss of
        Nothing -> Nothing
        Just (assn, loop, rest) -> Just (assn, loop, s:rest)
      where
        deps' = case s of
                  Assn v0@(V id _) e0 | any (`varDependsOn` deps) (codeIdsV v0 ++ codeIdsE e0) -> id:deps
                  Incr v0@(V id _) e0 | any (`varDependsOn` deps) (codeIdsV v0 ++ codeIdsE e0) -> id:deps
                  _ -> deps
    varDependsOn v deps = v `elem` deps

liftLoop s = s



-- flattenSeqs removes all Seqs
flattenSeqs [] = []
flattenSeqs ((Loop i lo hi b):xs) = (Loop i lo hi (flattenSeqs b)) : flattenSeqs xs
flattenSeqs ((If c t e):xs) = (If c (flattenSeqs t) (flattenSeqs e)) : flattenSeqs xs
flattenSeqs ((a `Seq` b):xs) = flattenSeqs (a:b:xs)
flattenSeqs (x:xs) = x : flattenSeqs xs


-- if we have something of the form 
--   f0(res0, f1(res1, ...), ...)
-- where f0 and f1 are both vector ops, then we can replace all res1 with res0
-- similar things happen when f1 is in the second optition
removeUnnecessaryVecVars (Fun f0 [res0, Fun f1 (res1:rest1), b0, lo0, hi0]) | isVecFn f0 && isVecFn f1 = Fun f0 [res0, Fun f1 (res0:rest1), b0, lo0, hi0]
removeUnnecessaryVecVars (Fun f0 [res0, a0, Fun f1 (res1:rest1), lo0, hi0]) | isVecFn f0 && isVecFn f1 = Fun f0 [res0, a0, Fun f1 (res0:rest1), lo0, hi0]
removeUnnecessaryVecVars (Fun f0 [res0, Fun f1 (res1:rest1), lo0, hi0])     | isVecFn f0 && isVecFn f1 = Fun f0 [res0, Fun f1 (res0:rest1), lo0, hi0]
removeUnnecessaryVecVars e = e

isVecFn "vec" = True
isVecFn "ID"  = True
isVecFn "IDR" = True
isVecFn f     = isJust $ parseVecFunc f

removeDanglingVecVars f 
  | mytrace ("removeDanglingVecVars: " ++ show (tempVars f, used)) True
  = f { tempVars = [(v,t) | (v,t) <- tempVars f, v `elem` used] }
  where used = codeIdsF f -- rhsIdsF f
{-
-- we want to be able to replace the various add/sub/etc vector
-- operations with direct computations.  combined with removeSub this
-- will not only allow us to not use as many calls to those external
-- functions (eventual goal: remove all of them!), but will enable us
-- to use significantly fewer local (vector) variables.
expandVectorFunctions :: Function -> Function
expandVectorFunctions f = f { body = body'
                            , tempVars = tempVars f ++ newTemps }
  where
    body' = everywhere (mkT expandStatement) (body f)
    newTemps = nub [(id,tInt) | id <- concatMap codeIdsS body', "loop_" `isPrefixOf` id]

expandStatement :: Statement -> Statement
expandStatement (Assn v e) | Just (e', stmts) <- expandExpr e = foldr Seq (Assn v e') stmts
expandStatement (Incr v e) | Just (e', stmts) <- expandExpr e = foldr Seq (Incr v e') stmts
expandStatement (Call f r a) = foldr Seq (Call f r a') (concat stmts)
  where
    (a', stmts) = unzip $ zipWith replaceArg a $ map expandExpr a

    replaceArg a Nothing        = (a , [])
    replaceArg a (Just (a',st)) = (a', st)
expandStatement s = s

expandExpr :: Expr -> Maybe (Expr, [Statement])
--expandExpr e0 | mytrace ("expandExpr0" ++ show e0 ++ "\n") False = undefined
-- the first is the important case
expandExpr e0@(Fun f [Var res,a,b,lo,hi]) 
  | Just ff <- parseVecFunc f
  , mytrace (show ("expandExpr",e0,ff)) True
    = Just (Var res, [makeExpandLoop ff res a b lo hi])
-- the remainder are just for recursion
expandExpr (Var v) = Nothing
expandExpr (Con c) = Nothing
expandExpr (Fun f el) 
  | all isNothing el_s = Nothing
  | otherwise          = Just (Fun f el', s)
  where
    el_s = map expandExpr el
    el'  = zipWith (flip maybe fst) el el_s
    s    = concatMap snd $ mapMaybe id el_s
expandExpr (CaseOf v cases)
  | all isNothing el_s = Nothing
  | otherwise          = Just (CaseOf v cases', s)
  where
    el   = map snd cases
    el_s = map expandExpr el
    el'  = zipWith (flip maybe fst) el el_s
    s    = concatMap snd $ mapMaybe id el_s
    cases' = zip (map fst cases) el'


makeExpandLoop (op, isConst, typ, numDim) (V res resSL) a b lo hi
  | numDim == 1 = Loop v lo hi [Assn res' (Fun op [a',b'])]
  | otherwise   = Loop v lo hi [Assn res' (Fun op [Var res',a',b',lo,hi])]
  where
    a' = if isConst then a else Fun "sub" [a,Var (V v [])]
    b' =                        Fun "sub" [b,Var (V v [])]

    v  = "loop_" ++ res ++ "_" ++ show (length resSL)
    res' = V res (resSL ++ [Var (V v [])])

-}

smooth_Mult (Fun "ldf_Mult"    [norm, x, Fun "add_const_r_1" [_, eta, theta, _, _], lo, hi]) = Fun "ldf_Mult_smooth"    [norm, eta, x, theta, lo, hi]
--smooth_Mult (Fun "sample_Mult" [         Fun "add_const_r_1" [_, eta, theta, _, _], lo, hi]) = Fun "sample_Mult_smooth" [      eta,    theta, lo, hi]
smooth_Mult f = f

lift_Mult_case (Fun "ldf_Mult"    [norm, x, CaseOf cv cases, lo, hi]) = CaseOf cv [(a, Fun "ldf_Mult"    [norm, x, b, lo, hi]) | (a,b) <- cases]
--lift_Mult_case (Fun "sample_Mult" [         CaseOf cv cases, lo, hi]) = CaseOf cv [(a, Fun "sample_Mult" [         b, lo, hi]) | (a,b) <- cases]
lift_Mult_case f = f

smooth_Mult_call (Call "sample_Mult" ret [Fun "add_const_r_1" [_, eta, theta, _, _], lo, hi]) = Call "sample_Mult_smooth" ret [eta, theta, lo, hi]
smooth_Mult_call c = c

lift_Mult_call (Call "sample_Mult" ret [CaseOf cv cases, lo, hi]) = makeIf cases
  where
    makeIf []         = Comment "cases exhausted"
    makeIf ((a,b):cs) = If (Fun "=" [cv,a]) [Call "sample_Mult" ret [b, lo, hi]] [makeIf cs]
lift_Mult_call s = s

parseVecFunc :: String -> Maybe (String, Bool, Char, Int)
parseVecFunc s
  | [op,vc,t,"1"] <- linesOn '_' s
  , Just op' <- readOp op
  , vc == "vec" || vc == "const"
  , t  == "i"   || t  == "r"     = Just ([op'], vc=="const", head t, 1)

  | [op,vc,t,num] <- linesOn '_' s
  , Just op' <- readOp op
  , vc == "vec" || vc == "const"
  , t  == "i"   || t  == "r"
  , all isDigit num              = Just (op ++ "_" ++ vc ++ "_" ++ t ++ "_" ++ show (read num-1)
                                        , vc=="const", head t, read num)
  where
    readOp "add"  = Just '+'
    readOp "sub"  = Just '-'
    readOp "mult" = Just '*'
    readOp "div"  = Just '/'
    readOp _      = Nothing
parseVecFunc s                   = Nothing

