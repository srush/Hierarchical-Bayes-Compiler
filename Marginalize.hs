----------------------------------------------------------------------------
-- |
-- Module      :  Marginalize
-- Project     :  HBC
-- Copyright   :  (c) Hal Daume III
-- License     :  Open
-- 
-- Maintainer  :  Hal Daume III <me@hal3.name>
-- Stability   :  stable
-- Portability :  portable
--
-- Implements marginalization (aka collapsing, ala Rao-Blackwellization)
--
-----------------------------------------------------------------------------

module Marginalize where

import Core
import Type

import Data.List
import Data.Maybe
import Control.Monad
import qualified Data.Map as M
import Util

data Update = Update { indexVariable :: Id
                     , isIncr        :: Bool -- if false, then it's an assn
                     , numVars       :: Int
                     , variableRem   :: [SExpr] -> ([Range], Expr, Expr)   -- (loop vars, update variable, incr/assn expression)
                     , variableAdd   :: [SExpr] -> ([Range], Expr, Expr)   -- initially the update variable is a var, but in the process of simplification, we might end up with a "sub"
                     } 

marginalizeAll :: Core -> TypeMap -> [Id] -> (TypeMap, Core, [Id], [Update], [String])
marginalizeAll core0 tm0 coll =
  foldr (\id (tm,core,ids,upd,warn) ->
             case findMarginalizeType core id of
               Nothing -> (tm,core,ids,upd,("cannot figure out how to marginalize " ++ id):warn)
               Just f  ->
                 let (tm', id', core', upd') = f tm id core
                 in  (tm', core', id':ids, upd ++ upd', warn)
        ) (tm0,core0,[],[],[]) coll

findMarginalizeType (Core decls) var =
  case find ((==var).varId.fst3) decls of
    Just (_, Dist _ "Dir" _, _) -> Just marginalizeDirichlet
    Just (_, Dist _ "DirSym" _, _) -> Just marginalizeDirichlet
    _ -> Nothing

-- marginalizeDirichlet v conj -> v', conj', update
--   v is the dirichlet-distributed variable whose dependents are
--   only ever multinomials, conj is the result of determinging
--   conjugacy.  we return a new variable name ("post_v")
--   which will need to be initialized, and a new core definition.
--   the new core differs from the original in the following ways:
--     1) the distribution over v has been removed
--     2) a definitional-distribution over post_v has been added
--     3) all references to v have been replaced by appropriate
--          references to post_v
--   finally, we also return a list of updates.  each update is
--   indexed by a variable that may change and, in doing so, will
--   affect the value of post_v.  each such update comes
--   with two functions: varRem and varAdd.  the first updates
--   post_v so that it *doesn't* depend on a the variable in
--   question; the second updates so that it *does* depend on the
--   variable in question.  these take as argument the sexprs to
--   the index variable.

marginalizeDirichlet :: TypeMap -> Id -> Core -> (TypeMap, Id, Core, [Update])
marginalizeDirichlet tm var core@(Core decls) 
  | mytrace (show (("var=",var),("prior=",prior),("remainder=",remainder),("varIdx=",varIdx),("updateVars=",updateVars),("rangeList=",rangeList),("innerExpr=",innerExpr),("ieGlobals=",map (getExprGlobals []) innerExpr),("priorRange=",priorRange),("updates=",updates),("nonPrior=",nonPrior)) ++ "\n\n") True
  = (tm', var', Core decls', updates)
  where
    globals = nub $ map (varId.fst3) decls

    varType@(Type _ typeIdx) = fromJust (M.lookup var tm)
    tm' = M.insert var' varType $ M.delete var tm

    var' = "post_" ++ var

    ([prior], nonPrior) = partition ((==var).varId.fst3) decls

    (variableDefinition, priorVal, varIdx, remainder, priorRange) = 
      case prior of
        (V _ se, Dist _ "Dir" ((Func "+" [pv,rem]):el), rl) -> ((V var' se, Dist (V var' se) "Delta" (rem:el), rl), pv, se, rem, rl)

    decls'  = variableDefinition : map (removeVariable var (length varIdx) newE) nonPrior

    newE el0 sl =
      case priorVal of
        Func "vec" ((v@(Var _)):_) -> {- makeSubE el0 $ -} Func ".+" [v, Var (V var' sl')]
        Func "vec" ((c@(Con _)):_) -> {- makeSubE el0 $ -} Func ".+" [c, Var (V var' sl')]
--        e -> error $ "don't know how to deal with prior " ++ show priorVal ++ " in " ++ show prior ++ " with sl=" ++ show (sl) ++ " and varIdx=" ++ show varIdx ++ " and lookupTable=" ++ show lookupTable ++ " and el0=" ++ show el0 ++ "; e' = " ++ show (makeSubSE e' sl)
        e -> Func "+" [makeSubSE e' sl, Var (V var' sl')]
          where 
            e' = replaceVars lookupTable e
            lookupTable = zip (map sexprToExpr varIdx) (take (length varIdx-length sl) el0
                                                        ++ map sexprToExpr sl)
      where sl' = map (fromJust.exprToSExpr) el0 ++ sl

    makeSubE [] e     = e
    makeSubE (s:sl) e = makeSubE sl (Func "sub" [e,s])

    makeSubSE e sl = makeSubE (map sexprToExpr sl) e

    -- find inner-most expression and associated ranges
    (rangeList, innerExpr) = unzip $ traceInsideSums [] remainder

    -- the update var is anything that lives inside "innerExpr"
    updateVars = globals `intersect` concatMap (getExprGlobals (map rangeIds $ concat rangeList)) innerExpr
    updates    = map mkUpdate updateVars

    mkUpdate id = mytrace (show (("id=",id),("idElem=",idElem),("occ=",occ),("unqualOcc=",unqualOcc),("equalOcc",equalOcc)) ++ "\n\n") $
      case occ of
--        [V _ sl] -> Update id True (length sl) (mkStatement True sl) (mkStatement False sl)
        [el] -> Update id True (length el) (mkStatement True idElem unqualOcc equalOcc el) (mkStatement False idElem unqualOcc equalOcc el)
        res  -> error ("Marginalize.marginalizeDirichlet.mkUpdate: non-matching occurances of '" ++ id ++ "' found in " ++ show remainder ++ "; findOcc returned " ++ show res)
      where
        occ = nub $ findIdOcc id remainder
        idElem    = map (\z -> id `elem` (getExprGlobals [] z)) innerExpr
        unqualOcc = reverse $ nub [r     | (oneRangeList, oneInnerExpr, True) <- zip3 rangeList innerExpr idElem
                               , r@(Range id _ _) <- oneRangeList
                               , not (id `elem` mapMaybe exprId (head occ))]
        equalOcc  = nub [(e,n) | (e,n) <- zip (head occ) [0..]
                               , case exprId e of
                                   Nothing -> True
                                   Just  v -> False] -- not (v `elem` map rangeIds rangeList)]

    lu l x = case lookup x l' of { Nothing -> x ; Just y -> y }
      where l' = map (\ (Id v _, Id v' _) -> (v,v')) l

    mkStatement isRem idElem unqualOcc equalOcc (el0 :: [Expr]) sl = (unqualLoops ++ map mkLoop loopVar, Var v0, addRem exprEq)
      where 
        loopVar = mapMaybe (\ (v,t) -> 
                                case unqualifiedSE (mapMaybe exprId el0) v of 
                                  Nothing -> Nothing 
                                  Just e -> Just (t,e) 
                           ) (zip varIdx typeIdx)
        unqualLoops = map (replaceVarsR $ map (\ (a,b) -> (a, sexprToExpr b)) curVars) unqualOcc
        equalExprs  = [Func "=" [replaceVarsSL (curVars0 ++ take n (zip el0 sl)) e, sexprToExpr (sl !! n)] | (e,n) <- equalOcc]
        _N = length el0
        curVars0 = map (\ (_,v) -> (Var (V v []), Id v Nothing)) loopVar
        curVars  = curVars0 ++ zip el0 sl
        v0 = V var' (map (renameBy curVars) varIdx)  -- varIdx -- (take (length varIdx) sl)
        mkLoop (Range _ lo hi, id) = Range id lo hi
        addRem e = if isRem then Func ".-" [Con (R 0), e] else e
        
        expr0  = foldr1 (\a b -> Func "+" [a,b]) $ mapMaybe (\ (a,b) -> if b then Just (replaceVarsSL curVars a) else Nothing) (zip innerExpr idElem)
        exprEq = foldr (\eq e -> Func ".*" [eq, e]) expr0  equalExprs
--        loopEq = foldr (\ (r,n)  e -> SP False r e ("marg_loop_" ++ show n))  exprEq (zip unqualLoops [1..])

    traceInsideSums acc (SP False r@(Range v0 lo hi) e _) = traceInsideSums (r:acc) e
    traceInsideSums acc (Func "+" [a,b]) = traceInsideSums acc a ++ traceInsideSums acc b
    traceInsideSums acc e = [(acc, e)]

    renameBy lu id@(Id v Nothing) =
      case lookup (Var (V v [])) lu of
        Nothing -> error ("Marginalize.renameBy: cannot find " ++ show id ++ " in " ++ show lu)
        Just  y -> y

    replaceVarsSL lu = replaceVars (map (\ (a,b) -> (a, sexprToExpr b)) lu)

    replaceVars lu e | e `elem` map fst lu = fromJust $ lookup e lu
    replaceVars lu v@(Var (V id [])) = v -- error ("Marginalize.replaceVars: variable not found: " ++ id ++ " in " ++ show lu)
    replaceVars lu (Var (V id sl))
      | all isJust sl'' = Var (V id (map fromJust sl''))
      | otherwise       = Func "sub" ((Var (V id [])):sl')
      where
        sl'  = map (replaceVars lu . sexprToExpr) sl
        sl'' = map exprToSExpr sl'
    replaceVars lu (Con c) = Con c
    replaceVars lu (Func f el) = Func f (map (replaceVars lu) el)
    replaceVars lu (SP b r e i) = SP b (replaceVarsR lu r) (replaceVars lu e) i

    replaceVarsR lu (Range i lo hi) = Range i (replaceVars lu lo) (replaceVars lu hi)

{-

    renameBy l x =
      case lookup x l of
        Nothing -> error ("Marginalize.renameBy: cannot find " ++ show x ++ " in " ++ show l)
        Just y  -> y

    replaceVars lu (Var (V id se)) = Var (V (lu id) (map (replaceVarsSE lu) se))
    replaceVars lu (Con c) = Con c
    replaceVars lu (Func f el) = Func f (map (replaceVars lu) el)
    replaceVars lu (SP b r e i) = SP b (replaceVarsR lu r) (replaceVars lu e) i
    replaceVarsSE lu (Id i c) = Id (lu i) c
    replaceVarsSE lu (Cn c) = Cn c
    replaceVarsR lu (Range i lo hi) = Range i (replaceVars lu lo) (replaceVars lu hi)
-}



containsVariable d v = v `elem` getDeclGlobals d

-- removeVariable assumes the variable in question never appears on the lhs nor in a range
removeVariable :: Id -> Int -> ([Expr] -> [SExpr] -> Expr) -> Decl -> Decl
removeVariable id0 idLen newE (var, dist, rl) = (var, removeVariableD {- [] -} id0 idLen newE dist, rl)

removeVariableD {- curEL -} id0 idLen newE (Dist var id el) = Dist var id (map (removeVariableE {- curEL -} id0 idLen newE) el)
removeVariableD {- curEL -} id0 idLen newE (a :*: b) = removeVariableD {- curEL -} id0 idLen newE a :*: removeVariableD {- curEL -} id0 idLen newE b
removeVariableD {- curEL -} id0 idLen newE (a :^: e) = removeVariableD {- curEL -} id0 idLen newE a :^: removeVariableE {- curEL -} id0 idLen newE e
removeVariableD {- curEL -} id0 idLen newE (Prod r d id') = Prod r (removeVariableD {- curEL -} id0 idLen newE d) id'

removeVariableE {- curEL -} id0 idLen newE e0@(Var (V id sl))
  | id == id0 && length sl >= idLen = newE (take idLen $ map sexprToExpr sl') (drop idLen sl')
  | id == id0 = error $ "Marginalize.removeVariableE: cannot remove occurance of variable " ++ id0 ++ " in expression " ++ show e0 ++ " because I couldn't find the right number of subscripts; expecting " ++ show idLen
  | otherwise = Var (V id sl')
  where sl' = map (removeVariableSE {- curEL -} id0 idLen newE) sl
{-
removeVariableE {- curEL -} id0 idLen newE (Func "sub" [e0,sub]) = Func "sub" [e0', sub']
  where
    sub' = removeVariableE [] id0 idLen newE sub
    e0'  = removeVariableE ([sub] ++ curEL) id0 idLen newE e0 
-}
-- sub( sub(X,1) , 2 ) --> X_{1,2}
removeVariableE {- curEL -} id0 idLen newE (Func id el) = Func id (map (removeVariableE {- curEL -} id0 idLen newE) el)
removeVariableE {- curEL -} id0 idLen newE (SP b r e i) = SP b r (removeVariableE {- curEL -} id0 idLen newE e) i
removeVariableE             id0 idLen newE (Case v cases) = Case v (map (\ (a,b) -> (removeVariableE id0 idLen newE a,removeVariableE id0 idLen newE b)) cases)
removeVariableE {- curEL -} id0 idLen newE e0 = e0

removeVariableSE {- curEL -} id0 idLen newE se@(Id id c)
  | id == id0 = error ("Marginalize.removeVariableSE: found id " ++ show id0 ++ "in SExpr " ++ show se)
removeVariableSE {- curEL -} id0 idLen newE se = se

unqualifiedSE qual (Id i Nothing) | not (i `elem` qual) = Just i
unqualifiedSE qual (Id i c) | not (i `elem` qual) = error ("Marginalize.unqualifiedSE: qualified sexpr")
unqualifiedSE qual _ = Nothing

instance Show Update where
  showsPrec i (Update id isIncr numVars rem add) = 
    showString "Update { id=" . showString id . 
    showString ", isIncr=" . shows isIncr . 
    showString ", numVars=" . shows numVars . 
    showString ", rem=" . showsPrec i (rem [Id ("var_" ++ show i) Nothing | i <- [1..numVars]]) . 
    showString ", add=" . showsPrec i (add [Id ("var_" ++ show i) Nothing | i <- [1..numVars]]) . 
    showString " }"

