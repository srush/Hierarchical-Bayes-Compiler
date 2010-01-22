-----------------------------------------------------------------------------
-- |
-- Module      :  Type
-- Project     :  HBC
-- Copyright   :  (c) Hal Daume III
-- License     :  Open
-- 
-- Maintainer  :  Hal Daume III <me@hal3.name>
-- Stability   :  stable
-- Portability :  portable
--
-- Provides very rudimentary type checking
--
-----------------------------------------------------------------------------

module Type where -- (Type0(..),Type(..),TypeMap,getTypeMap,inferType,tInt,tReal) where

import Core
import Data.List
import qualified Data.Map as M
import Control.Monad
import Util
import Data.Generics hiding ((:*:))
import Data.Typeable
import Debug.Trace
import Data.Maybe
import Data.Char

data Type0 = T0Int | T0Real | T0Unk deriving (Eq, Ord, Typeable, Data)
data Type  = Type { baseType :: Type0 , indices :: [Range] }
                               -- indices only allowed to use Var/Con; Var "?" means unknown
           | TDist Type deriving (Eq, Ord, Typeable, Data)

type TypeMap = M.Map Id Type

tInt  = Type T0Int  []
tReal = Type T0Real []

instance Show Type0 where
  showsPrec i T0Int  = showChar 'Z'
  showsPrec i T0Real = showChar 'R'
  showsPrec i T0Unk  = showChar 'U'

instance Show Type where
  showsPrec i (Type t0 []) = showsPrec i t0
  showsPrec i (Type t0 (x:xs)) = showsPrec i t0 . showString "_{" . showsPrec i x . showsRanges xs . showChar '}'
    where
      showsRanges [] = id
      showsRanges (x:xs) = showChar ',' . showsPrec i x . showsRanges xs
  showsPrec i (TDist t) = showString "dist(" . showsPrec i t . showChar ')'

multivarRange = (`elem` ["Dir", "DirSym", "NorMV", "Delta"])

getDistRange _ "Bin"    _ = tInt
getDistRange _ "Exp"    _ = tReal
getDistRange _ "Bet"    _ = tReal
getDistRange _ "Dir"    [_,len] = Type T0Real [mkR1 len]
getDistRange _ "DirSym" [_,Con c] = Type T0Real [mkR1 (Con c)]
getDistRange _ "DirSym" [_,Var v] = Type T0Real [mkR1 (Var v)]
getDistRange _ "DirSym" _ = Type T0Real [mkR1 unk]
getDistRange _ "Mult"   _ = tInt
getDistRange _ "MultSym" _ = tInt
getDistRange _ "Nor"    _ = tReal
getDistRange _ "NorMV"  [_,_,dim] = Type T0Real [mkR1 dim]
getDistRange _ "NorMV"  [_,_] = Type T0Real [mkR1 unk]
getDistRange _ "Gam"    _ = tReal
getDistRange _ "Poi"    _ = tInt
getDistRange _ "IG"     _ = tReal
getDistRange _ "Delta" [_,Con c] = Type T0Real [mkR1 (Con c)]
getDistRange _ "Delta" [_,Var v] = Type T0Real [mkR1 (Var v)]
getDistRange _ "Delta" _ = Type T0Real [mkR1 unk]
getDistRange _ "PY" (_:_:c:_) = Type T0Real [mkR1 (Func "+" [c, Con (I 1)])]
--getDistRange typ0 "PY"    (_:_:(Var (V d [])):args) = TDist (getDistRange typ0 d args)
--getDistRange typ0 d _ 
--  | Just (TDist t) <- M.lookup d typ0 = t
-- marginalized
{-getDistRange  "PoiGam" _ = tInt
getDistRange  "ExpGam" _ = tReal
getDistRange  "BinBet" _ = tInt
getDistRange  "MultDir" _ = tInt
getDistRange  "MultDirSym" _ = tInt
getDistRange  "NorNor" _ = tReal
getDistRange  "NorNorMV" [_,_,_,dim] = Type T0Real [mkR1 dim] -}
getDistRange typ0 d el = error ("Type.getDistRange: cannot infer type of " ++ show (d,el) ++ " in dictionary " ++ show typ0)

getDistDomain _  "Bin" _ _ = [tReal]
getDistDomain _  "Exp" _ _ = [tReal]
getDistDomain _  "Bet" _ _ = [tReal, tReal]
getDistDomain _  "Dir"    [_,l] _ = [Type T0Real [mkR1 l], tInt]
getDistDomain _  "DirSym" _     _ = [tReal, tInt]
getDistDomain _  "Mult"   _     _ = [Type T0Real [mkR1 unk]]
getDistDomain _  "MultSym"   _     _ = [tInt,tInt]
getDistDomain _  "Nor"    _     _ = [tReal, tReal]
getDistDomain _  "NorMV"  [_,_,l] _ = [Type T0Real [mkR1 l], tReal, tInt]
getDistDomain _  "NorMV"  [_,_] (Just t0) = [t0, tReal, tInt]
getDistDomain _  "NorMV"  [_,_] _ = [Type T0Real [mkR1 unk], tReal, tInt]
getDistDomain _  "Poi"    _     _ = [tReal]
getDistDomain _  "Gam"    _     _ = [tReal, tReal]
getDistDomain _  "IG"     _     _ = [tReal, tReal]
getDistDomain _  "Delta"  [_,l] _ = [Type T0Real [mkR1 l], tInt]
getDistDomain _  "PY"     _     _ = [tReal, tReal, tInt, Type T0Real [mkR1 unk]]
--getDistDomain typ0 "PY"     (_:_:(Var (V d [])):args) z = getDistDomain typ0 d args z
--getDistDomain typ0 d _ _ | Just t <- M.lookup d typ0 = []
-- marginalized ; first is always "n", second is always "sum_x"
{-getDistDomain _  "PoiGam" _ _ = [tInt, tInt, tReal, tReal]
getDistDomain _  "ExpGam" _ _ = [tInt, tReal, tReal, tReal]
getDistDomain _  "BinBet" _ _ = [tInt, tInt, tReal, tReal]
getDistDomain _  "MultDir" [_,_,_,l] _ = [tInt, Type T0Int [mkR1 l], Type T0Real [mkR1 l], tInt]
getDistDomain _  "MultDirSym" [_,_,_,l] _ = [tInt, Type T0Int [mkR1 l], Type T0Real [mkR1 l], tInt]
getDistDomain _  "NorNor" _ _ = [tInt, tReal, tReal, tReal, tReal]
getDistDomain _  "NorNorMV" [_,_,_,_,dim] _ = [tInt, Type T0Real [mkR1 dim], Type T0Real [mkR1 dim], tReal, tReal] -}
getDistDomain typ0 d el _ = error ("Type.getDistDomain: cannot infer type of " ++ show (d,el) ++ " in dictionary " ++ show typ0)


getFuncDomain t0@(Type t0t t0i) f
  | f `elem` ["+","-","*","/"] = [t0,t0]
  | f `elem` [".+",".-",".*","./"] = [Type T0Unk [],t0]
  | f `elem` ["=","~=","<=","<",">",">=","||","&&"] = [Type T0Unk [], Type T0Unk []]
  | f == "^" = [t0, tReal]
  | f `elem` ["log", "exp"] = [t0]
  | f == "sub" = (Type t0t ([mkR1 unk] ++ t0i)) : repeat tInt
  | f == "vec" = (Type t0t (drop 1 t0i)) : repeat tInt
  | f == "ID"  = [tInt,tInt,tInt]
  | f == "IDR" = [tInt,tInt,tInt]
  | f == "any" || f == "all" || f == "sum" || f == "prod" = [Type t0t []]
  | f == "sqrDiff" = [Type T0Real [mkR1 unk], Type T0Real [mkR1 unk]]
  | f == "addLog"  = [tReal, tReal]
  | f == "sample_Bin" = [tReal]
  | f == "sqrt" = [tReal]
  | otherwise = error ("Type.getFuncDomain: unknown function " ++ show f ++ " with type " ++ show t0)

getFuncRange tm f domTyp maybeEl
  | f `elem` ["+","-","*","/"] = (domTyp !! 0) `mplus` (domTyp !! 1)
  | f `elem` ["=","~=","<=","<",">",">=","||","&&"] = case (domTyp !! 0) `mplus` (domTyp !! 1) of { Just (Type _ i) -> Just (Type T0Int i) ; _ -> Nothing }
  | f `elem` [".+",".-",".*","./"] = domTyp !! 1
  | f `elem` ["^","log","exp"] = domTyp !! 0
  | f == "sub" = case domTyp!!0 of { Just t -> Just (Type (baseType t) (drop (length domTyp-1) $ indices t)) ; _ -> Nothing }
  | f == "ID"  = Just (Type T0Int  (makeVecRange (tail el')))
  | f == "IDR" = Just (Type T0Real (makeVecRange (tail el')))
  | f == "vec" = case domTyp!!0 of { Just t0 -> Just (Type (baseType t0) (makeVecRange (tail el'))) ; _ -> Nothing }
  | f == "any" || f == "all" || f == "sum" || f == "prod" = case (domTyp !! 0) of { Just (Type t0 _) -> Just (Type t0 []) ; _ -> Nothing }
  | "ldf_" `isPrefixOf` f = Just tReal
  | "lnorm_" `isPrefixOf` f = Just tReal
  | "mult_const" `isPrefixOf` f || "mult_vec" `isPrefixOf` f || 
     "add_const" `isPrefixOf` f ||  "add_vec" `isPrefixOf` f ||
     "div_const" `isPrefixOf` f ||  "div_vec" `isPrefixOf` f ||
     "sub_const" `isPrefixOf` f ||  "sub_vec" `isPrefixOf` f = domTyp !! 0
  | "exp_vec_" `isPrefixOf` f || "log_vec_" `isPrefixOf` f = domTyp !! 0
  | f == "sqrDiff" = Just tReal
  | f == "addLog"  = Just tReal
  | f == "sample_Bin" = Just tInt
  | f == "sqrt" = Just tReal
  | otherwise  = error ("Type.getFuncRange: unknown function " ++ show f ++ " with arguments " ++ show (maybeEl))
  where
    Just el' = maybeEl
    makeVecRange [] = []
    makeVecRange (lo:hi:xs) = mkR0 "" lo hi : makeVecRange xs
--    makeVecRange 

--    domTyp = map (inferType tm) el

quantifyGlobalType :: Type -> Type
quantifyGlobalType (Type t0 rl) = Type t0 (quantifyGlobalType' [] 1 rl)
  where
    quantifyGlobalType' _  _ [] = []
    quantifyGlobalType' lu n ((Range id lo hi):rs) = (Range "" lo' hi') : quantifyGlobalType' lu' (n+1) rs
      where
        lu' = if id == "" then lu else ((id,"#" ++ show n):lu)
        lo' = quantifyExpr lu lo
        hi' = quantifyExpr lu hi

    quantifyExpr lu (Var (V id [])) =
      case lookup id lu of
        Nothing -> Var (V id [])
        Just i0 -> Var (V i0 [])
    quantifyExpr lu (Var (V id sl)) =
      case lookup id lu of
        Nothing -> Var (V id $ map (quantifySExpr lu) sl)
        Just i0 -> error ("Type.quantifyGlobalType.quantifyExpr: quantified id " ++ show id ++ " appears with indexing")
    quantifyExpr lu (Con c) = Con c
    quantifyExpr lu (Func "+" [a,Con c]) = Func "+" [quantifyExpr lu a, Con c]
    quantifyExpr lu (Func "-" [a,Con c]) = Func "-" [quantifyExpr lu a, Con c]
    quantifyExpr lu e = error ("Type.quantifyGlobalType.quantifyExpr: cannot quantify expression: " ++ show e)

    quantifySExpr lu (Id id c) =
      case lookup id lu of
        Nothing -> Id id c
        Just i0 -> Id i0 c
    quantifySExpr lu c = c
quantifyGlobalType (TDist t) = TDist (quantifyGlobalType t)

--getTypeMap :: Core -> TypeMap
getTypeMap declTypes core = typ0 `M.union` (M.unionWith unify typ1 (M.unionWith unify typ2 typ3))
  where
    typ0 = makeDeclTypeMap declTypes
    typ1 = M.fromList [(v,getGlobalType typ0 core v) | v <- getGlobals core]
    typ2 = M.fromList [(v,getGlobalType typ1 core v) | v <- getGlobals core]
    typ3 = M.fromList [(v,getGlobalType typ2 core v) | v <- getGlobals core]
    

makeDeclTypeMap :: [(Var,Int,Char,[Expr],[Range])] -> TypeMap
makeDeclTypeMap = foldr (\ d@(V id _,n,c,el,_) tm -> M.insert id (makeDist n (makeType c el)) tm) M.empty
  where
    makeDist 0 t = t
    makeDist n t = makeDist (n-1) (TDist t)
    makeType t0 el = Type (if t0 == 'I' then T0Int else T0Real) (map makeERange el)
    makeERange e = Range "" (Con (I 1)) e

{-
makeDeclTypeMap = foldr (\ d@(V id _,_,_) tm -> M.insert id (makeType d) tm) M.empty
  where
    makeType (V _ sl, typ0, rl) = Type (if typ0=='I' then T0Int else T0Real) (map (makeSLRange rl) sl)
-}


--getGlobalType :: Core -> Id -> Type
getGlobalType typ0 core id {- | mytrace (show ("getGlobalType",id,allT)) True -} = quantifyGlobalType $ unifyN allT
  where
    allT = getGlobalAllTypes typ0 core id

-- (2,T-1) / (3,T) / (1,T-2) / (2,T-1)

--getGlobalAllTypes :: Core -> Id -> [Type]
getGlobalAllTypes typ0 (Core dl) id = 
  nub $ concat ([getDistTypes typ0 rl id dist ++ 
                 concat (snd (mapAccumL (\acc r -> (r:acc, getRangeTypes typ0 acc id r)) [] rl))
                     | (_, dist, rl) <- dl])

getDistTypes typ0 rl id (a :*: b)  = getDistTypes typ0  rl id a ++ getDistTypes typ0 rl id b
getDistTypes typ0 rl id (a :^: e)  = getDistTypes typ0  rl id a ++ getExprTypes typ0 rl id tReal e
getDistTypes typ0 rl id (Prod r d _) = getRangeTypes typ0 rl id r ++ getDistTypes typ0 (r:rl) id d
getDistTypes typ0 rl id (Dist (V i sl) dist el) 
  | id == i   = getOneDistType typ0 rl dist el i sl : rest
  | otherwise = rest
  where 
    rest = concatMap (getSExprTypes typ0 rl id) sl ++ 
           concat (zipWith (getExprTypes typ0 rl id) tl el)
    tl   = getDistDomain typ0 dist el thisTyp0
    thisTyp0 = case M.lookup i typ0 of
                 Nothing -> Nothing
                 Just (Type t0 r0) -> Just (Type t0 (drop (length sl) r0))

getRangeTypes typ0 rl id (Range _ lo hi) = getExprTypes typ0 rl id tInt lo ++ getExprTypes typ0 rl id tInt hi

getExprTypes typ0 rl id (Type t0 r0) (Var (V i sl)) 
  | id == i = [Type t0 ((map (makeSLRange rl) sl) ++ r0)]
  | otherwise = []
getExprTypes typ0 rl id t0 (Con _) = []
getExprTypes typ0 rl id t0 (Func f el) = concat $ zipWith (getExprTypes typ0 rl id) (getFuncDomain t0 f) el
getExprTypes typ0 rl id t0 sp@(SP _ r e spv) 
  | id == spv = t0 : maybeToList (inferType typ0 e) ++ rest
  | otherwise =      rest
  where rest = getRangeTypes typ0 rl id r ++ getExprTypes typ0 (r:rl) id t0 e
getExprTypes typ0 rl id t0 (Case cv cs) = concatMap (\ (_,f) -> getExprTypes typ0 rl id t0 f) cs

getSExprTypes typ0 rl id (Id i _) | i == id = [tInt]
getSExprTypes typ0 _ _ _ = []

getOneDistType typ0 rl dist distEl i sl = 
  case M.lookup i typ0 of
    Nothing -> 
        case getDistRange typ0 dist distEl of
          Type t0 r0 -> Type t0 ((map (makeSLRange rl) sl) ++ r0)
          TDist t -> if null sl then TDist t else error ("Type.getOneDistType(1): subindices on distribution: " ++ show t ++ " in context " ++ show (i,typ0,sl))
    Just (Type t0 r0) -> Type t0 (drop (length sl) r0)
    Just (TDist t) -> if null sl then TDist t else error ("Type.getOneDistType(2): subindices on distribution: " ++ show t)

makeSLRange rl (Id i Nothing) = lookupRange rl i
makeSLRange rl (Id i (Just c)) = adjustRange c $ lookupRange rl i
makeSLRange rl (Cn c) = mkR0 "" (Con c) (Con c)

lookupRange rl i =
  case find (\ (Range id _ _) -> id == i) rl of
    Nothing -> error ("Type.lookupRange: cannot find quantification for " ++ show i ++ " in rangeList: " ++ show rl)
    Just (Range i lo hi) -> mkR0 i lo hi

adjustRange c (Range id lo hi) = Range id (Func "-" [lo,Con c]) (Func "-" [hi,Con c])

mkR0 id lo hi = Range id lo hi
mkR1 = mkR0 "" (Con (I 1))
unk = Var (V "?" [])
unk' = Var (V "" [])

unify0 a b | a == b = a
unify0 T0Unk b = b
unify0 a T0Unk = a
unify0 _ _ = T0Int

unify :: Type -> Type -> Type
unify (Type t0 b0) (Type t1 b1) = Type (unify0 t0 t1) (unifyBound [] b0 b1)
unify (TDist t0)   (TDist t1)   = TDist (unify t0 t1)
unify (Type T0Unk []) z = z
unify z (Type T0Unk []) = z
unify t0 t1 = error ("Type.unify: cannot unify distributions with normal types in " ++ show [t0,t1])

unifyN = foldr unify (Type T0Unk [])

unifyBound lu x [] = map (renameRange lu) x
unifyBound lu [] y = map (renameRange lu) y
unifyBound lu ((Range id0 lo0 hi0):xs) ((Range id1 lo1 hi1):ys) =
  renameRange lu r' : unifyBound lu' xs ys
  where 
    lu' = if id0 == id1 then lu else (id0,id1):lu
    r'  = Range id1 (unifyRange lo0 lo1) (unifyRange hi0 hi1)

renameRange lu (Range id lo hi) = Range (repl id) (renE lo) (renE hi)
  where
    repl id = case lookup id lu of { Just id' -> id' ; Nothing -> id }
    renE (Var v) = Var (renV v)
    renE (Con c) = Con c
    renE (Func f el) = Func f $ map renE el
    renE (SP b (Range i l h) e spv) = SP b (Range (repl i) (renE l) (renE h)) (renE e) spv
    renV (V id sl) = V (repl id) $ map renS sl
    renS (Id id c) = Id (repl id) c
    renS (Cn c) = Cn c

unifyRange a b 
  | a == b = a
  | a == unk' = b
  | b == unk' = a
  | a == unk = b
  | b == unk = a
unifyRange _ c@(Con _) = c
unifyRange c@(Con _) _ = c
unifyRange a@(Var (V a0 _)) b@(Var (V b0 _))
  | a0 == b0 = b
unifyRange a b = a -- error ("Type.unifyRange: cannot unify " ++ show a ++ " and " ++ show b)



-----------------------------------------------------------------------------

inferType :: TypeMap -> Expr -> Maybe Type
inferType tm (Var v)     = inferTypeVar tm v
inferType tm (Con (I _)) = Just tInt
inferType tm (Con (R _)) = Just tReal
inferType tm (SP _ _ e _)= inferType tm e
inferType tm (Func f el) = getFuncRange tm f (map (inferType tm) el) (Just el)
inferType tm (Case _ cs) = msum $ map (inferType tm . snd) cs

inferTypeVar tm (V v sl) =
  case M.lookup v tm of
    Nothing -> Nothing
    Just (Type t0 t0i) ->
      if length sl > length t0i 
      then Nothing
      else Just (Type t0 (resolvePoundType sl $ drop (length sl) t0i))

resolvePoundType sl = everywhere (mkT resolvePoundType')
  where
    resolvePoundType' ('#':z)
      | all isDigit z && read z <= length sl =
      case sl !! (read z - 1) of
        Id i0 Nothing -> i0
        _ -> error $ "Code.resolvePoundType: found type pointer to non-Var expr: " ++ show (sl !! (read z - 1))
    resolvePoundType' v = v





inferMissingRanges :: TypeMap -> Core -> Core
inferMissingRanges tm = Core . map imrDecl . decls
  where
    imrDecl (v, dist, rl) = (v, imrDist dist, map (fillInBy dist) rl)

    imrDist d@(Dist _ _ _) = d
    imrDist (a :*: b) = imrDist a :*: imrDist b
    imrDist (a :^: e) = imrDist a :^: e
    imrDist (Prod r d spid) = Prod (fillInBy d r) (imrDist d) spid

    fillInBy d r@(Range id lo hi)
      | lo /= unkV && hi /= unkV = r
--      | mytrace (show ((lo,hi),(usage,mapMaybe (getUsageRange id) usage),(lo',hi'))) False = undefined
      | lo == unkV && hi == unkV = Range id lo' hi'
      | lo == unkV               = Range id lo' hi
      |               hi == unkV = Range id lo  hi'
      where
        usage = findUsage id d

        Range _ lo' hi' = unifyRanges (mapMaybe (getUsageRange id) usage)

        unifyRanges [] = r
        unifyRanges [Range _ lo hi] = Range id lo hi
        unifyRanges ((Range _ lo hi):rs) =
            let Range _ lo0 hi0 = unifyRanges rs
                lo' = if lo == unkV then lo0 else lo
                hi' = if hi == unkV then hi0 else hi
            in  Range id lo' hi'
        

    findUsage id = listify (\ (V _ el) -> Id id Nothing `elem` el)

    getUsageRange id (V id0 el) =
      case M.lookup id0 tm of
        Nothing -> Nothing
        Just (Type _ trl) -> Just (everywhere (mkT fillInTypeRefs) (trl !! idx))
      where
        idx = fromJust $ findIndex (==Id id Nothing) el
        fillInTypeRefs (Id ('#':nn) Nothing) = el !! (read nn-1)


typeDependsOn :: Type -> Var -> Bool
typeDependsOn (Type _ indices) var = any (\r -> rangeDependsOn r var) indices

rangeDependsOn (Range _ lo hi) var = exprDependsOn lo || exprDependsOn hi
  where
    exprDependsOn (Var v@(V _ se)) = v == var || any sexprDependsOn se
    exprDependsOn (Con _) = False
    exprDependsOn (Func _ el) = any exprDependsOn el
    exprDependsOn (Case e cs) = any exprDependsOn (e : map fst cs ++ map snd cs)
    exprDependsOn (SP _ r e _) = rangeDependsOn r var || exprDependsOn e
    sexprDependsOn (Id id _) = case var of { V id' [] -> id == id' ; _ -> False }
    sexprDependsOn _ = False

