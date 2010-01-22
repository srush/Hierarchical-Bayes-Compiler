----------------------------------------------------------------------------
-- |
-- Module      :  Core
-- Project     :  HBC
-- Copyright   :  (c) Hal Daume III
-- License     :  Open
-- 
-- Maintainer  :  Hal Daume III <me@hal3.name>
-- Stability   :  stable
-- Portability :  portable
--
-- The Core module: implements the base declarations for the core language 
-- of the HBC, plus various utilities for traversing and extracting
-- information from these declarations
--
-----------------------------------------------------------------------------

module Core where

import Data.List
import Data.Maybe
import Control.Monad
import Util
import Control.Monad.State
import Data.Generics hiding ((:*:))
import Data.Typeable
import Data.Char

type Id    = String
data Var   = V Id [SExpr]               deriving (Eq, Ord, Typeable, Data)
data Const = I Integer | R Double       deriving (Eq, Ord, Typeable, Data)

type Decl  = (Var, Dist, [Range])
data Core  = Core { decls :: [Decl] }
data Dist  = Dist Var Id [Expr]
           | Dist :*: Dist
           | Dist :^: Expr
           | Prod Range Dist Id         deriving (Eq, Ord, Typeable, Data)
                        --   ^^-- this is the new name assigned by renameSPVars
data SExpr = Id   Id (Maybe Const)
           | Cn   Const                 deriving (Eq, Ord, Typeable, Data)
data Expr  = Var  Var
           | Con  Const
           | Func Id [Expr]
           | Case Expr [(Expr,Expr)]
           | SP   Bool Range Expr Id    deriving (Eq, Ord, Typeable, Data)   -- false means "sum"
                             --   ^^-- this is the new name assigned by renameSPVars
data Range = Range { rangeId :: Id , rangeLo :: Expr , rangeHi :: Expr }         deriving (Eq, Ord, Typeable, Data)

varId (V id _) = id

-- Make everything an instance of show with some reasonable description:
instance Show Var where
  showsPrec i (V v []) = showString v
  showsPrec i (V v (x:l)) = showString v . showString "_{" . showsPrec i x . showL l . showChar '}'
    where { showL [] = id ; showL (x:xs) = showChar ',' . showsPrec i x . showL xs }

instance Show Const where
  showsPrec i (I j) = showsPrec i j
  showsPrec i (R j) = showsPrec i j

instance Show Dist where
  showsPrec i (Dist v "I" []) = showString "I"
  showsPrec i (Dist v "R" []) = showString "R"
  showsPrec i (Dist v d   []) = showString d . showChar '(' . showChar ')'
  showsPrec i (Dist v d (x:l)) = showString d . showChar '(' . showsPrec i v . showString " | " . showsPrec i x . showL l . showChar ')'
    where { showL [] = id ; showL (x:xs) = showString ", " . showsPrec i x . showL xs }
  showsPrec i (a :*: b) = showChar '(' . showsPrec i a . showString ")(" . showsPrec i b . showChar ')'
  showsPrec i (a :^: b) = showChar '(' . showsPrec i a . showString ")^{" . showsPrec i b . showChar '}'
  showsPrec i (Prod r d _) = showString "\\Prod_{" . showsPrec i r . showString "} " . showsPrec i d

instance Show SExpr where
  showsPrec i (Id v Nothing) = showString v
  showsPrec i (Id v (Just (I k)))
    | k == 0    = showString v
    | k >  0    = showString v . showChar '+' . shows k
    | otherwise = showString v . shows k
  showsPrec i (Id v (Just (R k)))
    | k == 0    = showString v
    | k >  0    = showString v . showChar '+' . shows k
    | otherwise = showString v . shows k
  showsPrec i (Cn c) = showsPrec i c

instance Show Expr where
  showsPrec i (Var v) = showsPrec i v
  showsPrec i (Con c) = showsPrec i c
  showsPrec i (Func f (x:l)) = showString f . showChar '(' . showsPrec i x . showL l . showChar ')'
    where { showL [] = id ; showL (x:xs) = showString ", " . showsPrec i x . showL xs }
  showsPrec i (SP prod r e _) = showChar '\\' . (if prod then showString "prod" else showString "sum") . showString "_{" . showsPrec i r . showString "} " . showsPrec i e
  showsPrec i (Case cv cs) = showString "case " . shows cv . showString " of {" . showCases cs . showString " }"
    where
      showCases [] = id
      showCases ((e,r):rs) = showChar ' ' . showsPrec i e . showString " :> " . showsPrec i r . if null rs then id else (showString " ;" . showCases rs)

instance Show Range where
  showsPrec i (Range "" (Con (I 1)) hi) = showsPrec i hi
  showsPrec i (Range "" lo hi) = showChar '[' . showsPrec i lo . showChar ',' . showsPrec i hi . showChar ']'
  showsPrec i (Range v  (Con (I 1)) hi) = showString v . showString " \\in [" . showsPrec i hi . showChar ']'
  showsPrec i (Range v  lo hi) = showString v . showString " \\in [" . showsPrec i lo . showChar ',' . showsPrec i hi . showChar ']'

instance Show Core where
  showsPrec i (Core []) = id
  showsPrec i (Core (x:l)) = showsPrec i x . showChar '\n' . showsPrec i (Core l)


sizeOfExpr e = length (show e)

findVariableOccurance :: Var -> Dist -> Maybe Dist
findVariableOccurance v0 d@(Dist v _ _) | v == v0   = Just d
                                        | otherwise = Nothing
findVariableOccurance v0 (a :*: b) = findVariableOccurance v0 a `mplus` findVariableOccurance v0 b
findVariableOccurance v0 (a :^: _) = findVariableOccurance v0 a
findVariableOccurance v0 (Prod _ d _) = findVariableOccurance v0 d

getGlobals :: Core -> [Id]
getGlobals = sort . nub . concatMap getDeclGlobals . decls

getDeclGlobals (V id se, d, r) = 
                 id :  getDistGlobals  ("?" : {- concatMap qualifiedSExpr se ++ -} map rangeIds r) d
                    ++ getRangeGlobals [] r
  where
    getRangeGlobals qual [] = []
    getRangeGlobals qual ((Range id lo hi):rs) =
      getExprGlobals  qual lo ++ 
      getExprGlobals  qual hi ++ 
      getRangeGlobals (id:qual) rs

rangeIds (Range i _ _) = i

qualifiedSExpr (Id i _) = [i]
qualifiedSExpr _ = []

getDistGlobals qual (Dist (V id se) _ el) 
  | id `elem` qual =      concatMap (getSExprGlobals qual) se ++ concatMap (getExprGlobals qual) el
  | otherwise      = id : concatMap (getSExprGlobals qual) se ++ concatMap (getExprGlobals qual) el
getDistGlobals qual (a :*: b)     = getDistGlobals qual a ++ getDistGlobals qual b
getDistGlobals qual (a :^: e)     = getDistGlobals qual a ++ getExprGlobals qual e
getDistGlobals qual (Prod (Range id lo hi) d _) = getExprGlobals qual lo ++ getExprGlobals qual hi ++ getDistGlobals (id:qual) d

getExprGlobals qual (Var (V id se)) 
  | id `elem` qual =      concatMap (getSExprGlobals qual) se
  | otherwise      = id : concatMap (getSExprGlobals qual) se
getExprGlobals qual (Con _) = []
getExprGlobals qual (Func _ el) = concatMap (getExprGlobals qual) el
getExprGlobals qual sp@(SP _ (Range id lo hi) e _) = spVarName sp : getExprGlobals qual lo ++ getExprGlobals qual hi ++ getExprGlobals (id:qual) e
getExprGlobals qual (Case cv cs) = getExprGlobals qual (cv) ++ concatMap (\ (e,f) -> getExprGlobals qual e ++ getExprGlobals qual f) cs

getSExprGlobals qual (Id id _)
  | id `elem` qual = []
  | otherwise      = [id]
getSExprGlobals qual _ = []

renameLocals :: Core -> Core
renameLocals core@(Core decls) = Core (zipWith renameDecl stores decls)
  where 
    globals = getGlobals core
    stores  = [["#local#" ++ show i ++ "*" ++ show j | j <- [0..]] | i <- [0..]]
    
    renameDecl st (v,dist,r) = (v, renameDist st1 mp dist, r')
      where 
        (st0,st1) = split st
        stR       = splitN (length r) st1
        (mp ,r' ) = mapAccumL renameRanges [] (zip stR r)

    renameRanges mp (id0:st, Range v lo hi)
      | v `elem` globals = (mp , Range v   (renameExpr st0 mp  lo) (renameExpr st1 mp  hi))
      | otherwise        = (mp', Range id0 (renameExpr st0 mp' lo) (renameExpr st1 mp' hi))
      where (st0,st1) = split st
            mp'       = (v,id0) : mp

    renameDist st mp (Dist v d el) = let (st0,st1) = split st in Dist (renameVar st0 mp v) d (zipWith (\s e -> renameExpr s mp e) (splitN (length el) st1) el)
    renameDist st mp (a :*: b)     = let (st0,st1) = split st in (renameDist st0 mp a :*: renameDist st1 mp b)
    renameDist st mp (a :^: e)     = let (st0,st1) = split st in (renameDist st0 mp a :^: renameExpr st1 mp e)
    renameDist st mp (Prod (Range v lo hi) d nam) = Prod (Range v' (renameExpr st0 mp lo) (renameExpr st1 mp hi)) (renameDist st2 mp' d) nam
      where 
        (v',st',mp') = if v `elem` globals then (v,st,mp) else (head st,tail st,(v,head st):mp)
        [st0,st1,st2] = splitN 3 st'

    renameVar st mp (V i sl) = V (fromMaybe i (lookup i mp)) (zipWith (\s se -> renameSExpr s mp se) (splitN (length sl) st) sl)
    
    renameSExpr st mp (Id i c) = Id (fromMaybe i (lookup i mp)) c
    renameSExpr st mp c        = c

    renameExpr st mp (Var v) = Var (renameVar st mp v)
    renameExpr st mp (Con c) = Con c
    renameExpr st mp (Func i el) = Func (fromMaybe i (lookup i mp)) (zipWith (\s e -> renameExpr s mp e) (splitN (length el) st) el)
    renameExpr st mp (SP b (Range v lo hi) e spv) = SP b (Range v' (renameExpr st0 mp lo) (renameExpr st1 mp hi)) (renameExpr st2 mp' e) spv
      where 
        (v',st',mp') = if v `elem` globals then (v,st,mp) else (head st,tail st,(v,head st):mp)
        [st0,st1,st2] = splitN 3 st'

---------------------------


distTimes Nothing b = b
distTimes a Nothing = a
distTimes (Just a) (Just b) = Just (a :*: b)

d `distWithout` d0 | d == d0 = Nothing
(a :*: b) `distWithout` d0 =
  case (a `distWithout` d0, b `distWithout` d0) of
    (Nothing, d)    -> d
    (d, Nothing)    -> d
    (Just d,Just e) -> Just (d :*: e)
(a :^: e) `distWithout` d0 = liftM (:^: e) (a `distWithout` d0)
(Prod r d spv) `distWithout` d0 = liftM (\d' -> Prod r d' spv) (d `distWithout` d0)
d `distWithout` _ = Just d

unkV = Var (V "?" [])

exprToSExpr e = exprToSExpr' e Nothing
  where
    exprToSExpr' (Con c) Nothing = Just (Cn c)
    exprToSExpr' (Con c) (Just (Cn c0)) = Just (Cn $ addConstant c c0)
    exprToSExpr' (Con c) (Just (Id id Nothing)) = Just (Id id (Just c))
    exprToSExpr' (Con c) (Just (Id id (Just c0))) = Just (Id id (Just (addConstant c c0)))

    exprToSExpr' (Var (V id [])) Nothing = Just (Id id Nothing)
    exprToSExpr' (Var (V id [])) (Just (Cn c0)) = Just (Id id (Just c0))

    exprToSExpr' _ _ = Nothing

addConstant (I a) (I b) = I (a+b)
addConstant (R a) (R b) = R (a+b)
addConstant (I a) (R b) = R ((fromIntegral a) + b)
addConstant (R a) (I b) = R (a + (fromIntegral b))

sexprToExpr (Id id Nothing)  = Var (V id [])
sexprToExpr (Id id (Just c)) = Func "+" [Var (V id []), Con c]
sexprToExpr (Cn c) = Con c

--spVarName sp@(SP b (Range id _ _) _ _) = "tmp" ++ (if b then "P" else "S") ++ "_" ++ id ++ "_" ++ show (sizeOfExpr sp)
spVarName (SP _ _ _ "") = error ("Core.spVarName: called before naming SPvars")
spVarName (SP _ _ _ n ) = n

isLocal x = "#local#" `isPrefixOf` x
isLocalE (Var (V x [])) = isLocal x
isLocalE _ = False

fiddleSP (Core dl) = Core (zipWith fiddleSPDecl store dl)
  where store = splitN (length dl) $ map show [0..]
        fiddleSPDecl s (var, dist, rl) = (fiddleVar mp var, fiddleSPDist mp s0 dist, rl')
          where
            (s0:s1)  = splitN (length rl+1) s
            (mp,rl') = mapAccumL mkRange [] (zip s1 rl)

            mkRange mp (s,Range id lo hi) = (mp', Range id' (fiddleSPExpr mp' s0 lo) (fiddleSPExpr mp' s1 hi))
              where (s0,s1) = split (tail s)
                    id' = id ++ "@" ++ head s
                    mp' = (id,id') : mp

        fiddleSPDist mp s (Dist v i el) = Dist (fiddleVar mp v) i $ zipWith (fiddleSPExpr mp) sl el where sl = splitN (length el) s
        fiddleSPDist mp s (a :*: b) = fiddleSPDist mp s0 a :*: fiddleSPDist mp s1 b where (s0,s1) = split s
        fiddleSPDist mp s (a :^: b) = fiddleSPDist mp s0 a :^: fiddleSPExpr mp s1 b where (s0,s1) = split s
        fiddleSPDist mp s (Prod (Range id lo hi) d spv) = Prod (Range id' (fiddleSPExpr mp' s0 lo) (fiddleSPExpr mp' s1 hi)) (fiddleSPDist mp' s2 d) spv
          where
            id' = id ++ "@" ++ head s
            [s0,s1,s2] = splitN 3 (tail s)
            mp' = (id,id') : mp

        fiddleVar mp (V id sl) =
--          | id == "?" && mytrace ("Id=" ++ show id ++ ",id=" ++ show (lookup id mp)) False = undefined
--          | otherwise =
          case lookup id mp of
            Nothing -> (V id sl')
            Just i0 -> (V i0 sl')
          where sl' = map (fiddleSPSExpr mp) sl

        fiddleSPExpr mp s (Var v) = Var $ fiddleVar mp v
        fiddleSPExpr mp s (Con c) = Con c
        fiddleSPExpr mp s (Func f el) = Func f $ zipWith (fiddleSPExpr mp) (splitN (length el) s) el
        fiddleSPExpr mp s (SP b (Range id lo hi) e spv) = SP b (Range id' (fiddleSPExpr mp' s0 lo) (fiddleSPExpr mp' s1 hi)) (fiddleSPExpr mp' s2 e) spv
          where [s0,s1,s2] = splitN 3 (tail s)
                id' = id ++ "@" ++ head s
                mp' = (id, id') : mp
        fiddleSPExpr mp s (Case cv cs) = Case (fiddleSPExpr mp s cv) (map (\ (e,f) -> (fiddleSPExpr mp s e, fiddleSPExpr mp s f)) cs)

        fiddleSPSExpr mp (Cn c) = Cn c
        fiddleSPSExpr mp (Id id c) =
          case lookup id mp of
            Nothing -> Id id c
            Just i0 -> Id i0 c

replaceVar v0@(V vi0 sl0) vnew (Dist vv@(V v sl) d el)
  | vi0 == v && sl0 `isPrefixOf` sl = Just (Dist vv' d (map (replaceVarExpr v0 e0) el))
  | all isJust sl'                  = Just (Dist vv  d (map (replaceVarExpr v0 e0) el))
  | otherwise      = Nothing
  where e0  = Var (V vnew [])
        vv' = V vnew (drop (length sl0) sl)
        sl' = map (replaceVarSExpr v0 e0) sl
replaceVar v0 vnew (a :*: b) =
  case (replaceVar v0 vnew a, replaceVar v0 vnew b) of
    (Just a', Just b') -> Just (a' :*: b')
    _                  -> Nothing
replaceVar v0 vnew (a :^: e)  = 
  case (replaceVarExpr v0 e0 e, replaceVar v0 vnew a) of
    (e', Just a') -> Just (a' :^: e')
    _ -> Nothing
  where e0  = Var (V vnew [])
replaceVar v0 vnew (Prod r d spv) = liftM (\d' -> Prod (replaceVarRange v0 e0 r) d' spv) $ replaceVar v0 vnew d
  where e0  = Var (V vnew [])



replaceVarWithExpr v0@(V vi0 sl0) enew (Dist v1 d el) = Dist v1 d (map (replaceVarExpr v0 enew) el)
replaceVarWithExpr v0 enew (a :*: b) = ((replaceVarWithExpr v0 enew a) :*: (replaceVarWithExpr v0 enew b))
replaceVarWithExpr v0 enew (a :^: e) = ((replaceVarWithExpr v0 enew a) :^: (replaceVarExpr v0 enew e))
replaceVarWithExpr v0 enew (Prod r d spv) = Prod (replaceVarRange v0 enew r) (replaceVarWithExpr v0 enew d) spv





replaceVarRemove v0@(V vi0 sl0) e0 (Dist (V v sl) d el)
  | vi0 == v = Nothing
  | all isJust sl' = Just (Dist (V v (map fromJust sl')) d (map (replaceVarExpr v0 e0) el))
  where sl' = map (replaceVarSExpr v0 e0) sl
replaceVarRemove v0 e0 (a :*: b) =
  case (replaceVarRemove v0 e0 a, replaceVarRemove v0 e0 b) of
    (Just a', Just b') -> Just (a' :*: b')
    _                  -> Nothing
replaceVarRemove v0 e0 (a :^: e)  = 
  case (replaceVarExpr v0 e0 e, replaceVarRemove v0 e0 a) of
    (e', Just a') -> Just (a' :^: e')
    _ -> Nothing
replaceVarRemove v0 e0 (Prod r d spv) = liftM (\d' -> Prod (replaceVarRange v0 e0 r) d' spv) $ replaceVarRemove v0 e0 d



replaceVarSExpr (V v0 [] ) e0 id@(Id i _) | i /= v0 = Just id
replaceVarSExpr (V v0 [] ) e0 (Id _ Nothing) = exprToSExpr e0
replaceVarSExpr (V v0 [] ) e0 (Id _ (Just c)) =
  case exprToSExpr e0 of
    Nothing -> Nothing
    Just (Cn c0) -> Just (Cn (addConstant c0 c))
    Just (Id j Nothing) -> Just (Id j (Just c))
    Just (Id j (Just c0)) -> Just (Id j (Just (addConstant c0 c)))
replaceVarSExpr _ _ se = Just se
--replaceVarSExpr v0 e0 z = error ("Core.replaceVarSExpr: can't handle " ++ show (v0,e0,z))

replaceVarExpr v0@(V vi0 sl0) e0@(Var (V vnew [])) v@(Var (V vi sl))
  | vi0 == vi && sl0 `isPrefixOf` sl = Var (V vnew (drop (length sl0) sl))
  | all isJust sl'                   = Var (V vi $ map fromJust sl')
  | vi0 /= vi                        = Func "sub" ((Var (V vi [])) : map (replaceVarExpr v0 e0 . sexprToExpr) sl)
  | length sl0 >  length sl = error ("Core.replaceVarExpr: subA in " ++ show v0 ++ "  > subB in " ++ show v)
  | otherwise = Func "sub" (e0 : map (replaceVarExpr v0 e0 . sexprToExpr) (drop (length sl0) sl))
  where sl' = map (replaceVarSExpr v0 e0) sl
replaceVarExpr v0@(V vi0 sl0) e0 v@(Var (V vi sl))
  | vi0 /= vi && all isJust sl' = Var (V vi $ map fromJust sl')
  | vi0 /= vi                   = Func "sub" ((Var (V vi [])) : map (replaceVarExpr v0 e0 . sexprToExpr) sl)
  | length sl0 >  length sl = error ("Core.replaceVarExpr: subA in " ++ show v0 ++ "  > subB in " ++ show v)
  | length sl0 == length sl = e0
  | otherwise = Func "sub" (e0 : map (replaceVarExpr v0 e0 . sexprToExpr) (drop (length sl0) sl))
  where sl' = map (replaceVarSExpr v0 e0) sl

{-
replaceVarExpr v0@(V vi0 sl0) e0 v@(Var (V vid [])) 
  | vi0 == vid && null sl0 = e0
replaceVarExpr v0@(V vi0 sl0) e0 v@(Var (V vid sl))
  | vi0 == vid = error ("Core.replaceVarExpr: non-simple occurance (A) of lifted var " ++ show v0 ++ " in: " ++ show v)
  | null sl0 && all isJust sl' = Var (V vid (map fromJust sl'))
  | null sl0      = Func "sub" ((Var (V vid [])) : map (replaceVarExpr v0 e0 . sexprToExpr) sl)
  | sl0 == sl           = e0
  | sl0 `isPrefixOf` sl = Func "sub" (e0 : map (replaceVarExpr v0 e0 . sexprToExpr) (drop (length sl0) sl))
  | otherwise = v
  | otherwise = error ("Core.replaceVarExpr: non-simple occurance (B) of lifted var " ++ show v0 ++ " in: " ++ show v)
  where sl' = map (replaceVarSExpr v0 e0) sl
-}
replaceVarExpr v0 e0 (Con c) = Con c
replaceVarExpr v0 e0 (Func f el) = Func f $ map (replaceVarExpr v0 e0) el
replaceVarExpr v0 e0 (SP b r e spv) = SP b (replaceVarRange v0 e0 r) (replaceVarExpr v0 e0 e) spv
replaceVarExpr v0 e0 (Case cv cs) =  Case (replaceVarExpr v0 e0 cv) (map (\ (e,f) -> (replaceVarExpr v0 e0 e, replaceVarExpr v0 e0 f)) cs)

replaceVarRange v0@(V vi0 sl0) e0 r@(Range v lo hi)
  | vi0 == v  = error ("Core.replaceVarRange: lifted variable appears in range: " ++ show r)
  | otherwise = Range v (replaceVarExpr v0 e0 lo) (replaceVarExpr v0 e0 hi)
--  | null sl0  = Range v (replaceVarExpr v0 e0 lo) (replaceVarExpr v0 e0 hi)
--  | otherwise = error ("Core.replaceVarRange: non-null sl0 for " ++ show v0 ++ " in range: " ++ show r)


-- (x_{d@17,n@27},(\prod_{*8*0*@187 \in [?,?]} (Mult(z_{d@17,n@27} | sub(theta, *8*0*@187, j_{d@17})))^{=(*8*0*@187, x_{d@17,n@27})})(Mult(x_{d@17,n@27} | beta_{d@17})),[d@17 \in [D],n@27 \in [N_{d@17}]])

nameSPVars (Core dl) = Core $ evalState (mapM nameSPVarsDecl dl) 0

nameSPVarsDecl (v,d,rl) = do
  d'  <- nameSPVarsDist d
  rl' <- mapM nameSPVarsRange rl
  return (v,d',rl')

nameSPVarsDist (Dist v id el) = mapM nameSPVarsExpr el >>= return . Dist v id
nameSPVarsDist (a :*: b) = nameSPVarsDist a >>= \a' -> 
                           nameSPVarsDist b >>= \b' -> return (a' :*: b')
nameSPVarsDist (a :^: e) = nameSPVarsDist a >>= \a' -> 
                           nameSPVarsExpr e >>= \e' -> return (a' :^: e')
nameSPVarsDist (Prod r d _) = do
  name <- get
  put (name+1)
  r' <- nameSPVarsRange r
  d' <- nameSPVarsDist  d
  return (Prod r' d' ("tmpProd" ++ show name))

nameSPVarsRange (Range id e f) = nameSPVarsExpr e >>= \e' -> 
                                 nameSPVarsExpr f >>= \f' -> return (Range id e' f')

nameSPVarsExpr (Func id el) = mapM nameSPVarsExpr el >>= return . Func id
nameSPVarsExpr (SP b r e _) = do
  name <- get
  put (name+1)
  r' <- nameSPVarsRange r
  e' <- nameSPVarsExpr  e
  return (SP b r' e' ("tmpSP" ++ show name))
nameSPVarsExpr e = return e

{-
-- unnameSPVarsDecl takes sum_ sum_ e to a single sum by adding "~" around the inside spnames
unnameSPVarsDecl (v,d,rl) = (v, unnameSPVarsDist d, rl)
  where
    unnameSPVarsDist (Dist v id el) = Dist v id (map unnameSPVarsExpr el)
    unnameSPVarsDist (a :*: b) = unnameSPVarsDist a :*: unnameSPVarsDist b
    unnameSPVarsDist (a :^: e) = unnameSPVarsDist a :^: unnameSPVarsExpr e
    unnameSPVarsDist (Prod r d n) = Prod r (unnameSPVarsDist d) n

    unnameSPVarsExpr (SP b0 r0 e0 v0) =
      case unnameSPVarsExpr e0 of
        e0'@(SP b1 r1 e1 v1) | b0 == b1 ->
          let v1' = if head v1 == '~' then v1 else ('~':v1)
          in  SP b0 r0 e0' v1'
        e0' -> SP b0 r0 e0' v0
    unnameSPVarsExpr (Func f el) = Func f (map unnameSPVarsExpr el)
    unnameSPVarsExpr (Case v el) = Case v (map (\ (a,b) -> (unnameSPVarsExpr a, unnameSPVarsExpr b)) el)
    unnameSPVarsExpr e = e
-}

fixOffsets :: Core -> Core
fixOffsets (Core dl) = Core $ map fixOffsetsDecl dl

fixOffsetsDecl (v, dist, rl) = (v, fixOffsetsD dist, rl')
  where
    offsets = [filter (/=0) (getOffsets v dist ++ concatMap (getOffsetsR v) rl) | Range v _ _ <- rl]
    rl'     = zipWith (\os r -> if null os then r else applyRangeOffset (minimum os) (maximum os) r) offsets rl

fixOffsetsD (Dist v id el) = Dist v id (map fixOffsetsE el)
fixOffsetsD (a :*: b) = fixOffsetsD a :*: fixOffsetsD b
fixOffsetsD (a :^: e) = fixOffsetsD a :^: fixOffsetsE e
fixOffsetsD (Prod r@(Range v _ _) d spv) = Prod r' (fixOffsetsD d) spv
  where os = filter (/=0) $ getOffsets v d
        r' = if null os then r else applyRangeOffset (minimum os) (maximum os) r

fixOffsetsE (Func f el) = Func f $ map fixOffsetsE el
fixOffsetsE (SP b r@(Range v _ _) e spv) = SP b r' (fixOffsetsE e) spv
  where os = filter (/=0) $ getOffsetsE v e
        r' = if null os then r else applyRangeOffset (minimum os) (maximum os) r
fixOffsetsE e = e

applyRangeOffset loI hiI (Range v lo hi) = Range v lo' hi'
  where
    lo' = if loI >= 0 then lo else simp $ Func "+" [lo, Con (I (-loI))]
    hi' = if hiI <= 0 then hi else simp $ Func "-" [hi, Con (I hiI)]
    simp (Func "+" [Con (I a), Con (I b)]) = Con (I (a+b))
    simp (Func "-" [Con (I a), Con (I b)]) = Con (I (a-b))
    simp e = e

getOffsets v0 (Dist v _ el) = getOffsetsV v0 v ++ concatMap (getOffsetsE v0) el
getOffsets v0 ((:*:) a b)   = getOffsets  v0 a ++ getOffsets  v0 b
getOffsets v0 ((:^:) a e)   = getOffsets  v0 a ++ getOffsetsE v0 e
getOffsets v0 (Prod r d _)  = getOffsetsR v0 r ++ getOffsets  v0 d

getOffsetsV v0 (V _ sl) = concatMap (getOffsetsS v0) sl

getOffsetsS v0 (Id i (Just (I c))) | i == v0 = [c]
getOffsetsS _ _ = []

getOffsetsR v0 (Range _ lo hi) = getOffsetsE v0 lo ++ getOffsetsE v0 hi

getOffsetsE v0 (Var v) = getOffsetsV v0 v
getOffsetsE v0 (SP _ r e _) = getOffsetsR v0 r ++ getOffsetsE v0 e
getOffsetsE v0 (Func "+" [a, Con (I c)]) = map (+c) $ getOffsetsE v0 a
getOffsetsE v0 (Func "+" [Con (I c), a]) = map (+c) $ getOffsetsE v0 a
getOffsetsE v0 (Func "-" [a, Con (I c)]) = map (\x->x-c) $ getOffsetsE v0 a
getOffsetsE v0 (Func _ el) = concatMap (getOffsetsE v0) el
getOffsetsE v0 _ = []

filterTypeDefinitions (Core decls) = (Core d1, types)
  where
    (dt, d0) = partition isTypeDecl decls
    (dd, d1) = partition isDistDecl d0

    isTypeDecl (_, Dist _ "I" _, _) = True
    isTypeDecl (_, Dist _ "R" _, _) = True
    isTypeDecl _ = False

    isDistDecl (_, Dist _ ('I':n) _, _) | all isDigit n = True
    isDistDecl (_, Dist _ ('R':n) _, _) | all isDigit n = True
    isDistDecl _ = False

    types = [(v,0,last id, el,rl) | (v, Dist _ id el, rl) <- dt] ++
            [(v,read n :: Int,id,el,rl) | (v, Dist _ (id:n) el, rl) <- dd]

findIdOcc id0 (Var v@(V id sl)) | id0 == id = [map sexprToExpr sl]

{-
findIdOcc id0 (Func "sub" ((Var (V id sl)):el)) | id0 == id = el : rest
                                                | otherwise = rest
-}
findIdOcc id0 (Func "sub" (e:el)) = (map (++el) this) ++ rest
  where rest = concatMap (findIdOcc id0) el
        this = findIdOcc id0 e
findIdOcc id0 (Func _ el) = concatMap (findIdOcc id0) el
findIdOcc id0 (SP _ (Range _ lo hi) e _) = concatMap (findIdOcc id0) [lo,hi,e]
findIdOcc id0 (Case cv cs) = findIdOcc id0 cv ++ concatMap (findIdOcc id0.fst) cs ++ concatMap (findIdOcc id0.snd) cs
--findIdOcc id0 (Case v@(V id sl) el) | id0 == id = (map sexprToExpr sl) : rest
--                                   | otherwise = rest
--  where rest = concatMap (findIdOcc id0.fst) el ++ concatMap (findIdOcc id0.snd) el
findIdOcc id0 _ = []

sexprId (Id i _) = Just i
sexprId _ = Nothing

exprId (Var (V i _)) = Just i
exprId _ = Nothing

unliftCore :: Core -> Core
unliftCore (Core dl) = Core $ map unliftDecl dl
  where
    unliftDecl (v, d, rl) = (v, d', rl)
      where
        (rest,prods) = collectProducts [] d
        eqPairs      = collectEqs rest
        samePairs    = [(v,e) | (v,e) <- eqPairs, v `elem` prods]
        dRem         = removePairs samePairs d
        d'           = foldr (\ (v,e) -> replaceVarWithExpr (V v []) e) dRem (reverse samePairs)

    collectProducts acc d@(Prod (Range vr lo hi) d' spid) = collectProducts (vr:acc) d'
    collectProducts acc (a :*: b) = 
      let (a',acca) = collectProducts acc  a
          (b',accb) = collectProducts acca b
      in  (a' :*: b', accb)
    collectProducts acc (a :^: e) =
      let (a',acca) = collectProducts acc  a
      in  (a' :^: e, acca)
    collectProducts acc d = (d, acc)

    collectEqs (Prod _ d _) = collectEqs d
    collectEqs (a :*: b)    = collectEqs a ++ collectEqs b
    collectEqs (a :^: (Func "=" [Var (V v []), ee])) = (v,ee) : collectEqs a
    collectEqs (a :^: (Func "=" [ee, Var (V v [])])) = (v,ee) : collectEqs a
    collectEqs (a :^: _) = collectEqs a
    collectEqs d = []

    removePairs pairs (Prod (Range vr lo hi) d' spid)
      | {- lo == unkV && hi == unkV && -} vr `elem` map fst pairs = removePairs pairs d'
      | otherwise = Prod (Range vr lo hi) (removePairs pairs d') spid
    removePairs pairs (a :*: b) = removePairs pairs a :*: removePairs pairs b
    removePairs pairs (a :^: (Func "=" [Var (V v []),ee]))
      | (v,ee) `elem` pairs = removePairs pairs a
    removePairs pairs (a :^: e) = removePairs pairs a :^: e
    removePairs pairs d0@(Dist vv@(V v0 sl) id el)
--      | mytrace (show ("removePairs", d0, pairs, lookup v0 pairs)) False = undefined
      | Just (Var (V v0' sl')) <- lookup v0 pairs = Dist (V v0' (sl'++sl)) id el
      | Nothing <- lookup v0 pairs = Dist (V v0 sl') id el
      | otherwise = error $ "Core.unliftCore.removePairs: cannot remove " ++ show vv ++ " from " ++ show d0 ++ " because our lookup gave " ++ show (lookup v0 pairs) ++ " in " ++ show pairs
      where
        sl' = map (\se -> case se of 
                            Cn c   -> Cn c 
                            Id v c -> case lookup v pairs of
                                        Nothing -> Id v c
                                        Just (Var (V v' [])) -> Id v' c
                                        z -> error $ "Core.unliftCore.removePairs: lookup of " ++ show v ++ " in subexpression of " ++ show d0 ++ " yielded " ++ show z
                  ) sl
--    removePairs pairs d = d

unliftCoreE :: Core -> Core
unliftCoreE = Core . map unliftDecl . decls
  where
    unliftDecl (v,d,r) = (v,unliftDist d,r)
    unliftDist (Dist v id el) = Dist v id (map unliftE0 el)
    unliftDist (a :*: b) = unliftDist a :*: unliftDist b
    unliftDist (a :^: e) = unliftDist a :^: e
    unliftDist (Prod r d spid) = Prod r (unliftDist d) spid

    unliftE0 e@(SP False _ _ _) = unliftE e
    unliftE0 (SP b r e spid) = SP b r (unliftE0 e) spid
    unliftE0 (Func f el) = Func f (map unliftE0 el)
    unliftE0 e = e

    unliftE e0 = {- mytrace (show (("prods",prods),eqPairs,samePairs,dRem)) -} e0'
      where
        (rest,prods) = collectSums [] e0
        eqPairs      = collectEqs rest
        samePairs    = [(v,e) | (v,e) <- eqPairs, v `elem` prods]
        dRem         = removePairs samePairs e0
        e0'          = foldr (\ (v,e) -> replaceVarExpr (V v []) e) dRem (reverse samePairs)

    collectSums acc (SP False (Range vr _ _) e' spid) = collectSums (vr:acc) e'
    collectSums acc e = (e, acc)

    collectEqs (Func  "=" [Var (V v []), ee]) = [(v,ee)]
    collectEqs (Func  "*" [a,b]) = collectEqs a ++ collectEqs b
    collectEqs (Func ".*" [a,_]) = collectEqs a
    collectEqs (SP _ _ e _) = collectEqs e
    collectEqs _ = []

    removePairs pairs (SP False r@(Range vr _ _) e' spid)
      | vr `elem` map fst pairs = removePairs pairs e'
      | otherwise = SP False r (removePairs pairs e') spid
    removePairs pairs (Func  "=" [Var (V v []), ee])
      | (v,ee) `elem` pairs = Con (I 1)
    removePairs pairs (Func f el) = Func f (map (removePairs pairs) el)
    removePairs pairs e = e



{-
    unliftDecl (v, d, rl) = (v, unliftDist d, rl)
    unliftDist (Prod r@(Range vr lo hi) (d :^: e@(Func "=" [ve,ee])) spid)
      | lo == unkV && hi == unkV && ve == Var (V vr []) = unliftDist (replaceVarWithExpr (V vr []) ee d)
    unliftDist (a :*: b) = unliftDist a :*: unliftDist b
    unliftDist (a :^: e) = unliftDist a :^: e
    unliftDist (Prod r d spid) 
      | d' == d = Prod r d' spid
      | otherwise = unliftDist (Prod r d' spid)
      where d' = unliftDist d
    unliftDist d = d
-}

--removeExtraSums :: [Id] -> Core -> Core
removeExtraSums glob (Core dl)
-- | mytrace (show ("removeExtraSums", glob, dl)) True 
  = Core (map (\ (v,d,r) -> (v,resD (map (\r -> Var (V (rangeIds r) [])) r) d,r)) dl)
  where
    resD tab d0@(Dist v id el)
--      | mytrace (show ("removeExtraSums.resD(a)",tab,d0,glob)) False = undefined
      | otherwise = Dist v id (map (resE tab) el)
    resD tab (a :*: b) = resD tab a :*: resD tab b
    resD tab (a :^: e) = resD tab a :^: resE tab e
    resD tab (Prod r@(Range v0 _ _) d spid)  =
--      | mytrace (show ("removeExtraSums.resD(b)",(r, d, spid), (varEq, varEqV, tab'), (mapMaybe (\ (v,e) -> if v `elem` glob then Just e else Nothing) varEqV), (varEq `intersect` tab))) True 
      case mapMaybe (\ (v,e) -> if v `elem` glob then Just e else Nothing) varEqV of
        [] -> case varEq `intersect` tab of
                []  -> Prod r (resD tab' d) spid
                z:_ -> replaceVarWithExpr (V v0 []) z d
        z:_ -> replaceVarWithExpr (V v0 []) z d
      where
        varEq  = nub $ findEqualityD v0 d
        varEqV = mapMaybe (\x -> case x of { Var (V v _) -> Just (v,x) ; _ -> Nothing }) varEq

        tab' = (Var (V v0 [])) : tab

    resE tab e@(Var _)    = e
    resE tab e@(Con _)    = e
    resE tab (Func id el) = Func id (map (resE tab) el)
    resE tab (SP b r@(Range v0 _ _) e spid) 
      | mytrace (show ("resE",v0,varEq,tab)) False = undefined
      | otherwise =
      case mapMaybe (\ (v,e) -> if v `elem` glob then Just e else Nothing) varEqV of
        [] -> case varEq `intersect` tab of
                []  -> SP b r (resE tab' e) spid
                z:_ -> replaceVarExpr (V v0 []) z e
        z:_ -> replaceVarExpr (V v0 []) z e
      where
        varEq  = nub $ findEqualityE v0 e
        varEqV = mapMaybe (\x -> case x of { Var (V v _) -> Just (v,x) ; _ -> Nothing }) varEq

        tab' = (Var (V v0 [])) : tab
    resE tab (Case cv cs) = Case cv (map (\ (e,f) -> (resE tab e, resE tab f)) cs)

    findEqualityE v0 (Func "=" [Var (V v []), e']) | v0 == v = [e']
    findEqualityE v0 (Func "=" [e', Var (V v [])]) | v0 == v = [e']
    findEqualityE v0 (Func _ el) = concatMap (findEqualityE v0) el
    findEqualityE v0 (SP _ _ e _) = findEqualityE v0 e
    findEqualityE v0 _ = []

    findEqualityD v0 (Dist _ _ el) = concatMap (findEqualityE v0) el
    findEqualityD v0 (a :*: b) = concatMap (findEqualityD v0) [a,b]
    findEqualityD v0 (a :^: e) = findEqualityD v0 a ++ findEqualityE v0 e
    findEqualityD v0 (Prod _ d _) = findEqualityD v0 d

cval (R a) = a
cval (I a) = fromIntegral a


instance Num Const where
  I a + I b = I (a+b)
  a   + b   = R (cval a + cval b)

  I a * I b = I (a*b)
  a   * b   = R (cval a * cval b)

  I a - I b = I (a-b)
  a   - b   = R (cval a - cval b)

  negate (I a) = I (negate a)
  negate (R a) = R (negate a)
  abs (I a) = I (abs a)
  abs (R a) = R (abs a)
  signum (I a) = I (signum a)
  signum (R a) = R (signum a)
  fromInteger i = I (fromInteger i)

instance Fractional Const where
  a / b = R (cval a / cval b)
  recip a = R (recip (cval a))
  fromRational a = R (fromRational a)

instance Floating Const where
  pi = R pi
  exp = R . exp . cval
  sqrt = R . sqrt . cval
  log = R . log . cval
  a ** b = R (cval a ** cval b)
  logBase a b = R (logBase (cval a) (cval b))
  sin = R . sin . cval
  tan = R . tan . cval
  cos = R . cos . cval
  asin = R . asin . cval
  atan = R . atan . cval
  acos = R . acos . cval
  sinh = R . sinh . cval
  tanh = R . tanh . cval
  cosh = R . cosh . cval
  asinh = R . asinh . cval
  atanh = R . atanh . cval
  acosh = R . acosh . cval
