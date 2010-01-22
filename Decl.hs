-----------------------------------------------------------------------------
-- |
-- Module      :  Decl
-- Project     :  HBC
-- Copyright   :  (c) Hal Daume III
-- License     :  Open
-- 
-- Maintainer  :  Hal Daume III <me@hal3.name>
-- Stability   :  stable
-- Portability :  portable
--
-- The Decl module: implements the base declarations for the HBC
-- system, plus various utilities for traversing and extracting information
-- from these declarations
--
-----------------------------------------------------------------------------

module Decl where

import Data.Maybe
import Data.Generics hiding ((:*:))
import Data.Typeable
import Data.Generics.Basics
import Data.Generics.Schemes

type VAR   = String
type DIST  = String
type TYPE0 = (Int, Char, [EXPR])
data CONST = INT Integer | REAL Double                 deriving (Eq, Ord, Typeable, Data)
data DECL  = DECL   LHS RHS    [RANGE]                     
           | TDECL  LHS TYPE0  [RANGE]
           | IMPORT VAR [(VAR,EXPR)] [RANGE]           deriving (Eq, Ord, Typeable, Data)
data LHS   = LHS   VAR [VAR]                           deriving (Eq, Ord, Typeable, Data)
data RHS   = RHS   DIST [EXPR] LIFT                    deriving (Eq, Ord, Typeable, Data)  -- lift cannot be specified by grammar; is a result of Lift.lift
data RANGE = RANGE VAR EXPR EXPR                       deriving (Eq, Ord, Typeable, Data)
data EXPR  = VAR   VAR
           | IND   VAR [EXPR]
           | FN    VAR [EXPR]    -- fold OP in here
           | SUMPP Bool RANGE EXPR   -- false = sum
           | CASE  EXPR [(EXPR,EXPR)]    -- CASE variable OF [(value, result)]
           | CONST CONST                               deriving (Eq, Ord, Typeable, Data)
data MOD   = MOD { decls :: [DECL] }                   deriving (Eq, Ord, Typeable, Data)
type LIFT  = [(EXPR,EXPR)]  -- initially (VAR,EXPR), but reindex may change the first to an expr

isDecl (DECL _ _ _) = True
isDecl _ = False

isTDecl (TDECL _ _ _) = True
isTDecl _ = False

isImport (IMPORT _ _ _) = True
isImport _ = False

-- Make everything an instance of show with some reasonable description:
instance Show CONST where 
  showsPrec i (INT  j) = showsPrec i j
  showsPrec i (REAL j) = showsPrec i j

instance Show DECL where
  showsPrec i decl =
    case decl of
      DECL   lhs rhs         range -> showsPrec i lhs . showString " ~ "    . showsPrec i rhs . showsRange range
      TDECL  lhs (0,typ0,[])   range -> showsPrec i lhs . showString " \\in " . showChar typ0    . showsRange range
      TDECL  lhs (0,typ0,el)   range -> showsPrec i lhs . showString " \\in " . showChar typ0 . showChar '_' . shows el . showsRange range
      TDECL  lhs (i,typ0,[]) range -> showsPrec i lhs . showString " \\in dist^" . shows i . showChar '(' . showChar typ0    . showsRange range . showChar ')'
      TDECL  lhs (i,typ0,el) range -> showsPrec i lhs . showString " \\in dist^" . shows i . showChar '(' . showChar typ0  . showChar '_' . shows el . showsRange range . showChar ')'
      IMPORT nam ((v,a):ars) range -> showString "import " . showString nam . showChar '(' . showString v . showString " :> " . showsPrec i a . showsArgs ars . showChar ')' . showsRange range
    where
      showsRange [] = id
      showsRange (x:xs) = showString " , " . showsPrec i x . showsRange xs
      showsArgs [] = id
      showsArgs ((v,a):ars) = showString ", " . showString v . showString " :> " . showsPrec i a . showsArgs ars

instance Show LHS where
  showsPrec i (LHS v []) = showString v
  showsPrec i (LHS v (x:l)) = showString v . showString "_{" . showString x . showsIx l . showChar '}'
    where
      showsIx [] = id
      showsIx (x:xs) = showChar ',' . showString x . showsIx xs

instance Show RHS where
  showsPrec i (RHS d [] []) = showString d . showString "()"
  showsPrec i (RHS d (x:l) lift) = liftA lift . showString d . showChar '(' . showsPrec i x . showsPa l . showChar ')' . liftB lift
    where
      showsPa [] = id
      showsPa (x:xs) = showString ", " . showsPrec i x . showsPa xs

      liftA [] = id
      liftA ((new,old):xs) = showsPrec i (SUMPP True (RANGE (show new) (VAR "?") (VAR "?")) (VAR "")) . liftA xs

      liftB [] = id
      liftB ((new,old):xs) = showString "^{" . showsPrec i new . showChar '=' . showsPrec i old . showChar '}' . liftB xs

instance Show RANGE where
  showsPrec i (RANGE v lo hi) = showString v . showString " \\in [" . showsPrec i lo . showChar ',' . showsPrec i hi . showChar ']'

instance Show EXPR where
  showsPrec i (VAR v) = showString v
  showsPrec i (IND v []) = showString v
  showsPrec i (IND v (x:l)) = showString v . showString "_{" . showsPrec i x . showsIx l . showChar '}'
    where
      showsIx [] = id
      showsIx (x:xs) = showChar ',' . showsPrec i x . showsIx xs
  showsPrec i (FN v (x:l)) = showString v . showChar '(' . showsPrec i x . showsIx l . showChar ')'
    where
      showsIx [] = id
      showsIx (x:xs) = showString ", " . showsPrec i x . showsIx xs
  showsPrec i (SUMPP prod (RANGE v lo hi) e) = showChar '\\' . (if prod then showString "prod" else showString "sum") . showString "_{" . showString v . showChar '=' . showsPrec i lo . showString "}^{" . showsPrec i hi . showString "} " . showsPrec i  e
  showsPrec i (CONST c) = showsPrec i c
  showsPrec i (CASE cv cs) = showString "case " . shows cv . showString " of {" . showCases cs . showString " }"
    where
      showCases [] = id
      showCases ((e,r):rs) = showChar ' ' . showsPrec i e . showString " :> " . showsPrec i r . if null rs then id else (showString " ;" . showCases rs)

instance Show MOD where
  showsPrec i (MOD []) = id
  showsPrec i (MOD (x:l)) = showsPrec i x . showChar '\n' . showsPrec i (MOD l)

-- -----------------------------------------------------------------------------

-- | extract all ids from various types
declIds  (DECL   lhs rhs  rl) = lhsIds lhs ++ rhsIds rhs ++ concatMap rangeIds rl
declIds  (TDECL  lhs _    rl) = lhsIds lhs ++ concatMap rangeIds rl
declIds  (IMPORT _   args rl) = concatMap (exprIds.snd) args ++ concatMap rangeIds rl
lhsIds   (LHS   v vl)       = map VAR (v:vl)
rhsIds   (RHS   _ pa lift)  = concatMap exprIds pa ++ concatMap liftIds lift
rangeIds (RANGE v lo hi)    = (VAR v) : exprIds lo ++ exprIds hi
exprIds  (VAR   v)          = [VAR v]
exprIds  (IND   v sub)      = (IND v sub) : concatMap exprIds sub
exprIds  (FN    f pa)       = concatMap exprIds pa
exprIds  (SUMPP _ r e)      = rangeIds r ++ exprIds e
exprIds  (CONST _)          = []
exprIds  (CASE cv cs)       = exprIds cv ++ concatMap (\ (e,f) -> exprIds e ++ exprIds f) cs
modIds   (MOD   decls)      = concatMap declIds decls
liftIds  (v,e)              = exprIds v ++ exprIds e

isVar (VAR _) = True
isVar _ = False

exprVars = mapMaybe (\x -> case x of { VAR v -> Just v ; _ -> Nothing }) . exprIds

-- -----------------------------------------------------------------------------

-- | evaluate a function as far as possible (for generating simple expressions)

evalFn :: Maybe CONST -> EXPR -> (Maybe VAR, Maybe CONST)
evalFn c0 (VAR v) = (Just v, c0)
evalFn c0 f@(FN op [a,b]) =
  case (evalFn c0 a, evalFn Nothing b) of
    ((Nothing,cA),(v,cB)) -> (v, evalOp op cA cB)
    ((v,cA),(Nothing,cB)) -> (v, evalOp op cA cB)
    ((Just _,_),(Just _,_)) -> error ("Decl.evalFn: both LHS and RHS have variables in: " ++ show f)
evalFn c0 (IND v []) = (Just v,c0)
evalFn c0 (CONST c) = (Nothing, Just c)
evalFn _ z = error ("Decl.evalFn: cannot evaluate: " ++ show z)

evalOp "+" a Nothing = a
evalOp "+" Nothing a = a
evalOp "-" a Nothing = a
evalOp "-" Nothing (Just (INT  i)) = Just (INT  (-i))
evalOp "-" Nothing (Just (REAL r)) = Just (REAL (-r))
evalOp "+" (Just (INT  i)) (Just (INT  j)) = Just (INT  (i+j))
evalOp "+" (Just (INT  i)) (Just (REAL j)) = Just (REAL ((fromIntegral i)+j))
evalOp "+" (Just (REAL i)) (Just (INT  j)) = Just (REAL (i+(fromIntegral j)))
evalOp "+" (Just (REAL i)) (Just (REAL j)) = Just (REAL (i+j))
evalOp "-" (Just (INT  i)) (Just (INT  j)) = Just (INT  (i-j))
evalOp "-" (Just (INT  i)) (Just (REAL j)) = Just (REAL ((fromIntegral i)-j))
evalOp "-" (Just (REAL i)) (Just (INT  j)) = Just (REAL (i-(fromIntegral j)))
evalOp "-" (Just (REAL i)) (Just (REAL j)) = Just (REAL (i-j))
evalOp op  a b = error ("Decl.evalOp: cannot evalute op '" ++ op ++ "' applied to " ++ show (a,b))


-----------------------------------------------------------------------------

replaceVar v0 e0 (DECL   lhs rhs  rl) = DECL   lhs (replaceVarRHS v0 e0 rhs) (map (replaceVarR v0 e0) rl)
replaceVar v0 e0 (TDECL  lhs typ  rl) = TDECL  lhs typ (map (replaceVarR v0 e0) rl)
replaceVar v0 e0 (IMPORT nam args rl) = IMPORT nam (map (\ (v,a) -> (v, replaceVarE v0 e0 a)) args) (map (replaceVarR v0 e0) rl)

replaceVarRHS v0 e0 (RHS dist el lf) = RHS dist (map (replaceVarE v0 e0) el) (map (replaceVarL v0 e0) lf)

replaceVarE v0 e0 (VAR v)    | v == v0   = e0
                             | otherwise = VAR v
replaceVarE v0 e0 (IND v el) | v == v0   = FN "sub" (e0 : map (replaceVarE v0 e0) el)
                             | otherwise = IND v (map (replaceVarE v0 e0) el)
replaceVarE v0 e0 (FN v el)              = FN  v (map (replaceVarE v0 e0) el)
replaceVarE v0 e0 (SUMPP b r e) = SUMPP b (replaceVarR v0 e0 r) (replaceVarE v0 e0 e)
replaceVarE v0 e0 (CONST c)     = CONST c
replaceVarE v0 e0 (CASE cv cs)  = CASE (replaceVarE v0 e0 cv) (map (\ (e,f) -> (replaceVarE v0 e0 e, replaceVarE v0 e0 f)) cs)

replaceVarR v0 e0 (RANGE v lo hi) = RANGE v (replaceVarE v0 e0 lo) (replaceVarE v0 e0 hi)

replaceVarL v0 e0 (e,f) = (replaceVarE v0 e0 e, replaceVarE v0 e0 f)
