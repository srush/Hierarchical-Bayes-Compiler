-----------------------------------------------------------------------------
-- |
-- Module      :  Translate
-- Project     :  HBC
-- Copyright   :  (c) Hal Daume III
-- License     :  Open
-- 
-- Maintainer  :  Hal Daume III <me@hal3.name>
-- Stability   :  stable
-- Portability :  portable
--
-- Translate lifted, re-indexed markov Blankets
--
-----------------------------------------------------------------------------

module Translate where

import Decl
import Core
import Util
import Control.Monad

translateExpr :: EXPR -> Expr
translateExpr (VAR   v    ) = Var  (V v [])
translateExpr (IND   v el ) = Var  (V v $ map translateSExpr el)
translateExpr (FN    f el ) = Func f $ map translateExpr el
translateExpr (SUMPP b r e) = SP   b (translateRange r) (translateExpr e) ""
translateExpr (CONST c    ) = Con  (translateConst c)
translateExpr (CASE  cv cs) = Case (translateExpr cv) (map (\ (e,f) -> (translateExpr e, translateExpr f)) cs)

translateSExpr :: EXPR -> SExpr
translateSExpr (VAR v) = Id v Nothing
translateSExpr (CONST (INT  c)) = Cn (I c)
translateSExpr (CONST (REAL c)) = Cn (R c)
translateSExpr f@(FN _ _) = 
  case evalFn Nothing f of
    (Just v, c) -> Id v (liftM translateConst c)
    (Nothing, Nothing) -> Cn (I 0)
    (Nothing, Just c)  -> Cn (translateConst c)
translateSExpr z = error ("Translate.translateSExpr: cannot translate '" ++ show z ++ "' into a simple expression")

translateRange :: RANGE -> Range
translateRange (RANGE v lo hi) = Range v (translateExpr lo) (translateExpr hi)

translateConst :: CONST -> Const
translateConst (INT  i) = I i
translateConst (REAL r) = R r
