-----------------------------------------------------------------------------
-- |
-- Module      :  Blanket
-- Project     :  HBC
-- Copyright   :  (c) Hal Daume III
-- License     :  Open
-- 
-- Maintainer  :  Hal Daume III <me@hal3.name>
-- Stability   :  stable
-- Portability :  portable
--
-- Find the Markov blanket for a given definition
--
-----------------------------------------------------------------------------
module Blanket(blanket) where

import Decl
import Util
import Data.List

-- | blanket takes a module and an int specifying which declaration in
-- | the module we care about.  it returns the set of all RHSs in
-- | which the variable under consideration appears, plus the form it
-- | appears in.  in particular, if the variable is z_n, and we find
-- | both z_n and z_{n+1} on the RHS of some declaration, then we
-- | return this index *twice*, once with z_n as the corresponding
-- | expression, and once with z_{n+1}

blanket :: MOD -> Int -> [(Int,EXPR)]
blanket (MOD decls) ii = 
  [(jj,expr) | (jj,decl) <- number decls     -- get all declarations, including our own
             , case decl of { DECL _ _ _ -> True ; _ -> False }
             , let DECL _ rhs rl = decl
             , expr <- nub (rhsIds rhs ++ concatMap rangeIds rl)    -- get the ids mentioned in this declaration
             , case expr of { VAR v -> v == v0 ; IND v _ -> v == v0 ; _ -> False } -- make sure we're there
             ]
  where
    v0 = case decls !! ii of
           DECL  (LHS v0 _) _ _ -> v0
           TDECL (LHS v0 _) _ _ -> v0


