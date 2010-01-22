-----------------------------------------------------------------------------
-- |
-- Module      :  GenMatlab
-- Project     :  HBC
-- Copyright   :  (c) Hal Daume III
-- License     :  Open
-- 
-- Maintainer  :  Hal Daume III <me@hal3.name>
-- Stability   :  stable
-- Portability :  portable
--
-- Generate Matlab code
--
-----------------------------------------------------------------------------

module GenMatlab where

import Code
import qualified Core as C
import Type
import qualified Data.Map as M
import Gen
import Data.Maybe
import Data.Char
import Data.List
import Debug.Trace 

gen :: C.Core -> ShowS
gen = undefined

genS tm ind (Loop var beg end body) =
  genIndent ind . showString "for " . genId var . showString " = " 
                                    . parens (genE tm beg) . showChar ':'
                                    . parens (genE tm end) . showString ",\n" .
    genMany (genS tm (ind+1)) body .
  genIndent ind . showString "end;\n"
genS tm ind (If cond th el) =
  genIndent ind . showString "if " . genE tm cond . showString ",\n" .
    genMany (genS tm (ind+1)) th .
    (if null el then id else 
       genIndent ind . showString "else,\n" .
       genMany (genS tm (ind+1)) el) .
  genIndent ind . showString "end;\n"
genS tm ind (Assn v e) = genIndent ind . genV tm v . showString " = " . genE tm e . showString ";\n";
genS tm ind (Incr v e) = genIndent ind . genV tm v . showString " = " . genV tm v . showString " + " . genE tm e . showString ";\n";
genS tm ind (Call f ret arg) =
  genIndent ind . brackets (genMany (genE tm) ret) .
    showString " = " . genF f . (if null arg then id else parens (genMany (genE tm) arg)) .
    showString ";\n"
genS tm ind (Comment s) = genIndent ind . showString "%% " . showString s . showChar '\n'

genE tm (Var v) = genV tm v
genE tm (Con c) = genC c
genE tm (Fun f el)
  | length el == 2 && not (any isAlphaNum f) = parens (genE tm (el!!0) . genF f . genE tm (el!!1))
  | otherwise = genF f . parens (commaSep (map (genE tm) el))

genC (C.I i) = shows i
genC (C.R r) = shows r

genV tm (V id []) = genId id
genV tm (V id el) = genId id . 
                    genMany (\e -> braces (genE tm e)) (take n el) . 
                    parens (commaSep (map (genE tm) (drop n el)))
  where n = squareLength tm id

genId :: Id -> ShowS
genId = showsQuotedString True matlabOkChar
  where
    matlabOkChar = ['A'..'Z'] ++ ['a'..'z'] ++ ['0'..'9']

genF f
  | f `elem` [".+",".-",".*","./"] = showString (drop 1 f)
  | f == "="  = showString "=="
  | otherwise = showString f

-- return how many indices we have to go through before we get to a square matrix
squareLength tm id = undefined
