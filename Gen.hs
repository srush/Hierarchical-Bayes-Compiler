-----------------------------------------------------------------------------
-- |
-- Module      :  Gen
-- Project     :  HBC
-- Copyright   :  (c) Hal Daume III
-- License     :  Open
-- 
-- Maintainer  :  Hal Daume III <me@hal3.name>
-- Stability   :  stable
-- Portability :  portable
--
-- Helper functions for generating code
--
-----------------------------------------------------------------------------

module Gen where

import Data.Char
import Code

parens :: ShowS -> ShowS
parens s = showChar '(' . s . showChar ')'

brackets :: ShowS -> ShowS
brackets s = showChar '[' . s . showChar ']'

braces :: ShowS -> ShowS
braces s = showChar '{' . s . showChar '}'

commaSep :: [ShowS] -> ShowS
commaSep [] = id
commaSep [x] = x
commaSep (x:xs) = x . showString ", " . commaSep xs

genMany :: (a -> ShowS) -> [a] -> ShowS
genMany f = foldr (\a b -> b . f a) id

showsQuotedString :: Bool -> String -> String -> ShowS
showsQuotedString initCapOk okChar = showString . fixCap . concatMap replaceChar 
  where
    replaceChar c
      | c `elem` okChar = [c]
      | numbersOkay     = show (ord c)
      | lowercaseOkay   = show (map numToLC $ show $ ord c)
      | uppercaseOkay   = show (map (toUpper.numToLC) $ show $ ord c)
      | otherwise       = error ("Gen.showsQuotedString: cannot show character " ++ show c)
    fixCap [] = []
    fixCap (c:cs) | isUpper c && not initCapOk = "lc_" ++ (c:cs)
                  | otherwise = c:cs
    numToLC = chr . (+17) . ord
    numbersOkay   = all (`elem` okChar) ['0'..'9']
    uppercaseOkay = all (`elem` okChar) ['A'..'Z']
    lowercaseOkay = all (`elem` okChar) ['a'..'z']

genIndent ind = showString (replicate (ind*2) ' ')


