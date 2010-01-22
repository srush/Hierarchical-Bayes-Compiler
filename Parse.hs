-----------------------------------------------------------------------------
-- |
-- Module      :  Parse
-- Project     :  HBC
-- Copyright   :  (c) Hal Daume III
-- License     :  Open
-- 
-- Maintainer  :  Hal Daume III <me@hal3.name>
-- Stability   :  stable
-- Portability :  portable
--
-- Parsing of DECLarations
--
-----------------------------------------------------------------------------

module Parse(parse,loadHier) where

-- parseTest decl "a_{k} ~ Mult(5) , {- jdsk -} x \\in [  1,20] ; foo ~ Dir(x)"
-- parseTest decl "a_{k} ~ Mult(case k of { 0 :> 5 ; 1 :> 6 }), k \\in [1,K]"
import Data.List
import Data.Maybe
import Data.Char
import Text.ParserCombinators.Parsec hiding (parse)
import qualified Text.ParserCombinators.Parsec as P
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import Text.ParserCombinators.Parsec.Token
import System
import System.IO
import Decl
import Control.Monad
--import System.IO.Unsafe

loadHier :: FilePath -> IO (MOD, [String])
loadHier "-" = getContents >>= parse "stdin"
loadHier fn  = readFile fn >>= parse fn

parse :: SourceName -> String -> IO (MOD, [String])
parse source str =
  case P.parse code source (addSemis str) of
    Left err -> hPutStrLn stderr (show err) >> exitWith (ExitFailure 1)
    Right d  -> return (MOD d, extractDirectives str)


hbcDef :: LanguageDef st
hbcDef = LanguageDef
           { commentStart    = "{-"
           , commentEnd      = "-}"
           , commentLine     = "--"
           , nestedComments  = True
           , identStart      = letter <|> char '\\'
           , identLetter     = alphaNum <|> oneOf "'\\"
           , opStart         = opLetter hbcDef
           , opLetter        = oneOf ":!#$%&*+./<=>?@-^|"
           , caseSensitive   = True
           , reservedNames   = ["\\prod", "\\sum", "\\in", "case", "of", "import"]
           , reservedOpNames = [":>"]
           }

lx :: TokenParser st
lx = makeTokenParser hbcDef

code = semiSep1 lx decl >>= \x -> eof >> return x

decl = (do
  reserved lx "import"
  whiteSpace lx
  nam  <- identifier lx
  whiteSpace lx
  args <- parens lx (commaSep1 lx varExpr)
  whiteSpace lx
  rl   <- many (whiteSpace lx >> comma lx >> range)
  whiteSpace lx
  return (IMPORT nam args rl)) <|> declNonImport
  where
    varExpr = do
      whiteSpace lx
      v <- identifier lx
      whiteSpace lx
      reservedOp lx ":>"
      whiteSpace lx
      e <- expr
      whiteSpace lx
      return (v,e)

declNonImport = do
  whiteSpace lx
  l <- lhs
  whiteSpace lx
  mkD <- (do char '~'
             whiteSpace lx
             r <- rhs
             return (\rl -> DECL l r rl)) <|>
         (do reserved lx "\\in"
             whiteSpace lx
             type0 <- parseType
             return (\rl -> TDECL l type0 rl)) <|>
         (do comma lx
             whiteSpace lx
             (LHS v0 vl) <- lhs
             whiteSpace lx
             char '~'
             whiteSpace lx
             r@(RHS dist el lift) <- rhs
             when (dist /= "PY") $ error ("two variables not allowed on RHS of " ++ dist)
             return (\rl -> DECL l (RHS dist (el++[IND v0 (map VAR vl)]) lift) rl))
  whiteSpace lx
  g <- many (whiteSpace lx >> comma lx >> range)
  whiteSpace lx
  return (mkD g)

parseType = (do
  type0 <- oneOf "ZIR"
  let type0' = if type0 == 'Z' then 'I' else type0
  s <- option [] (char '_' >> braces lx (commaSep1 lx expr))
  return (0, type0, s)
  ) <|> (do
  string "dist("
  whiteSpace lx
  t <- parseType
  whiteSpace lx
  char ')'
  case t of
    (i, type0, s) -> return (i+1, type0, s)
  )

lhs = do
  whiteSpace lx
  id <- identifier lx
  s  <- option [] (char '_' >> braces lx (commaSep1 lx (identifier lx)))
  whiteSpace lx
  return (LHS id s)

rhs = do
  dist <- identifier lx
  args <- parens lx (commaSep lx expr)
  return (RHS dist args [])

range = do
  whiteSpace lx
  id <- identifier lx
  whiteSpace lx
  string "\\in"
  whiteSpace lx
  range <- brackets lx (commaSep1 lx expr)
  (lo,hi) <- case range of
               [lo,hi] -> return (lo,hi)
               _ -> unexpected ("ranges must have only two options, not " ++ show (length range) ++ " as in " ++ show range)
  whiteSpace lx
  return (RANGE id lo hi)

expr = buildExpressionParser opTable term
  where
    opTable =
      [ [ Postfix sub ]
      , [ Postfix arguments ]
      , [ Infix equal AssocLeft ]
      , [ Infix timesDivide AssocLeft ]
      , [ Infix plusMinus AssocLeft ]
      ]

term = 
  whiteSpace lx >>
  (   try sumProduct
  <|> try caseOf
  <|> try (float lx      >>= return . CONST . REAL)
  <|> (integer lx    >>= return . CONST . INT)
  <|> (identifier lx >>= return . VAR)
  <|> (parens lx expr)
  <|> (char '#' >> integer lx >>= return . VAR . ('#':) . show)
  ) >>= \x -> whiteSpace lx >> return x

caseOf = do
  reserved lx "case"
  whiteSpace lx
--  id0 <- identifier lx
--  ids <- option [] (char '_' >> braces lx (commaSep1 lx (identifier lx)))
--  let cv = if null ids then VAR id0 else IND id0 (map VAR ids)
  cv <- expr
  whiteSpace lx
  reserved lx "of"
  whiteSpace lx
  cases <- braces lx (semiSep1 lx caseOfCases)
  return (CASE cv cases)

caseOfCases = do
  whiteSpace lx
  e <- expr
  whiteSpace lx
  reservedOp lx ":>"
  whiteSpace lx
  f <- expr
  return (e,f)


sumProduct = do
  sp <- (reserved lx "\\sum" >> return False) <|> (reserved lx "\\prod" >> return True)
  string "_{"
  whiteSpace lx
  r <- range
  whiteSpace lx
{-  whiteSpace lx
  i <- identifier lx
  whiteSpace lx
  char '='
  whiteSpace lx
  lo <- expr
  whiteSpace lx
  string "}^{"
  whiteSpace lx
  hi <- expr
  whiteSpace lx -}
  char '}'
  whiteSpace lx
  e <- expr
  whiteSpace lx
  return (SUMPP sp r e)
  

sub = char '_' >> braces lx ((commaSep1 lx) expr) >>= \l -> 
        return (\x -> case x of
                        VAR v -> IND v l
                        _ -> error ("Indices can only be applied to plain variables\n\t\tYou tried to apply " ++ show l ++ " to " ++ show x)
               )

arguments = parens lx ((commaSep1 lx) expr) >>= \l ->
        return (\x -> case x of
                        VAR v -> FN v l
                        _ -> error ("Only plain variables can stand in as functions\n\t\tYou tried to apply " ++ show l ++ " to " ++ show x)
               )

equal = 
  (string "=" <|> string "~=" <|> try (string "<=") <|> string "<" <|> try (string ">=") <|> string ">" <|> string "||" <|> string "&&") 
  >>= \op -> return (\l r -> FN op [l,r])

timesDivide =
  ((string "*" <|> string "/" <|> try (string ".*") <|> try (string "./") <|> string "^")
       >>= \op -> return (\l r -> FN op [l,r]))

plusMinus = 
  ((string "+" <|> string "-" <|> try (string ".+") <|> try (string ".-"))
       >>= \op -> return (\l r -> FN op [l,r]))

addSemis :: String -> String
addSemis = removeLastNL . unlines . addSemis' . map removeEOLComments . lines . removeLastNL
  where
    addSemis' []  = []
    addSemis' (x:xs) | all isSpace x = "" : addSemis' xs
    addSemis' [x] = [x]
    addSemis' (x:xs) =
      let i    = length (takeWhile isSpace x)
          this = x : takeWhile (\y -> length (takeWhile isSpace y) > i) xs
          rest = drop (length this-1) xs
      in  case addSemis' rest of
            [] -> this
            l  -> init this ++ [(last this) ++ " ;"] ++ l

    removeEOLComments [] = []
    removeEOLComments ('-':'-':xs) = []
    removeEOLComments (x:xs) = x : removeEOLComments xs

    removeLastNL = reverse . dropWhile (`elem` " \n\t;") . reverse


extractDirectives :: String -> [String]
extractDirectives = concat . mapMaybe findDirective . lines
  where
    findDirective x
      | "--#" `isPrefixOf` x' = Just (words $ dropWhile isSpace $ drop 3 x')
      | otherwise = Nothing
      where x' = dropWhile isSpace x



detex :: String -> String
detex = unlines . reverse . detex' False [] . map (dropWhile isSpace) . lines
  where
    detex' isIn acc [] = acc
    detex' isIn acc (('%':_):xs) = detex' isIn acc xs
    detex' isIn acc (x:xs)
      | "\\begin{hbc}" `isPrefixOf` x = detex' True  acc xs
      | "\\end{hbc}"   `isPrefixOf` x = detex' False acc xs
    detex' True acc (x:xs) = detex' True  (x:acc) xs
    detex' _    acc (_:xs) = detex' False acc     xs
