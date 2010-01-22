-----------------------------------------------------------------------------
-- |
-- Module      :  MkCore
-- Project     :  HBC
-- Copyright   :  (c) Hal Daume III
-- License     :  Open
-- 
-- Maintainer  :  Hal Daume III <me@hal3.name>
-- Stability   :  stable
-- Portability :  portable
--
-- Perform all operations necessary to convert DECL to Core
--
-----------------------------------------------------------------------------

module Import where

import Decl
import Util
import Parse

import Data.Maybe
import Control.Monad
import System.IO
import Data.Generics hiding ((:*:))
import Data.Typeable
import Data.Generics.Basics
import Data.Generics.Schemes

importAll :: MOD -> IO MOD
importAll (MOD decls) = (MOD . concat) `liftM` mapM importDecl decls

importDecl :: DECL -> IO [DECL]
importDecl d@(DECL  _ _ _) = return [d]
importDecl d@(TDECL _ _ _) = return [d]
importDecl (IMPORT nam args rl) = do
  hPutStrLn stderr $ "Loading module " ++ nam ++ ".hier"
  (mod,_) <- loadHier (nam ++ ".hier")
  return (decls . everywhere (mkT addRange) 
                . everywhere (mkT renameE)
                . everywhere (mkT renameR)
                . everywhere (mkT renameLHS)
                $ mod)
  where
    get v = lookup v args
    mkV v = "imp_" ++ nam ++ "_" ++ v

    renameE (VAR v)
      | Just e <- get v = e
      | otherwise       = VAR (mkV v)
    renameE (IND v el)
      | Just (VAR v'    ) <- get v = IND v' el
      | Just (IND v' el') <- get v = IND v' (el'++el)
      | otherwise                  = IND (mkV v) el
    renameE e = e

    renameR r@(RANGE v lo hi)
      | Just (VAR v') <- get v = RANGE v' lo hi
      | Just e <- get v        = error $ "Import.renameR: cannot rename " ++ v ++ " to " ++ show e ++ " in range " ++ show r
      | otherwise              = RANGE (mkV v) lo hi

    renameLHS lhs@(LHS v sl)
      | Just (VAR v')    <- get v = LHS v' sl'
      | Just (IND v' el) <- get v,
        all isVar el              = LHS v' ((map (\ (VAR v) -> v) el) ++ sl')
      | Just e           <- get v = error $ "Import.renameLHS: cannot rename " ++ v ++ " to " ++ show e ++ " in LHS " ++ show lhs
      | otherwise                 = LHS (mkV v) sl'
      where
        sl' = map (\v -> case get v of
                           Just (VAR v') -> v'
                           Just e        -> error $ "Import.renameLHS: cannot rename " ++ v ++ " to " ++ show e ++ " in LHS " ++ show lhs
                           otherwise     -> mkV v) sl

    addRange d@(DECL lhs rhs rl0) = DECL lhs rhs ([r | r@(RANGE id _ _) <- rl, VAR id `elem` declIds d] ++ rl0)

        
