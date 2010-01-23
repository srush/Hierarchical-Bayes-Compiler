-----------------------------------------------------------------------------
-- |
-- Module      :  Devectorize
-- Project     :  HBC
-- Copyright   :  (c) Hal Daume III
-- License     :  Open
-- 
-- Maintainer  :  Hal Daume III <me@hal3.name>
-- Stability   :  stable
-- Portability :  portable
--
-- Remove all vector calls
--
-----------------------------------------------------------------------------

module HBC.Devectorize where

import HBC.Core
import HBC.Type

devecC = map devecF
devecF f 