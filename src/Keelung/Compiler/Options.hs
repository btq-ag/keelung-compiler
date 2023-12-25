{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Keelung.Compiler.Options (Options (..), defaultOptions, buildOptionsWithFieldType) where

import Control.DeepSeq
import Data.Field.Galois
import Data.Proxy
import GHC.Generics
import Keelung.Compiler.Util (gf181Info)
import Keelung.Data.FieldInfo
import Keelung.Field (FieldType)

--------------------------------------------------------------------------------

-- | Options for the compiler
data Options = Options
  { -- | Field information
    optFieldInfo :: FieldInfo,
    -- | Whether to perform constant propagation
    optConstProp :: Bool,
    -- | Whether to perform optimization
    optOptimize :: Bool,
    -- | Whether to use the new linker
    optUseNewLinker :: Bool
  }
  -- \| Whether disable testing on unoptimized program
  -- optTestOnO0 :: Bool

  deriving (Eq, Generic, NFData)

-- | Default options
defaultOptions :: Options
defaultOptions =
  Options
    { optFieldInfo = gf181Info,
      optConstProp = True,
      optOptimize = True,
      optUseNewLinker = False
      -- optTestOnO0 = True
    }

buildOptionsWithFieldType :: FieldType -> IO Options
buildOptionsWithFieldType fieldType = caseFieldType fieldType handlePrime handleBinary
  where
    handlePrime (_ :: Proxy (Prime n)) fieldInfo = return $ defaultOptions {optFieldInfo = fieldInfo}
    handleBinary (_ :: Proxy (Binary n)) fieldInfo = return $ defaultOptions {optFieldInfo = fieldInfo}