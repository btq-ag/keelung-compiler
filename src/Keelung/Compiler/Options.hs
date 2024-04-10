{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Keelung.Compiler.Options (Options (..), new, defaultOptions, buildOptionsWithFieldType) where

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
    optOptimize :: Bool
  }
  deriving (Eq, Generic, NFData)

-- | Create new options with the given field type
new :: FieldType -> Options
new fieldType = Options {optFieldInfo = fromFieldType fieldType, optConstProp = True, optOptimize = True}

-- | Default options
defaultOptions :: Options
defaultOptions =
  Options
    { optFieldInfo = gf181Info,
      optConstProp = True,
      optOptimize = True
    }

buildOptionsWithFieldType :: FieldType -> IO Options
buildOptionsWithFieldType fieldType = caseFieldType fieldType handlePrime handleBinary
  where
    handlePrime (_ :: Proxy (Prime n)) fieldInfo = return $ defaultOptions {optFieldInfo = fieldInfo}
    handleBinary (_ :: Proxy (Binary n)) fieldInfo = return $ defaultOptions {optFieldInfo = fieldInfo}