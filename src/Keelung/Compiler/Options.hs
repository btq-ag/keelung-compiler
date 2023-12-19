module Keelung.Compiler.Options (Options (..), defaultOptions) where

import Keelung.Compiler.Util (gf181Info)
import Keelung.Data.FieldInfo

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

-- | Default options
defaultOptions :: Options
defaultOptions =
  Options
    { optFieldInfo = gf181Info,
      optConstProp = True,
      optOptimize = True,
      optUseNewLinker = False
    }