module Keelung.Compiler.Util where

import Data.IntMap (IntMap)

-- A Witness is a mapping from variables to their values
type Witness n = IntMap n
