module Keelung.Compiler.Relations.UInt
  ( UIntRelations,
    new,
    -- assign,
    -- relate,
    -- relationBetween,
    -- toMap,
    -- size,
    -- isValid,
  )
where

-- import Control.DeepSeq (NFData)
-- import Data.Map.Strict (Map)
-- import Data.Map.Strict qualified as Map
-- import GHC.Generics (Generic)
-- import Keelung.Compiler.Compile.Error
import Keelung.Compiler.Relations.EquivClass qualified as EquivClass
import Keelung.Data.Reference
import Prelude hiding (lookup)

type UIntRelations = EquivClass.EquivClass RefL Integer ()

new :: UIntRelations
new = EquivClass.new "UInt"
