module Keelung.Compiler.Syntax.BinRep where

import Data.IntMap (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.Set (Set)
import qualified Data.Set as Set
import Keelung.Types (Var)

--------------------------------------------------------------------------------

-- | Relation between a variable and binary representation
data BinRep = BinRep
  { -- | The variable
    binRepVar :: Var,
    -- | Bit width info of the variable
    binRepBitWidth :: Int,
    -- | The starting index of the binary representation
    binRepBitsIndex :: Var,
    -- | How much the view of binary representation as been rotated
    binRepRotates :: Int
  }
  deriving (Eq)

instance Show BinRep where
  show (BinRep var 1 index _) = "$" <> show var <> " = $" <> show index
  show (BinRep var 2 index r) = case r `mod` 2 of
    0 -> "$" <> show var <> " = $" <> show index <> " + 2$" <> show (index + 1)
    _ -> "$" <> show var <> " = $" <> show (index + 1) <> " + 2$" <> show index
  show (BinRep var 3 index r) = case r `mod` 3 of
    0 -> "$" <> show var <> " = $" <> show index <> " + 2$" <> show (index + 1) <> " + 4$" <> show (index + 2)
    1 -> "$" <> show var <> " = $" <> show (index + 2) <> " + 2$" <> show index <> " + 4$" <> show (index + 1)
    _ -> "$" <> show var <> " = $" <> show (index + 1) <> " + 2$" <> show (index + 2) <> " + 4$" <> show index
  show (BinRep var 4 index r) = case r `mod` 4 of
    0 -> "$" <> show var <> " = $" <> show index <> " + 2$" <> show (index + 1) <> " + 4$" <> show (index + 2) <> " + 8$" <> show (index + 3)
    1 -> "$" <> show var <> " = $" <> show (index + 3) <> " + 2$" <> show index <> " + 4$" <> show (index + 1) <> " + 8$" <> show (index + 2)
    2 -> "$" <> show var <> " = $" <> show (index + 2) <> " + 2$" <> show (index + 3) <> " + 4$" <> show index <> " + 8$" <> show (index + 1)
    _ -> "$" <> show var <> " = $" <> show (index + 1) <> " + 2$" <> show (index + 2) <> " + 4$" <> show (index + 3) <> " + 8$" <> show index
  show (BinRep var w index r) =
    let w' = r `mod` w
     in "$" <> show var <> " = $" <> show (index + w - w') <> " + 2$" <> show (index + w - w' + 1) <> " + ... + 2^" <> show (w - 1) <> "$" <> show (index + w - w' - 1)

instance Ord BinRep where
  compare (BinRep x _ _ _) (BinRep y _ _ _) = compare x y

--------------------------------------------------------------------------------

-- | A collection of BinReps sorted according to their bitwidth
type BinReps = IntMap (Set BinRep)

toBinReps :: [BinRep] -> BinReps
toBinReps = foldl (\acc binRep -> IntMap.insertWith (<>) (binRepBitWidth binRep) (Set.singleton binRep) acc) mempty

mergeBinReps :: BinReps -> BinReps -> BinReps
mergeBinReps = IntMap.unionWith (<>)