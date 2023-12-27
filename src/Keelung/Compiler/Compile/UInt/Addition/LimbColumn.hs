module Keelung.Compiler.Compile.UInt.Addition.LimbColumn (LimbColumn, View (..), new, singleton, trim, view, insert) where

import Data.Sequence (Seq, (<|))
import Data.Sequence qualified as Seq
import Keelung.Data.Limb (Limb (..))
import Keelung.Data.Limb qualified as Limb

--------------------------------------------------------------------------------

-- | A 'LimbColumn' is a sequence of 'Limb's, with a constant value.
data LimbColumn = LimbColumn Integer (Seq Limb)
  deriving (Show, Eq)

instance Semigroup LimbColumn where
  (LimbColumn const1 limbs1) <> (LimbColumn const2 limbs2) =
    LimbColumn (const1 + const2) (limbs1 <> limbs2)

instance Monoid LimbColumn where
  mempty = LimbColumn 0 mempty

--------------------------------------------------------------------------------

-- | Create a 'LimbColumn' from a constant and a list of 'Limb's.
new :: Integer -> [Limb] -> LimbColumn
new c xs = LimbColumn c (Seq.fromList xs)

-- | Create a 'LimbColumn' with a single 'Limb'.
singleton :: Limb -> LimbColumn
singleton x = LimbColumn 0 (pure x)

-- | Insert a 'Limb' into a 'LimbColumn'.
insert :: Limb -> LimbColumn -> LimbColumn
insert x (LimbColumn c xs) = LimbColumn c (x <| xs)

-- | Trim all Limbs in a 'LimbColumn' to a given width.
trim :: Int -> LimbColumn -> LimbColumn
trim width (LimbColumn c xs) = LimbColumn c (fmap (Limb.trim width) xs)

--------------------------------------------------------------------------------

data View
  = Ordinary Integer (Seq Limb)
  | OneLimbOnly Limb
  | OneConstantOnly Integer
  deriving (Show, Eq)

-- | Split a column of limbs into a stack of limbs and the rest of the column
-- Let `H` be the maximum batch size allowed
--    if all limbs are negative
--      then we can only add `H-1` limbs up at a time
--      else we can add all `H` limbs up at a time
view :: Int -> LimbColumn -> (View, Maybe LimbColumn)
view _ (LimbColumn constant Seq.Empty) = (OneConstantOnly constant, Nothing)
view _ (LimbColumn constant (limb Seq.:<| Seq.Empty)) =
  if constant == 0 && Limb.isPositive limb
    then (OneLimbOnly limb, Nothing)
    else (Ordinary constant (Seq.singleton limb), Nothing)
view maxHeight (LimbColumn constant limbs) =
  let (currentBatch, nextBatch) = Seq.splitAt (maxHeight - 1) limbs
      currentBatchAllNegative = not (any Limb.isPositive currentBatch)
   in if currentBatchAllNegative
        then (Ordinary constant currentBatch, if Seq.null nextBatch then Nothing else Just (LimbColumn 0 nextBatch))
        else -- we can take 1 more limb from the next batch, because not all limbs are negative
        case Seq.viewl nextBatch of
          Seq.EmptyL -> (Ordinary constant currentBatch, Nothing)
          nextBatchHead Seq.:< nextBatchTail ->
            ( Ordinary constant (currentBatch Seq.|> nextBatchHead),
              if Seq.null nextBatchTail
                then Nothing
                else Just (LimbColumn 0 nextBatchTail)
            )
