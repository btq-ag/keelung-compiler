module Keelung.Compiler.Compile.Limb where

import Data.Field.Galois (GaloisField)
import Data.Sequence (Seq)
import Data.Sequence qualified as Seq
import Keelung.Compiler.Constraint
import Keelung.Syntax (HasWidth (widthOf), Width)

--------------------------------------------------------------------------------

data Limb = Limb
  { -- | Which RefU this limb belongs to
    lmbRef :: RefU,
    -- | How wide this limb is
    lmbWidth :: Width,
    -- | The offset of this limb
    lmbOffset :: Int,
    -- | Left: Sign of all bits
    -- | Right: Signs of each bit, LSB first
    lmbSigns :: Either Bool [Bool]
  }
  deriving (Show)

-- | A limb is considered "positive" if all of its bits are positive
limbIsPositive :: Limb -> Bool
limbIsPositive limb = case lmbSigns limb of
  Left sign -> sign
  Right signs -> and signs

-- | Construct a sequence of (Ref, n) pairs from a limb
toBitsC :: (GaloisField n, Integral n) => Int -> Bool -> Limb -> n -> Seq (Ref, n)
toBitsC powerOffset positive limb multiplyBy =
  let makePair sign i =
        ( B (RefUBit (widthOf (lmbRef limb)) (lmbRef limb) (lmbOffset limb + i)),
          multiplyBy
            * if (if sign then positive else not positive)
              then 2 ^ (powerOffset + i :: Int)
              else -(2 ^ (powerOffset + i :: Int))
        )
   in Seq.fromList $
        case lmbSigns limb of
          Left sign ->
            map
              (makePair sign)
              [0 .. lmbWidth limb - 1]
          Right signs ->
            zipWith
              makePair
              signs
              [0 .. lmbWidth limb - 1]

toBits :: (GaloisField n, Integral n) => Int -> Bool -> Limb -> Seq (Ref, n)
toBits powerOffset positive limb = toBitsC powerOffset positive limb 1
