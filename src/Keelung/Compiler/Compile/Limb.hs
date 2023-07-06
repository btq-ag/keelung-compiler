module Keelung.Compiler.Compile.Limb where

import Data.Field.Galois (GaloisField)
import Data.Sequence (Seq)
import Data.Sequence qualified as Seq
import Keelung.Compiler.Constraint
import Keelung.Syntax (Width)

--------------------------------------------------------------------------------

data Limb = Limb
  { -- | Which RefU this limb belongs to
    lmbRef :: RefU,
    -- | How wide this limb is
    lmbWidth :: Width,
    -- | The offset of this limb
    lmbOffset :: Int,
    -- | Signs of each bit, LSB first
    lmbSigns :: [Bool]
  }
  deriving (Show)

-- | A limb is considered "positive" if all of its bits are positive
limbIsPositive :: Limb -> Bool
limbIsPositive = and . lmbSigns

-- | Given the UInt width, limb offset, and a limb, construct a sequence of bits.
toBits :: (GaloisField n, Integral n) => Int -> Int -> Bool -> Limb -> Seq (Ref, n)
toBits width powerOffset positive limb =
  Seq.fromList $
    zipWith
      ( \i sign ->
          ( B (RefUBit width (lmbRef limb) (lmbOffset limb + i)),
            if (if sign then positive else not positive)
              then 2 ^ (powerOffset + i :: Int)
              else -(2 ^ (powerOffset + i :: Int))
          )
      )
      [0 .. lmbWidth limb - 1]
      (lmbSigns limb)

toBitsC :: (GaloisField n, Integral n) => Int -> Int -> Bool -> Limb -> n -> Seq (Ref, n)
toBitsC width powerOffset positive limb constant =
  Seq.fromList $
    zipWith
      ( \i sign ->
          ( B (RefUBit width (lmbRef limb) (lmbOffset limb + i)),
            constant
              * if (if sign then positive else not positive)
                then 2 ^ (powerOffset + i :: Int)
                else -(2 ^ (powerOffset + i :: Int))
          )
      )
      [0 .. lmbWidth limb - 1]
      (lmbSigns limb)
