module Keelung.Compiler.Compile.UInt where

import Control.Monad.Except
import Control.Monad.State
import Data.Bits qualified
import Data.Sequence (Seq)
import Data.Sequence qualified as Seq
import Keelung
import Keelung.Compiler.Compile.Error qualified as Error
import Keelung.Compiler.Compile.Util
import Keelung.Compiler.Constraint
import Keelung.Compiler.ConstraintModule (ConstraintModule (..))
import Keelung.Compiler.FieldInfo (FieldInfo (..))

-- Model of addition: we expect these two piles of limbs to be equal
--
--
--                [ operand ]
--                [ operand ]
--                    ...
--                [ operand ]
--    +           [ operand ]
--    -----------------------------
--       [ carry ][ result  ]
--       [ carry ]
--          ...
--       [ carry ]
--       [ carry ]

compileAddU :: (GaloisField n, Integral n) => Width -> RefU -> [(RefU, Bool)] -> Integer -> M n ()
compileAddU width out [] constant = do
  -- constants only
  fieldInfo <- gets cmField
  let carryWidth = 0 -- no carry needed
  let limbWidth = fieldWidth fieldInfo - carryWidth
  mapM_ (go limbWidth) [0, limbWidth .. width - 1]
  where
    go :: (GaloisField n, Integral n) => Int -> Int -> M n ()
    go limbWidth limbStart = do
      let range = [limbStart .. (limbStart + limbWidth - 1) `min` (width - 1)]
      forM_ range $ \i -> do
        let bit = Data.Bits.testBit constant i
        writeValB (RefUBit width out i) bit
compileAddU width out vars constant = do
  fieldInfo <- gets cmField

  let numberOfOperands = length vars

  -- calculate the expected width of the carry limbs, which is logarithimic to the number of operands
  let expectedCarryWidth = ceiling (logBase 2 (fromIntegral numberOfOperands + if constant == 0 then 0 else 1) :: Double) :: Int

  -- invariants about widths of carry and limbs:
  --  1. limb width + carry width ≤ field width, so that they both fit in a field
  --  2. limb width ≥ carry width, so that the carry can be added to the next limb
  let carryWidth =
        if expectedCarryWidth * 2 <= fieldWidth fieldInfo
          then expectedCarryWidth -- we can use the expected carry width
          else fieldWidth fieldInfo `div` 2 -- the actual carry width should be less than half of the field width

  -- NOTE, we use the same width for all limbs on the both sides for the moment (they can be different)
  let limbWidth = fieldWidth fieldInfo - carryWidth

  let dimensions =
        Dimensions
          { dimUIntWidth = width,
            dimMaxHeight = 2 ^ carryWidth,
            dimCarryWidth = carryWidth
          }

  case fieldTypeData fieldInfo of
    Binary _ -> throwError $ Error.FieldNotSupported (fieldTypeData fieldInfo)
    Prime 2 -> throwError $ Error.FieldNotSupported (fieldTypeData fieldInfo)
    Prime 3 -> throwError $ Error.FieldNotSupported (fieldTypeData fieldInfo)
    _ -> do
      let ranges =
            map
              ( \start ->
                  let currentLimbWidth = limbWidth `min` (width - start)
                      -- positive limbs
                      operandLimbs = [Limb var currentLimbWidth start sign sign | (var, sign) <- vars]
                      -- negative limbs
                      resultLimb = Limb out currentLimbWidth start False False
                      constantSegment = sum [(if Data.Bits.testBit constant (start + i) then 1 else 0) * (2 ^ i) | i <- [0 .. currentLimbWidth - 1]]
                   in (start, currentLimbWidth, constantSegment, resultLimb, operandLimbs)
              )
              [0, limbWidth .. width - 1]
      foldM_
        ( \prevCarries (start, limbWidth', constant', resultLimb, limbs) ->
            compileWholeLimbPile dimensions start limbWidth' constant' resultLimb (prevCarries <> limbs)
        )
        []
        ranges

data Dimensions = Dimensions
  { dimUIntWidth :: Int,
    dimMaxHeight :: Int,
    dimCarryWidth :: Int
  }
  deriving (Show)

-- | Compress a pile of limbs into a single limb and some carry
--
--              [ operand+ ]
--              [ operand+ ]    positive operands
--  +           [ operand+ ]
-- -----------------------------
--    [ carry  ][  result  ]
compileSingleLimbPile :: (GaloisField n, Integral n) => Dimensions -> Int -> Int -> [Limb] -> M n (Limb, Limb)
compileSingleLimbPile dimensions limbStart currentLimbWidth limbs = do
  -- if the any of the limbs is negative, the largest digit of the carry should be negative as well
  let msbSign = all lmbSign limbs
  carryLimb <- allocCarryLimb (dimCarryWidth dimensions) limbStart True msbSign
  resultLimb <- allocLimb currentLimbWidth limbStart True
  -- limbs = resultLimb + carryLimb
  writeAddWithSeq 0 $
    -- positive side
    mconcat (map (toBits (dimUIntWidth dimensions) 0 True) limbs)
      -- negative side
      <> toBits (dimUIntWidth dimensions) 0 False resultLimb
      <> toBits (dimUIntWidth dimensions) currentLimbWidth False carryLimb
  return (carryLimb, resultLimb)

compileWholeLimbPile :: (GaloisField n, Integral n) => Dimensions -> Int -> Int -> n -> Limb -> [Limb] -> M n [Limb]
compileWholeLimbPile dimensions limbStart currentLimbWidth constant finalResultLimb limbs = do
  let (currentBatch, nextBatch) = splitAt (dimMaxHeight dimensions) limbs
  if null nextBatch
    then do
      if length currentBatch == dimMaxHeight dimensions 
        then do 
          -- inductive case, there are more limbs to be processed
          (carryLimb, resultLimb) <- compileSingleLimbPile dimensions limbStart currentLimbWidth currentBatch
          -- insert the result limb of the current batch to the next batch
          moreCarryLimbs <- compileWholeLimbPile dimensions limbStart currentLimbWidth constant finalResultLimb [resultLimb]

          return (carryLimb : moreCarryLimbs)
        else do 
          -- edge case, all limbs are in the current batch
          let msbSign = all lmbSign currentBatch

          carryLimb <- allocCarryLimb (dimCarryWidth dimensions) (limbStart + currentLimbWidth) True msbSign

          -- limbs - result + previous carry = carryLimb
          writeAddWithSeq constant $
            -- positive side
            mconcat (map (toBits (dimUIntWidth dimensions) 0 True) limbs)
              -- negative side
              <> toBits (dimUIntWidth dimensions) 0 True finalResultLimb
              <> toBits (dimUIntWidth dimensions) currentLimbWidth False carryLimb -- multiply by `2^currentLimbWidth`
          return [carryLimb]
    else do
      -- inductive case, there are more limbs to be processed
      (carryLimb, resultLimb) <- compileSingleLimbPile dimensions limbStart currentLimbWidth currentBatch
      -- insert the result limb of the current batch to the next batch
      moreCarryLimbs <- compileWholeLimbPile dimensions limbStart currentLimbWidth constant finalResultLimb (resultLimb : nextBatch)

      return (carryLimb : moreCarryLimbs)

compileSubU :: (GaloisField n, Integral n) => Width -> RefU -> Either RefU Integer -> Either RefU Integer -> M n ()
compileSubU width out (Right a) (Right b) = compileAddU width out [] (a - b)
compileSubU width out (Right a) (Left b) = compileAddU width out [(b, False)] a
compileSubU width out (Left a) (Right b) = compileAddU width out [(a, True)] (-b)
compileSubU width out (Left a) (Left b) = compileAddU width out [(a, True), (b, False)] 0

--------------------------------------------------------------------------------

data Limb = Limb
  { -- | Which RefU this limb belongs to
    lmbRef :: RefU,
    -- | How wide this limb is
    lmbWidth :: Width,
    -- | The offset of this limb
    lmbOffset :: Int,
    -- | Whether all bits (except for the highest bit) are positive or negative
    lmbSign :: Bool,
    -- | Whether the highest bit is positive or negative
    lmbMSBSign :: Bool
  }
  deriving (Show)

allocLimb :: (GaloisField n, Integral n) => Width -> Int -> Bool -> M n Limb
allocLimb w offset sign = do
  refU <- freshRefU w
  mapM_ addBooleanConstraint [RefUBit w refU i | i <- [0 .. w - 1]]
  return $
    Limb
      { lmbRef = refU,
        lmbWidth = w,
        lmbOffset = offset,
        lmbSign = sign,
        lmbMSBSign = sign
      }

allocCarryLimb :: (GaloisField n, Integral n) => Width -> Int -> Bool -> Bool -> M n Limb
allocCarryLimb w offset sign msbSign = do
  refU <- freshRefU w
  mapM_ addBooleanConstraint [RefUBit w refU i | i <- [0 .. w - 1]]
  return $
    Limb
      { lmbRef = refU,
        lmbWidth = w,
        lmbOffset = offset,
        lmbSign = sign,
        lmbMSBSign = msbSign
      }

-- | Given the UInt width, limb offset, and a limb, construct a sequence of bits.
toBits :: (GaloisField n, Integral n) => Int -> Int -> Bool -> Limb -> Seq (Ref, n)
toBits width powerOffset positive limb =
  Seq.fromFunction
    (lmbWidth limb)
    ( \i ->
        ( B (RefUBit width (lmbRef limb) (lmbOffset limb + i)),
          if i == lmbWidth limb - 1
            then
              if (if lmbMSBSign limb then positive else not positive)
                then 2 ^ (powerOffset + i :: Int)
                else -(2 ^ (powerOffset + i :: Int))
            else
              if (if lmbSign limb then positive else not positive)
                then 2 ^ (powerOffset + i :: Int)
                else -(2 ^ (powerOffset + i :: Int))
        )
    )
