{-# LANGUAGE TupleSections #-}

module Keelung.Compiler.Compile.UInt.Addition (Dimensions (..), addLimbColumn, compileAddU, compileSubU, allocLimb) where

import Control.Monad.Except
import Control.Monad.RWS
import Data.Bits qualified
import Data.Field.Galois (GaloisField)
import Data.Foldable (Foldable (toList))
import Data.Sequence (Seq)
import Data.Sequence qualified as Seq
import Keelung.Compiler.Compile.Error qualified as Error
import Keelung.Compiler.Compile.LimbColumn (LimbColumn (LimbColumn))
import Keelung.Compiler.Compile.LimbColumn qualified as LimbColumn
import Keelung.Compiler.Compile.Monad
import Keelung.Compiler.Compile.Util
import Keelung.Compiler.ConstraintModule (ConstraintModule (..))
import Keelung.Data.FieldInfo
import Keelung.Data.Limb (Limb (..))
import Keelung.Data.Limb qualified as Limb
import Keelung.Data.Reference
import Keelung.Field (FieldType (..))
import Keelung.Syntax (Width)

--------------------------------------------------------------------------------

data LimbStack
  = Ordinary Integer (Seq Limb)
  | OneLimbOnly Limb
  | OneConstantOnly Integer

--------------------------------------------------------------------------------

-- Model of addition: elementary school addition with possibly multiple carries
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
compileAddU width out vars constant = do
  fieldInfo <- gets cmField

  let arity = length vars + if constant == 0 then 0 else 1
  -- calculate the expected width of the carry limbs, which is logarithimic to the number of operands
  let expectedCarryWidth = ceiling (logBase 2 (fromIntegral arity :: Double)) `max` 2 :: Int
  -- invariants about widths of carry and limbs:
  --  1. limb width + carry width ≤ field width, so that they both fit in a field
  --  2. limb width ≥ carry width, so that the carry can be added to the next limb
  --  3. carryWidth ≥ 2 (TEMP HACK)
  let carryWidth =
        if expectedCarryWidth * 2 <= fieldWidth fieldInfo
          then expectedCarryWidth -- we can use the expected carry width
          else fieldWidth fieldInfo `div` 2 -- the actual carry width should be less than half of the field width

  -- NOTE, we use the same width for all limbs on the both sides for the moment (they can be different)
  let limbWidth = fieldWidth fieldInfo - carryWidth

  let dimensions =
        Dimensions
          { dimUIntWidth = width,
            dimMaxHeight = if carryWidth > 21 then 1048576 else 2 ^ carryWidth, -- HACK
            dimCarryWidth = carryWidth
          }

  case fieldTypeData fieldInfo of
    Binary _ -> throwError $ Error.FieldNotSupported (fieldTypeData fieldInfo)
    Prime 2 -> throwError $ Error.FieldNotSupported (fieldTypeData fieldInfo)
    Prime 3 -> throwError $ Error.FieldNotSupported (fieldTypeData fieldInfo)
    Prime 5 -> throwError $ Error.FieldNotSupported (fieldTypeData fieldInfo)
    Prime 7 -> throwError $ Error.FieldNotSupported (fieldTypeData fieldInfo)
    Prime 11 -> throwError $ Error.FieldNotSupported (fieldTypeData fieldInfo)
    Prime 13 -> throwError $ Error.FieldNotSupported (fieldTypeData fieldInfo)
    _ -> do
      let ranges =
            map
              ( \start ->
                  let currentLimbWidth = limbWidth `min` (width - start)
                      -- positive limbs
                      constantSegment = sum [(if Data.Bits.testBit constant (start + i) then 1 else 0) * (2 ^ i) | i <- [0 .. currentLimbWidth - 1]]
                      column = LimbColumn.new constantSegment [Limb.new var currentLimbWidth start (Left sign) | (var, sign) <- vars]
                      -- negative limbs
                      resultLimb = Limb.new out currentLimbWidth start (Left True)
                   in (column, resultLimb)
              )
              [0, limbWidth .. width - 1] -- index of the first bit of each limb
      foldM_
        ( \prevCarries (column, resultLimb) -> addLimbColumn dimensions resultLimb (prevCarries <> column)
        )
        mempty
        ranges

data Dimensions = Dimensions
  { dimUIntWidth :: Int,
    dimMaxHeight :: Int,
    dimCarryWidth :: Int
  }
  deriving (Show)

compileSubU :: (GaloisField n, Integral n) => Width -> RefU -> Either RefU Integer -> Either RefU Integer -> M n ()
compileSubU width out (Right a) (Right b) = compileAddU width out [] (a - b)
compileSubU width out (Right a) (Left b) = compileAddU width out [(b, False)] a
compileSubU width out (Left a) (Right b) = compileAddU width out [(a, True)] (-b)
compileSubU width out (Left a) (Left b) = compileAddU width out [(a, True), (b, False)] 0

-- | Add a column of limbs, and return a column of carry limbs
addLimbColumn :: (GaloisField n, Integral n) => Dimensions -> Limb -> LimbColumn -> M n LimbColumn
addLimbColumn dimensions finalResultLimb limbs = do
  -- trim the limbs so that their width does not exceed that of the result limb
  let trimmedLimbs = LimbColumn.trim (lmbWidth finalResultLimb) limbs
  -- split the limbs into a stack of limbs and the rest of the column
  let (stack, rest) = splitLimbStack dimensions trimmedLimbs
  if LimbColumn.isEmpty rest
    then do
      -- base case, there are no more limbs to be processed
      addLimbStack finalResultLimb stack
    else do
      -- inductive case, there are more limbs to be processed
      resultLimb <- allocLimb (lmbWidth finalResultLimb) (lmbOffset finalResultLimb) True
      carryLimb <- addLimbStack resultLimb stack
      -- insert the result limb of the current batch to the next batch
      moreCarryLimbs <- addLimbColumn dimensions finalResultLimb (LimbColumn.insert resultLimb rest)
      return (carryLimb <> moreCarryLimbs)

-- | Split a column of limbs into a stack of limbs and the rest of the column
-- Let `H` be the maximum batch size allowed
--    if all limbs are negative
--      then we can only add `H-1` limbs up at a time
--      else we can add all `H` limbs up at a time
splitLimbStack :: Dimensions -> LimbColumn -> (LimbStack, LimbColumn)
splitLimbStack _ (LimbColumn constant Seq.Empty) = (OneConstantOnly constant, mempty)
splitLimbStack _ (LimbColumn constant (limb Seq.:<| Seq.Empty)) =
  if constant == 0 && Limb.isPositive limb
    then (OneLimbOnly limb, mempty)
    else (Ordinary constant (Seq.singleton limb), mempty)
splitLimbStack dimensions (LimbColumn constant limbs) =
  let (currentBatch, nextBatch) = Seq.splitAt (dimMaxHeight dimensions - 1) limbs
      currentBatchAllNegative = not (any Limb.isPositive currentBatch)
   in if currentBatchAllNegative
        then (Ordinary constant currentBatch, LimbColumn 0 nextBatch)
        else case Seq.viewl nextBatch of
          Seq.EmptyL -> (Ordinary constant currentBatch, mempty)
          nextBatchHead Seq.:< nextBatchTail -> (Ordinary constant (currentBatch Seq.|> nextBatchHead), LimbColumn 0 nextBatchTail)

-- | Compress a column of limbs into a single limb and some carry
--
--              [ operand+ ]
--              [ operand+ ]    positive operands
--  +           [ operand+ ]
-- -----------------------------
--    [ carry  ][  result  ]
addLimbStack :: (GaloisField n, Integral n) => Limb -> LimbStack -> M n LimbColumn
addLimbStack resultLimb (OneConstantOnly constant) = do
  -- no limb => result = constant, no carry
  writeValL resultLimb constant
  return mempty
addLimbStack resultLimb (OneLimbOnly limb) = do
  writeEqL resultLimb limb
  return mempty
addLimbStack resultLimb (Ordinary constant limbs) = do
  let carrySigns = calculateCarrySigns (lmbWidth resultLimb) constant limbs
  carryLimb <- allocCarryLimb (length carrySigns) (lmbOffset resultLimb) carrySigns
  writeAddWithLimbs (fromInteger constant) $
    -- negative side
    (resultLimb, -1)
      : (carryLimb, -(2 ^ lmbWidth resultLimb))
      -- positive side
      : fmap (,1) (toList limbs)
  return $ LimbColumn.singleton carryLimb

allocCarryLimb :: (GaloisField n, Integral n) => Width -> Int -> [Bool] -> M n Limb
allocCarryLimb w offset signs = do
  refU <- freshRefU w
  return $ Limb.new refU w offset (Right signs)

allocLimb :: (GaloisField n, Integral n) => Width -> Int -> Bool -> M n Limb
allocLimb w offset sign = do
  refU <- freshRefU w
  return $ Limb.new refU w offset (Left sign)