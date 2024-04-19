module Keelung.Compiler.Compile.UInt.Addition (addLimbColumn, compileAdd, compileSub) where

import Control.Monad.Except
import Control.Monad.RWS
import Data.Bits qualified
import Data.Field.Galois (GaloisField)
import Data.Foldable (Foldable (toList))
import Debug.Trace
import Keelung.Compiler.Compile.Error qualified as Error
import Keelung.Compiler.Compile.Monad
import Keelung.Compiler.Compile.UInt.Addition.Binary (compileAddB)
import Keelung.Compiler.Compile.UInt.Addition.LimbColumn (LimbColumn)
import Keelung.Compiler.Compile.UInt.Addition.LimbColumn qualified as LimbColumn
import Keelung.Compiler.Compile.Util
import Keelung.Compiler.ConstraintModule (ConstraintModule (..))
import Keelung.Compiler.Options
import Keelung.Data.FieldInfo
import Keelung.Data.Limb qualified as Limb
import Keelung.Data.Reference
import Keelung.Data.Slice (Slice (Slice))
import Keelung.Data.Slice qualified as Slice
import Keelung.Data.U (U)
import Keelung.Field (FieldType (..))
import Keelung.Syntax (Width, widthOf)

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

compileAdd :: (GaloisField n, Integral n) => Width -> RefU -> [(RefU, Bool)] -> U -> M n ()
compileAdd width out refs constant = do
  fieldInfo <- gets (optFieldInfo . cmOptions)

  let arity = length refs + if constant == 0 then 0 else 1
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

  -- the maximum number of limbs that can be added up at a time
  let maxHeight = if carryWidth > 21 then 1048576 else 2 ^ carryWidth -- HACK
  case fieldTypeData fieldInfo of
    Binary _ -> compileAddB width out refs constant
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
                  let end = (start + limbWidth) `min` width
                      outputLimbWidth = end - start
                      -- positive limbs
                      constantSegment = sum [(if Data.Bits.testBit constant (start + i) then 1 else 0) * (2 ^ i) | i <- [0 .. outputLimbWidth - 1]]
                      column =
                        LimbColumn.new
                          constantSegment
                          [ Limb.newOperand (Slice ref start ((start + outputLimbWidth) `min` widthOf ref)) sign
                            | (ref, sign) <- refs,
                              ((start + outputLimbWidth) `min` widthOf ref) > start
                          ]
                      -- negative limbs
                      outputSlice = Slice out start (start + outputLimbWidth)
                   in (column, outputSlice)
              )
              [0, limbWidth .. width - 1] -- index of the first bit of each limb
      foldM_
        ( \prevCarries (column, resultSlice) -> addLimbColumn maxHeight resultSlice (prevCarries <> column)
        )
        mempty
        ranges

-- | Subtraction is implemented as addition with negated operands
compileSub :: (GaloisField n, Integral n) => Width -> RefU -> Either RefU U -> Either RefU U -> M n ()
compileSub width out (Right a) (Right b) = compileAdd width out [] (a - b)
compileSub width out (Right a) (Left b) = compileAdd width out [(b, False)] a
compileSub width out (Left a) (Right b) = compileAdd width out [(a, True)] (-b)
compileSub width out (Left a) (Left b) = compileAdd width out [(a, True), (b, False)] 0

--------------------------------------------------------------------------------

-- | Add a column of limbs, and return a column of carry limbs
addLimbColumn :: (GaloisField n, Integral n) => Int -> Slice -> LimbColumn -> M n LimbColumn
addLimbColumn maxHeight finalResultSlice limbs = do
  -- trim the limbs so that their width does not exceed that of the result limb
  let trimmedLimbs = LimbColumn.trim (widthOf finalResultSlice) limbs
  -- split the limbs into a stack of limbs and the rest of the column
  let (stack, rest) = LimbColumn.view maxHeight trimmedLimbs
  case rest of
    Nothing -> do
      -- base case, there are no more limbs to be processed
      addLimbColumnView finalResultSlice stack
    Just rest' -> do
      -- inductive case, there are more limbs to be processed
      resultSlice <- allocSlice (widthOf finalResultSlice)
      carryLimbs <- addLimbColumnView resultSlice stack
      -- insert the result limb of the current batch to the next batch
      moreCarryLimbs <- addLimbColumn maxHeight finalResultSlice (LimbColumn.insert (Limb.newOperand resultSlice True) rest')
      return $ carryLimbs <> moreCarryLimbs

-- | Compress a column of limbs into a single limb and some carry
--
--              [ operand ]
--              [ operand ]   operands
--  +           [ operand ]
-- -----------------------------
--    [ carry  ][  result  ]
addLimbColumnView :: (GaloisField n, Integral n) => Slice -> LimbColumn.View -> M n LimbColumn
addLimbColumnView resultSlice (LimbColumn.OneConstantOnly constant) = do
  -- no limb => result = constant, no carry
  writeSliceVal resultSlice constant
  return mempty
addLimbColumnView resultSlice (LimbColumn.OnePositiveLimbOnly slice) = do
  let operandWidth = widthOf slice
  let resultWidth = widthOf resultSlice
  case operandWidth `compare` resultWidth of
    LT -> do
      -- the operand is shorter than result
      -- write 0 to the higher bits of the result
      let resultSliceLO = resultSlice {Slice.sliceEnd = Slice.sliceEnd resultSlice - (resultWidth - operandWidth)}
      let resultSliceHI = resultSlice {Slice.sliceStart = Slice.sliceEnd resultSlice - (resultWidth - operandWidth)}
      writeSliceEq resultSliceLO slice
      writeSliceVal resultSliceHI 0
    EQ -> writeSliceEq resultSlice slice
    GT -> do
      -- the operand is longer than result
      -- write the lower bits of the operand to the result
      let operandSliceLO = slice {Slice.sliceEnd = Slice.sliceEnd slice - (operandWidth - resultWidth)}
      writeSliceEq resultSlice operandSliceLO
  return mempty
addLimbColumnView resultSlice (LimbColumn.Ordinary constant limbs) = do
  let carrySigns = calculateCarrySigns (widthOf resultSlice) constant limbs
  carryLimb <- allocCarryLimb carrySigns
  let carrySlices = Limb.toSlice (-(2 ^ widthOf resultSlice)) carryLimb
  let otherSlices = toList limbs >>= Limb.toSlice 1
  writeAdd (fromInteger constant) [] $
    (resultSlice, -1)
      : carrySlices
        <> otherSlices

  return $ LimbColumn.singleton carryLimb