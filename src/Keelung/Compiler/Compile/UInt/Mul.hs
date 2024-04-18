module Keelung.Compiler.Compile.UInt.Mul (compile) where

import Control.Monad.Except
import Control.Monad.RWS
import Data.Field.Galois (GaloisField)
import Data.Maybe qualified as Maybe
import Keelung (FieldType (..), HasWidth (widthOf))
import Keelung.Compiler.Compile.Error qualified as Error
import Keelung.Compiler.Compile.Monad
import Keelung.Compiler.Compile.UInt.Addition
import Keelung.Compiler.Compile.UInt.Addition.LimbColumn (LimbColumn)
import Keelung.Compiler.Compile.UInt.Addition.LimbColumn qualified as LimbColumn
import Keelung.Compiler.Compile.UInt.Multiplication.Binary qualified as Binary
import Keelung.Compiler.ConstraintModule (ConstraintModule (..))
import Keelung.Compiler.Options
import Keelung.Data.FieldInfo
import Keelung.Data.LC qualified as LC
import Keelung.Data.Limb qualified as Limb
import Keelung.Data.Reference
import Keelung.Data.Slice (Slice (Slice))
import Keelung.Data.Slice qualified as Slice
import Keelung.Data.U (U)
import Keelung.Data.U qualified as U
import Keelung.Syntax (Width)

--------------------------------------------------------------------------------

-- Model of multiplication: elementary school schoolbook multiplication
compile :: (GaloisField n, Integral n) => RefU -> Either RefU U -> Either RefU U -> M n ()
compile out (Right a) (Right b) = writeRefUVal out (U.mulV (widthOf out) a b)
compile out (Right a) (Left b) = compileMul out b (Right a)
compile out (Left a) (Right b) = compileMul out a (Right b)
compile out (Left a) (Left b) = compileMul out a (Left b)

compileMul :: (GaloisField n, Integral n) => RefU -> RefU -> Either RefU U -> M n ()
compileMul out x y = do
  let operandWidth = widthOf x -- assuming that the width of `x` is the same as the width of `y`
  fieldInfo <- gets (optFieldInfo . cmOptions)

  -- limb width limitation:
  --    2 ≤ limb width ≤ field width / 2

  -- determine the maximum and minimum limb widths
  let maxLimbWidth = fieldWidth fieldInfo `div` 2 -- cannot exceed half of the field width
  let minLimbWidth = 2 -- TEMPORARY HACK FOR ADDITION
  -- the optimal width
  let limbWidth = minLimbWidth `max` (operandWidth * 2) `min` maxLimbWidth
  -- traceM $ "maxLimbWidth: " <> show maxLimbWidth
  -- traceM $ "minLimbWidth: " <> show minLimbWidth
  -- traceM $ "limbWidth: " <> show limbWidth
  -- traceM $ "operandWidth: " <> show operandWidth
  let maxHeight = if limbWidth > 20 then 1048576 else 2 ^ limbWidth -- HACK
  case fieldTypeData fieldInfo of
    Binary _ -> Binary.compile out x y
    Prime 2 -> throwError $ Error.FieldNotSupported (fieldTypeData fieldInfo)
    Prime 3 -> throwError $ Error.FieldNotSupported (fieldTypeData fieldInfo)
    Prime 5 -> throwError $ Error.FieldNotSupported (fieldTypeData fieldInfo)
    Prime 7 -> throwError $ Error.FieldNotSupported (fieldTypeData fieldInfo)
    Prime 11 -> throwError $ Error.FieldNotSupported (fieldTypeData fieldInfo)
    Prime 13 -> throwError $ Error.FieldNotSupported (fieldTypeData fieldInfo)
    _ -> multiply maxHeight out (x, y) limbWidth

-- | Multiply slices of two operands and return the resulting slice
multiplyLimbs :: (GaloisField n, Integral n) => (Slice, Either Slice U) -> M n (Maybe Slice)
multiplyLimbs (sliceX, Left sliceY) = do
  let productWidth = widthOf sliceX + widthOf sliceY
  productSlice <- allocSlice productWidth

  -- write constraints: productSlice = sliceX * sliceY
  writeMulWithLC
    (LC.new 0 [] [(sliceX, 1)])
    (LC.new 0 [] [(sliceY, 1)])
    (LC.new 0 [] [(productSlice, 1)])

  return (Just productSlice)
multiplyLimbs (_, Right 0) = do
  return Nothing
multiplyLimbs (sliceX, Right 1) = do
  return (Just sliceX)
multiplyLimbs (sliceX, Right valueY) = do
  -- range of product: 0 ... ((2 ^ widthOf sliceX) - 1) * valueY
  let productUpperBound = ((2 ^ widthOf sliceX) - 1) * toInteger valueY
  let productWidth = U.widthOfInteger productUpperBound
  -- traceShowM (productUpperBound, sliceX, valueY)
  productSlice <- allocSlice productWidth
  -- write constraints: productSlice = valueY * sliceX
  writeAdd 0 [] [(productSlice, -1), (sliceX, fromIntegral valueY)]
  return (Just productSlice)

--  Here's what multiplication looks like in the elementary school:
--
--                    ... 2   1   0     limb indices of the first operand
--    x               ... 2   1   0     limb indices of the second operand
--  ------------------------------------------
--                          00H 00L
--                      10H 10L
--                  20H 20L
--              ....
--                      01H 01L
--                  11H 11L
--              21H 21L
--          ....
--                  02H 02L
--              12H 12L
--          22H 22L                     -- 22H may not exist
-- +    ....
-- ------------------------------------------
--
-- Observe that the nth column of the result is the sum of:
--    * lower limbs of products of two limbs whose indices sum to n
--    * upper limbs of lower limbs of the previous column
--    * carry from the previous column
--
-- Because the width of output varies, we only calculate the limbs that are needed.
--    * The number of columns = outputWidth / limbWidth + 1
--
-- The highest limb of an operand may be shorter than the default limb width.
--    * Width of the highest limb of an operand = outputWidth % limbWidth
--
-- It's possible that the product of the highest two limbs may be shorter than the default limb width.
--    * Width of the product of the highest limbs = (outputWidth % limbWidth) * 2
--
multiply :: (GaloisField n, Integral n) => Int -> RefU -> (RefU, Either RefU U) -> Width -> M n ()
multiply maxHeight refOutput (refX, operandY) limbWidth = foldM_ step (mempty, mempty) [0 .. (outputWidth `ceilDiv` limbWidth) - 1] -- the number of columns
  where
    outputWidth = widthOf refOutput
    operandWidth = widthOf refX

    step :: (GaloisField n, Integral n) => ([Slice], LimbColumn) -> Int -> M n ([Slice], LimbColumn)
    step (prevUpperLimbs, prevCarries) columnIndex = do
      let indexPairs = [(xi, columnIndex - xi) | xi <- [0 .. columnIndex]]
      let slicePairs =
            [ ( Slice refX startX ((startX + limbWidth) `min` operandWidth),
                case operandY of
                  Left refY -> Left $ Slice refY startY ((startY + limbWidth) `min` operandWidth)
                  Right valY -> Right $ U.slice valY (startY, (startY + limbWidth) `min` operandWidth)
              )
              | (indexX, indexY) <- indexPairs,
                let startX = limbWidth * indexX,
                let startY = limbWidth * indexY,
                (limbWidth * indexX) < operandWidth,
                (limbWidth * indexY) < operandWidth
            ]
      -- calculate the product of the limbs
      productSlices <- mapM multiplyLimbs slicePairs
      let (lowerLimbsMaybe, upperLimbsMaybe) = unzip $ map (splitMultipliedResult limbWidth) productSlices
      let lowerLimbs = Maybe.catMaybes lowerLimbsMaybe
      let upperLimbs = Maybe.catMaybes upperLimbsMaybe

      -- add these limbs to the output:
      --  1. lower limbs of the product
      --  2. upper limbs of the previous column
      --  3. carry from the previous column
      let limbs = map (`Limb.newOperand` True) (prevUpperLimbs <> lowerLimbs)
      let outputSlice = Slice refOutput (limbWidth * columnIndex) ((limbWidth * columnIndex + limbWidth) `min` outputWidth)
      nextCarries <- addLimbColumn maxHeight outputSlice (prevCarries <> LimbColumn.new 0 limbs)

      -- traceM $ show columnIndex <> "             =============================="
      -- traceM $ "     lower    " <> show lowerLimbs
      -- traceM $ "prev upper    " <> show prevUpperLimbs
      -- traceM $ "prev carry    " <> show prevCarries
      -- traceM "              ------------------------"

      -- traceM $ "    output    " <> show outputSlice
      -- traceM ""
      -- traceM $ "     upper    " <> show upperLimbs
      -- traceM $ "next carry    " <> show nextCarries

      return (upperLimbs, nextCarries)

    -- split the resulting slice of multiplication into lower and upper slices
    -- returns Nothing as the upper slice if it's shorter than the limb width
    splitMultipliedResult :: Int -> Maybe Slice -> (Maybe Slice, Maybe Slice)
    splitMultipliedResult _ Nothing = (Nothing, Nothing)
    splitMultipliedResult n (Just slice) =
      if n < widthOf slice
        then let (a, b) = Slice.split n slice in (Just a, Just b)
        else (Just slice, Nothing)

-- like div, but rounds up
ceilDiv :: Int -> Int -> Int
ceilDiv a b = ((a - 1) `div` b) + 1
