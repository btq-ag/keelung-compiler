module Keelung.Compiler.Compile.UInt.Multiplication (compileMulU) where

import Control.Monad.Except
import Control.Monad.RWS
import Data.Bits qualified
import Data.Field.Galois (GaloisField)
import Data.IntMap.Strict qualified as IntMap
import Keelung (FieldType (..), HasWidth (widthOf))
import Keelung.Compiler.Compile.Error qualified as Error
import Keelung.Compiler.Compile.Monad
import Keelung.Compiler.Compile.UInt.Addition
import Keelung.Compiler.Compile.UInt.Addition.LimbColumn (LimbColumn)
import Keelung.Compiler.Compile.UInt.Addition.LimbColumn qualified as LimbColumn
import Keelung.Compiler.ConstraintModule (ConstraintModule (..))
import Keelung.Data.FieldInfo
import Keelung.Data.Limb (Limb (..))
import Keelung.Data.Limb qualified as Limb
import Keelung.Data.Reference
import Keelung.Data.U (U)
import Keelung.Syntax (Width)
import Keelung.Compiler.Compile.UInt.Multiplication.Binary (compileMulB)

--------------------------------------------------------------------------------

-- Model of multiplication: elementary school schoolbook multiplication

-- assume that each number has been divided into L w-bit limbs
-- multiplying two numbers will result in L^2 2w-bit limbs
--
--                          a1 a2 a3
-- x                        b1 b2 b3
-- ------------------------------------------
--                             a3*b3
--                          a2*b3
--                       a1*b3
--                          a3*b2
--                       a2*b2
--                    a1*b2
--                       a3*b1
--                    a2*b1
--                 a1*b1
-- ------------------------------------------
--
-- the maximum number of operands when adding these 2w-bit limbs is 2L (with carry from the previous limb)
compileMulU :: (GaloisField n, Integral n) => Int -> RefU -> Either RefU U -> Either RefU U -> M n ()
compileMulU _width out (Right a) (Right b) = writeRefUVal out (a * b)
compileMulU width out (Right a) (Left b) = compileMul width out b (Right a)
compileMulU width out (Left a) (Right b) = compileMul width out a (Right b)
compileMulU width out (Left a) (Left b) = compileMul width out a (Left b)

compileMul :: (GaloisField n, Integral n) => Width -> RefU -> RefU -> Either RefU U -> M n ()
compileMul width out x y = do
  fieldInfo <- gets cmField

  -- invariants about widths of carry and limbs:
  --  1. 2 ≤ limb width * 2 ≤ field width

  -- determine the maximum and minimum limb widths
  let maxLimbWidth = fieldWidth fieldInfo `div` 2 -- cannot exceed half of the field width
  let minLimbWidth = 2 -- TEMPORARY HACK FOR ADDITION
  -- the number of limbs needed to represent an operand
  let limbNumber = width `ceilDiv` (minLimbWidth `max` width `min` maxLimbWidth)
  -- the optimal width
  let limbWidth = width `ceilDiv` limbNumber

  let maxHeight = if limbWidth > 20 then 1048576 else 2 ^ limbWidth -- HACK
  case fieldTypeData fieldInfo of
    Binary _ -> compileMulB width out x y
    Prime 2 -> throwError $ Error.FieldNotSupported (fieldTypeData fieldInfo)
    Prime 3 -> throwError $ Error.FieldNotSupported (fieldTypeData fieldInfo)
    Prime 5 -> throwError $ Error.FieldNotSupported (fieldTypeData fieldInfo)
    Prime 7 -> throwError $ Error.FieldNotSupported (fieldTypeData fieldInfo)
    Prime 11 -> throwError $ Error.FieldNotSupported (fieldTypeData fieldInfo)
    Prime 13 -> throwError $ Error.FieldNotSupported (fieldTypeData fieldInfo)
    _ -> mulnxn width maxHeight limbWidth limbNumber out x y
  where
    -- like div, but rounds up
    ceilDiv :: Int -> Int -> Int
    ceilDiv a b = ((a - 1) `div` b) + 1

mul2Limbs :: (GaloisField n, Integral n) => Width -> Int -> (n, Limb) -> Either n (n, Limb) -> M n (LimbColumn, LimbColumn)
mul2Limbs currentLimbWidth limbStart (a, x) operand = do
  case operand of
    Left 0 -> do
      -- if the constant is 0, then the resulting limbs should be empty
      return (mempty, mempty)
    Left 1 -> do
      -- if the constant is 1, then the resulting limbs should be the same as the input
      return (LimbColumn.new (toInteger a) [x], mempty)
    Left constant -> do
      upperLimb <- allocLimb currentLimbWidth (limbStart + currentLimbWidth) True
      lowerLimb <- allocLimb currentLimbWidth limbStart True
      writeAddWithLimbs
        (a * constant)
        []
        [ -- operand side
          (x, constant),
          -- negative side
          (lowerLimb, -1),
          (upperLimb, -(2 ^ currentLimbWidth))
        ]
      return (LimbColumn.singleton lowerLimb, LimbColumn.singleton upperLimb)
    Right (b, y) -> do
      let carryLimbWidth = lmbWidth x + lmbWidth y - currentLimbWidth
      upperLimb <- allocLimb carryLimbWidth (limbStart + currentLimbWidth) True
      lowerLimb <- allocLimb currentLimbWidth limbStart True
      writeMulWithLimbs
        (a, [(x, 1)])
        (b, [(y, 1)])
        ( 0,
          [ (lowerLimb, 1),
            (upperLimb, 2 ^ currentLimbWidth)
          ]
        )
      return (LimbColumn.singleton lowerLimb, LimbColumn.singleton upperLimb)

-- | n-limb by n-limb multiplication
--                       .. x2 x1 x0
-- x                     .. y2 y1 y0
-- ------------------------------------------
--                             x0*y0
--                          x1*y0
--                       x2*y0
--                    .....
--                          x0*y1
--                       x1*y1
--                    x2*y1
--                 .....
--                       x0*y2
--                    x1*y2
--                 x2*y2
--               .....
-- ------------------------------------------
mulnxn :: (GaloisField n, Integral n) => Width -> Int -> Width -> Int -> RefU -> RefU -> Either RefU U -> M n ()
mulnxn width maxHeight limbWidth arity out var operand = do
  -- generate pairs of indices for choosing limbs
  let indices = [(xi, columnIndex - xi) | columnIndex <- [0 .. arity - 1], xi <- [0 .. columnIndex]]
  -- generate pairs of limbs to be added together
  limbColumns <-
    foldM
      ( \columns (xi, yi) -> do
          -- current limb width may be smaller than
          --    1. the default limb width in the highest limbs
          --    2. the width of the RefU
          let currentLimbWidthX = limbWidth `min` widthOf var `min` (width - (limbWidth * xi))
          let currentLimbWidthY = limbWidth `min` widthOf var `min` (width - (limbWidth * yi))

          let x = Limb.new var currentLimbWidthX (limbWidth * xi) (Left True)
          let y = case operand of
                Right constant -> Left $ sum [(if Data.Bits.testBit constant (limbWidth * yi + i) then 1 else 0) * (2 ^ i) | i <- [0 .. currentLimbWidthY - 1]]
                Left variable -> Right (0, Limb.new variable currentLimbWidthY (limbWidth * yi) (Left True))
          let index = xi + yi

          (lowerLimb, upperLimb) <- mul2Limbs limbWidth (limbWidth * index) (0, x) y
          let columns' = IntMap.insertWith (<>) index lowerLimb columns
          let columns'' =
                if index == arity - 1 -- throw limbs higher than the arity away
                  then columns'
                  else IntMap.insertWith (<>) (index + 1) upperLimb columns'
          return columns''
      )
      mempty
      indices
  -- go through each columns and add them up
  foldM_
    ( \previousCarryLimbs (index, limbs) -> do
        let limbStart = limbWidth * index
        let currentLimbWidth = limbWidth `min` (width - limbStart)
        let resultLimb = Limb.new out currentLimbWidth limbStart (Left True)
        addLimbColumn maxHeight resultLimb (previousCarryLimbs <> limbs)
    )
    mempty
    (IntMap.toList limbColumns)
