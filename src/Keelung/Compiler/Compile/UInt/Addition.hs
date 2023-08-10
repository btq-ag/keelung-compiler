module Keelung.Compiler.Compile.UInt.Addition (Dimensions (..), addWholeColumn, compileAddU, compileSubU, allocLimb) where

import Control.Monad.Except
import Control.Monad.RWS
import Data.Bits qualified
import Data.Field.Galois (GaloisField)
import Data.Foldable (toList)
import Data.Sequence (Seq)
import Data.Sequence qualified as Seq
import Keelung.Compiler.Compile.Error qualified as Error
import Keelung.Compiler.Compile.LimbColumn (LimbColumn)
import Keelung.Compiler.Compile.LimbColumn qualified as LimbColumn
import Keelung.Compiler.Compile.Util
import Keelung.Compiler.ConstraintModule (ConstraintModule (..))
import Keelung.Data.FieldInfo
import Keelung.Data.Reference
import Keelung.Field (FieldType (..))
import Keelung.Syntax (Width)

-- | Metavariables
--  * N – arity, number of operands
--  * F – maximum bit width of unsigned integers allowed in some underlying field,
--          for example, `F = 180` in `GF181`
--  * W - bit width of unsigned integers
data Model
  = -- | N ≤ 1
    Trivial
  | -- | 2 < N ≤ 2^⌊F/2⌋
    Standard
  | -- | 2^⌊F/2⌋ < N
    Extended

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
                      operandLimbs = LimbColumn.new 0 [Limb var currentLimbWidth start (Left sign) | (var, sign) <- vars]
                      -- negative limbs
                      resultLimb = Limb out currentLimbWidth start (Left True)
                      constantSegment = sum [(if Data.Bits.testBit constant (start + i) then 1 else 0) * (2 ^ i) | i <- [0 .. currentLimbWidth - 1]]
                   in (start, currentLimbWidth, constantSegment, resultLimb, operandLimbs)
              )
              [0, limbWidth .. width - 1]
      foldM_
        ( \prevCarries (start, currentLimbWidth, constant', resultLimb, limbs) ->
            addWholeColumn dimensions start currentLimbWidth resultLimb (LimbColumn.addConstant constant' (prevCarries <> limbs))
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

addWholeColumn :: (GaloisField n, Integral n) => Dimensions -> Int -> Int -> Limb -> LimbColumn -> M n LimbColumn
addWholeColumn dimensions limbStart currentLimbWidth finalResultLimb column = do
  let constant = LimbColumn.constant column

  let limbs = LimbColumn.limbs column
  let negLimbSize = length $ Seq.filter (not . limbIsPositive) limbs
  let allNegative = negLimbSize == length limbs
  let arity = length limbs + if allNegative || constant /= 0 then 1 else 0

  if arity > dimMaxHeight dimensions
    then do
      let (currentBatch, nextBatch) = splitLimbs limbs
      -- inductive case, there are more limbs to be processed
      resultLimb <- allocLimb currentLimbWidth limbStart True
      carryLimb <- addPartialColumn dimensions limbStart currentLimbWidth resultLimb 0 (toList currentBatch)
      -- insert the result limb of the current batch to the next batch
      moreCarryLimbs <- addWholeColumn dimensions limbStart currentLimbWidth finalResultLimb (LimbColumn.new (toInteger constant) (resultLimb : toList nextBatch))
      return (carryLimb <> moreCarryLimbs)
    else -- edge case, all limbs are in the current batch
      addPartialColumn dimensions limbStart currentLimbWidth finalResultLimb (fromInteger constant) (toList limbs)
  where
    -- Let `H` be the maximum batch size allowed
    --    if all limbs are negative
    --      then we can only add `H-1` limbs up at a time
    --      else we can add all `H` limbs up at a time
    splitLimbs :: Seq Limb -> (Seq Limb, Seq Limb)
    splitLimbs limbs =
      let (currentBatch', nextBatch') = Seq.splitAt (dimMaxHeight dimensions - 1) limbs
          currentBatchAllNegative = not (any limbIsPositive currentBatch')
       in if currentBatchAllNegative
            then (currentBatch', nextBatch')
            else case Seq.viewl nextBatch' of
              Seq.EmptyL -> (currentBatch', mempty)
              nextBatchHead Seq.:< nextBatchTail -> (currentBatch' Seq.|> nextBatchHead, nextBatchTail)

-- | Compress a column of limbs into a single limb and some carry
--
--              [ operand+ ]
--              [ operand+ ]    positive operands
--  +           [ operand+ ]
-- -----------------------------
--    [ carry  ][  result  ]
addPartialColumn :: (GaloisField n, Integral n) => Dimensions -> Int -> Int -> Limb -> n -> [Limb] -> M n LimbColumn
addPartialColumn dimensions _ currentLimbWidth resultLimb constant [] = do
  -- no limb => result = constant, no carry
  forM_ [0 .. currentLimbWidth - 1] $ \i -> do
    let bit = Data.Bits.testBit (toInteger constant) i
    writeValB (RefUBit (dimUIntWidth dimensions) (lmbRef resultLimb) (lmbOffset resultLimb + i)) bit
  return mempty
addPartialColumn dimensions limbStart currentLimbWidth resultLimb constant limbs = do
  let negLimbSize = length $ filter (not . limbIsPositive) limbs
  let allNegative = negLimbSize == length limbs

  if length limbs == 1 && constant == 0 && not allNegative
    then do
      forM_ [0 .. currentLimbWidth - 1] $ \i -> do
        let limb = head limbs
        writeEqB (RefUBit (dimUIntWidth dimensions) (lmbRef resultLimb) (lmbOffset resultLimb + i)) (RefUBit (dimUIntWidth dimensions) (lmbRef limb) (lmbOffset limb + i))
      return mempty
    else do
      let carrySigns = map (not . Data.Bits.testBit negLimbSize) [0 .. dimCarryWidth dimensions - 1]
      carryLimb <- allocCarryLimb (dimCarryWidth dimensions) limbStart carrySigns
      writeAddWithRefLs constant $
        -- positive side
        Seq.fromList (map (toRefL1 0 True) limbs)
          -- negative side
          Seq.:|> toRefL1 0 False resultLimb
          Seq.:|> toRefL1 currentLimbWidth False carryLimb
      return $ LimbColumn.singleton carryLimb

allocCarryLimb :: (GaloisField n, Integral n) => Width -> Int -> [Bool] -> M n Limb
allocCarryLimb w offset signs = do
  refU <- freshRefU w
  return $
    Limb
      { lmbRef = refU,
        lmbWidth = w,
        lmbOffset = offset,
        lmbSigns = Right signs
      }

allocLimb :: (GaloisField n, Integral n) => Width -> Int -> Bool -> M n Limb
allocLimb w offset sign = do
  refU <- freshRefU w
  return $
    Limb
      { lmbRef = refU,
        lmbWidth = w,
        lmbOffset = offset,
        lmbSigns = Left sign
      }