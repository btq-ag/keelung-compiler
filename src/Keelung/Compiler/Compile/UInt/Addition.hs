{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use guards" #-}
module Keelung.Compiler.Compile.UInt.Addition (Dimensions (..), addLimbColumn, compileAddU, compileSubU, allocLimb) where

import Control.Monad.Except
import Control.Monad.RWS
import Data.Bits qualified
import Data.Field.Galois (GaloisField)
import Data.Sequence (Seq)
import Data.Sequence qualified as Seq
import Keelung.Compiler.Compile.Error qualified as Error
import Keelung.Compiler.Compile.LimbColumn (LimbColumn (..))
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
-- data Model
--   = -- | N ≤ 1
--     Trivial
--   | -- | 2 < N ≤ 2^⌊F/2⌋
--     Standard
--   | -- | 2^⌊F/2⌋ < N
--     Extended

--------------------------------------------------------------------------------

data LimbStack
  = Ordinary Integer (Seq Limb)
  | OneLimbOnly Limb
  | OneConstantOnly Integer

-- AllNegative Integer [Limb] | Ordinary Integer [Limb]

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
                      constantSegment = sum [(if Data.Bits.testBit constant (start + i) then 1 else 0) * (2 ^ i) | i <- [0 .. currentLimbWidth - 1]]
                      column = LimbColumn.new constantSegment [Limb var currentLimbWidth start (Left sign) | (var, sign) <- vars]
                      -- negative limbs
                      resultLimb = Limb out currentLimbWidth start (Left True)
                   in (column, resultLimb)
              )
              [0, limbWidth .. width - 1]
      foldM_
        ( \prevCarries (column, resultLimb) ->
            addLimbColumn dimensions resultLimb (prevCarries <> column)
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
addLimbColumn dimensions finalResultLimb column = do
  let (stack, rest) = splitLimbStack dimensions column
  if LimbColumn.isEmpty rest
    then do
      addLimbStack dimensions finalResultLimb stack
    else do
      -- inductive case, there are more limbs to be processed
      resultLimb <- allocLimb (lmbWidth finalResultLimb) (lmbOffset finalResultLimb) True
      carryLimb <- addLimbStack dimensions resultLimb stack
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
  if constant == 0 && limbIsPositive limb
    then (OneLimbOnly limb, mempty)
    else (Ordinary constant (Seq.singleton limb), mempty)
splitLimbStack dimensions (LimbColumn constant limbs) =
  let (currentBatch, nextBatch) = Seq.splitAt (dimMaxHeight dimensions - 1) limbs
      currentBatchAllNegative = not (any limbIsPositive currentBatch)
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
addLimbStack :: (GaloisField n, Integral n) => Dimensions -> Limb -> LimbStack -> M n LimbColumn
addLimbStack dimensions resultLimb (OneConstantOnly constant) = do
  -- no limb => result = constant, no carry
  forM_ [0 .. lmbWidth resultLimb - 1] $ \i -> do
    let bit = Data.Bits.testBit constant i
    writeValB (RefUBit (dimUIntWidth dimensions) (lmbRef resultLimb) (lmbOffset resultLimb + i)) bit
  return mempty
addLimbStack dimensions resultLimb (OneLimbOnly limb) = do
  forM_ [0 .. lmbWidth resultLimb - 1] $ \i -> do
    writeEqB (RefUBit (dimUIntWidth dimensions) (lmbRef resultLimb) (lmbOffset resultLimb + i)) (RefUBit (dimUIntWidth dimensions) (lmbRef limb) (lmbOffset limb + i))
  return mempty
addLimbStack dimensions resultLimb (Ordinary constant limbs) = do
  let negLimbSize = length $ Seq.filter (not . limbIsPositive) limbs
  let allNegatives = negLimbSize == length limbs && constant == 0

  -- calculate the expected width of the carry limbs
  let arity =
        if constant /= 0
          then length limbs + 1 -- presence of a constant limb
          else
            if allNegatives
              then length limbs + 1 -- presence of a constant zero limb
              else length limbs
  let expectedCarryWidth = ceiling (logBase 2 (fromIntegral arity :: Double)) :: Int
  -- the actual width cannot be larger than that allowed by the field (dimCarryWidth dimensions)
  let carryWidth = expectedCarryWidth `min` dimCarryWidth dimensions

  let carrySigns = map (not . Data.Bits.testBit negLimbSize) [0 .. carryWidth - 1]
  carryLimb <- allocCarryLimb carryWidth (lmbOffset resultLimb) carrySigns
  writeAddWithRefLs (fromInteger constant) $
    -- positive side
    fmap (\limb -> toRefLPrim (lmbWidth limb `min` lmbWidth resultLimb) 0 True 1 limb) limbs
      -- negative side
      Seq.:|> toRefL 0 False resultLimb
      Seq.:|> toRefL (lmbWidth resultLimb) False carryLimb
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