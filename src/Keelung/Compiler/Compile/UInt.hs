module Keelung.Compiler.Compile.UInt where

import Control.Monad.Except
import Control.Monad.State
import Data.Bits (xor)
import Data.Bits qualified
import Data.Sequence (Seq)
import Data.Sequence qualified as Seq
import Keelung
import Keelung.Compiler.Compile.Error qualified as Error
import Keelung.Compiler.Compile.Util
import Keelung.Compiler.Constraint
import Keelung.Compiler.ConstraintModule (ConstraintModule (..))
import Keelung.Compiler.FieldInfo (FieldInfo (..))

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
  -- for each negative operand, we compensate by adding 2^width
  let numberOfNegativeOperand = length $ filter (not . snd) vars
  -- we need some extra bits for carry when adding UInts
  let expectedCarryWidth = ceiling (logBase 2 (fromIntegral (length vars) + if constant == 0 then 0 else 1) :: Double)
  let limbWidth = (fieldWidth fieldInfo - expectedCarryWidth) `max` 1
  let carryWidth = fieldWidth fieldInfo - limbWidth

  maxHeight <- maxHeightAllowed
  case fieldTypeData fieldInfo of
    Binary _ -> throwError $ Error.FieldNotSupported (fieldTypeData fieldInfo)
    Prime 2 -> throwError $ Error.FieldNotSupported (fieldTypeData fieldInfo)
    Prime 3 -> throwError $ Error.FieldNotSupported (fieldTypeData fieldInfo)
    _ -> do
      let ranges =
            reverse $
              fst $
                foldl
                  ( \(acc, borrow) start ->
                      let currentLimbWidth = limbWidth `min` (width - start)
                          resultLimb = Limb out currentLimbWidth start True
                          operandLimbs = [Limb var currentLimbWidth start sign | (var, sign) <- vars]
                          constantSegment = sum [(if Data.Bits.testBit constant (start + i) then 1 else 0) * (2 ^ i) | i <- [0 .. currentLimbWidth - 1]]
                          -- borrowAmount =
                          -- compensatedConstant = constantSegment + 2 ^ currentLimbWidth * fromIntegral numberOfNegativeOperand - borrow
                          compensatedConstant = constantSegment + 2 ^ currentLimbWidth * fromIntegral numberOfNegativeOperand - borrow

                          overflowed = compensatedConstant == 2 ^ fieldWidth fieldInfo && compensatedConstant < 2 ^ width
                          compensatedConstant' = if overflowed then compensatedConstant - (2 ^ currentLimbWidth) else compensatedConstant
                          nextBorrow = if overflowed then fromIntegral numberOfNegativeOperand - 1 else fromIntegral numberOfNegativeOperand
                       in ((start, currentLimbWidth, resultLimb, operandLimbs, compensatedConstant') : acc, nextBorrow)
                  )
                  ([], 0)
                  [0, limbWidth .. width - 1]
      foldM_ (addLimbs width maxHeight carryWidth) [] ranges

-- | Maximum number of limbs allowed to be added at once
maxHeightAllowed :: M n Int
maxHeightAllowed = do
  w <- gets (fieldWidth . cmField)
  if w <= 10
    then return (2 ^ (w - 1))
    else return 256

addLimbs :: (GaloisField n, Integral n) => Width -> Int -> Int -> [Limb] -> (Int, Int, Limb, [Limb], Integer) -> M n [Limb]
addLimbs width maxHeight carryWidth previousCarries (limbStart, currentLimbWidth, resultLimb, limbs, constant) = do
  addLimbs' width maxHeight carryWidth resultLimb (limbStart, currentLimbWidth, previousCarries <> limbs, constant)

addLimbs' :: (GaloisField n, Integral n) => Width -> Int -> Int -> Limb -> (Int, Int, [Limb], Integer) -> M n [Limb]
addLimbs' width maxHeight carryWidth out (limbStart, currentLimbWidth, limbs, constant) = do
  let (currentBatch, nextBatch) = splitAt (maxHeight - if constant == 0 then 0 else 1) limbs
  if null nextBatch
    then do
      addLimitedLimbs width carryWidth [] (limbStart, currentLimbWidth, out, currentBatch, constant)
    else do
      tempResultLimb <- allocLimb currentLimbWidth limbStart True
      x <- addLimitedLimbs width carryWidth [] (limbStart, currentLimbWidth, tempResultLimb, currentBatch, constant)
      xs <- addLimbs' width maxHeight carryWidth out (limbStart, currentLimbWidth, tempResultLimb : nextBatch, 0)
      return $ x <> xs

addLimitedLimbs :: (GaloisField n, Integral n) => Width -> Int -> [Limb] -> (Int, Int, Limb, [Limb], Integer) -> M n [Limb]
addLimitedLimbs width carryWidth previousCarries (limbStart, currentLimbWidth, resultLimb, limbs, constant) = do
  -- traceShowM (constant, map limbSign limbs)
  carryLimb <- allocLimb carryWidth (limbStart + currentLimbWidth) True
  -- limbs + previousCarryLimb = resultLimb + carryLimb
  writeAddWithSeq (fromInteger constant) $
    mconcat (map (toBits width 0 True) previousCarries)
      <> mconcat (map (toBits width 0 True) limbs)
      <> toBits width 0 False resultLimb
      <> toBits width currentLimbWidth False carryLimb -- multiply carryBits by `2^currentLimbWidth` and negate it
  return [carryLimb]

compileSubU :: (GaloisField n, Integral n) => Width -> RefU -> Either RefU Integer -> Either RefU Integer -> M n ()
compileSubU width out (Right a) (Right b) = compileAddU width out [] (a - b)
compileSubU width out (Right a) (Left b) = compileAddU width out [(b, False)] a
compileSubU width out (Left a) (Right b) = compileAddU width out [(a, True)] (-b)
compileSubU width out (Left a) (Left b) = compileAddU width out [(a, True), (b, False)] 0

--------------------------------------------------------------------------------

data Limb = Limb
  { -- | Which RefU this limb belongs to
    limbRef :: RefU,
    -- | How wide this limb is
    limbWidth :: Width,
    -- | The offset of this limb
    limbOffset :: Int,
    -- | True if this limb is positive, False if negative
    limbSign :: Bool
  }
  deriving (Show)

allocLimb :: (GaloisField n, Integral n) => Width -> Int -> Bool -> M n Limb
allocLimb w offset sign = do
  refU <- freshRefU w
  mapM_ addBooleanConstraint [RefUBit w refU i | i <- [0 .. w - 1]]
  return $
    Limb
      { limbRef = refU,
        limbWidth = w,
        limbOffset = offset,
        limbSign = sign
      }

-- | Given the UInt width, limb offset, and a limb, construct a sequence of bits.
toBits :: (GaloisField n, Integral n) => Int -> Int -> Bool -> Limb -> Seq (Ref, n)
toBits width powerOffset dontFlip limb =
  Seq.fromFunction
    (limbWidth limb)
    ( \i ->
        ( B (RefUBit width (limbRef limb) (limbOffset limb + i)),
          if not (limbSign limb `xor` dontFlip)
            then 2 ^ (powerOffset + i :: Int)
            else -(2 ^ (powerOffset + i :: Int))
        )
    )
