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
--              [ operand+ ]
--              [ operand+ ]    positive operands
--  + [ borrow ][ operand+ ]
-- -----------------------------
--    [ carry  ][  result  ]
--              [ operand- ]    negative operands (including the result)
--              [ operand- ]
--
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
  let numberOfNegativeOperands = length (filter (not . snd) vars)
  let numberOfPositiveOperands = numberOfOperands - numberOfNegativeOperands

  -- calculate the pile height on both side of the addition
  let positivePileHeight =
        numberOfPositiveOperands -- positive operands
          + (if constant > 0 then 1 else 0) -- positive constant
  let negativePileHeight =
        numberOfNegativeOperands -- negative operands
          + (if constant < 0 then 1 else 0) -- negative constant
          + 1 -- the result

  -- calculate the expected width of the carry and borrow limbs
  -- NOTE, we use the same width for all limbs on the both sides for the moment (they can be different)
  let expectedCarryWidth = ceiling (logBase 2 (fromIntegral positivePileHeight) :: Double) :: Int
  let expectedBorrowWidth = ceiling (logBase 2 (fromIntegral negativePileHeight) :: Double) :: Int

  -- calculate the width of the limbs, both the limb and the carry (or borrow) needs to fit in a field
  let limbWidth = (fieldWidth fieldInfo - (expectedCarryWidth `max` expectedBorrowWidth)) `max` 1

  let carryWidth = fieldWidth fieldInfo - limbWidth
  let borrowWidth = fieldWidth fieldInfo - limbWidth

  maxHeight <- maxHeightAllowed
  let dimensions =
        Dimensions
          { dimUIntWidth = width,
            dimMaxHeight = maxHeight,
            dimCarryWidth = carryWidth,
            dimBorrowWidth = borrowWidth
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
                      positiveLimbs = [Limb var currentLimbWidth start | (var, sign) <- vars, sign]
                      negativeLimbs = [Limb var currentLimbWidth start | (var, sign) <- vars, not sign]
                      -- negative limbs
                      resultLimb = Limb out currentLimbWidth start
                      constantSegment = sum [(if Data.Bits.testBit constant (start + i) then 1 else 0) * (2 ^ i) | i <- [0 .. currentLimbWidth - 1]]
                   in (start, currentLimbWidth, constantSegment, (positiveLimbs, resultLimb : negativeLimbs))
              )
              [0, limbWidth .. width - 1]
      foldM_ (\(prevCarries, prevBorrows) (start, limbWidth', constant', (posLimbs, negLimbs)) -> compileWholeLimbPile dimensions start limbWidth' (prevCarries, prevBorrows) constant' (posLimbs, negLimbs)) ([], []) ranges

-- foldM_ (addLimbs width maxHeight carryWidth) [] ranges

data Dimensions = Dimensions
  { dimUIntWidth :: Int,
    dimMaxHeight :: Int,
    dimCarryWidth :: Int,
    dimBorrowWidth :: Int
  }

-- | Compress a pile of limbs into a single limb and some carry
--
--              [ operand+ ]
--              [ operand+ ]    positive operands
--  +           [ operand+ ]
-- -----------------------------
--    [ carry  ][  result  ]
compileSingleLimbPile :: (GaloisField n, Integral n) => Dimensions -> Int -> Int -> [Limb] -> M n ([Limb], [Limb])
compileSingleLimbPile dimensions limbStart currentLimbWidth limbs = do
  carryLimb <- allocLimb (dimCarryWidth dimensions) (limbStart + currentLimbWidth)
  resultLimb <- allocLimb currentLimbWidth limbStart
  -- limbs = resultLimb + carryLimb
  writeAddWithSeq 0 $
    -- positive side
    mconcat (map (toBits (dimUIntWidth dimensions) 0 True) limbs)
      -- negative side
      <> toBits (dimUIntWidth dimensions) 0 False resultLimb
      <> toBits (dimUIntWidth dimensions) currentLimbWidth False carryLimb -- multiply carryBits by `2^currentLimbWidth` and negate it
  return ([carryLimb], [resultLimb])

compileWholeLimbPile :: (GaloisField n, Integral n) => Dimensions -> Int -> Int -> ([Limb], [Limb]) -> n -> ([Limb], [Limb]) -> M n ([Limb], [Limb])
compileWholeLimbPile dimensions limbStart currentLimbWidth (prevCarries, prevBorrows) constant (posLimbs, negLimbs) = do
  -- positive piles
  -- let (currentBatch, nextBatch) = splitAt (dimMaxHeight dimensions) posLimbs
  carryLimbs <- 
    if constant > 0 
      then 
        if null posLimbs
          then return []
          else pure <$> allocLimb (dimCarryWidth dimensions) (limbStart + currentLimbWidth)
      else 
        if length posLimbs < 2
          then return []
          else pure <$> allocLimb (dimCarryWidth dimensions) (limbStart + currentLimbWidth)
  borrowLimbs <-
    if constant < 0 
      then 
        if null negLimbs
          then return []
          else pure <$> allocLimb (dimBorrowWidth dimensions) (limbStart + currentLimbWidth)
      else 
        if length negLimbs < 2 
          then return []
          else pure <$> allocLimb (dimBorrowWidth dimensions) (limbStart + currentLimbWidth)

  -- limbs = resultLimb + carryLimb
  writeAddWithSeq constant $
    -- positive side
    mconcat (map (toBits (dimUIntWidth dimensions) 0 True) posLimbs)
      <> mconcat (map (toBits (dimUIntWidth dimensions) 0 True) prevCarries)
      <> mconcat (map (toBits (dimUIntWidth dimensions) currentLimbWidth True) borrowLimbs) -- multiply by `2^currentLimbWidth`
      -- negative side
      <> mconcat (map (toBits (dimUIntWidth dimensions) 0 False) negLimbs)
      <> mconcat (map (toBits (dimUIntWidth dimensions) 0 False) prevBorrows)
      <> mconcat (map (toBits (dimUIntWidth dimensions) currentLimbWidth False) carryLimbs) -- multiply by `2^currentLimbWidth`
  return (carryLimbs, borrowLimbs)

-- writeAddWithSeq (fromInteger constant) $
--   mconcat (map (toBits width 0 True) previousCarries)
--     <> mconcat (map (toBits width 0 True) limbs)
--     <> toBits width 0 False resultLimb
--     <> toBits width currentLimbWidth False carryLimb -- multiply carryBits by `2^currentLimbWidth` and negate it
--   return [carryLimb]

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
      tempResultLimb <- allocLimb currentLimbWidth limbStart
      x <- addLimitedLimbs width carryWidth [] (limbStart, currentLimbWidth, tempResultLimb, currentBatch, constant)
      xs <- addLimbs' width maxHeight carryWidth out (limbStart, currentLimbWidth, tempResultLimb : nextBatch, 0)
      return $ x <> xs

addLimitedLimbs :: (GaloisField n, Integral n) => Width -> Int -> [Limb] -> (Int, Int, Limb, [Limb], Integer) -> M n [Limb]
addLimitedLimbs width carryWidth previousCarries (limbStart, currentLimbWidth, resultLimb, limbs, constant) = do
  carryLimb <- allocLimb carryWidth (limbStart + currentLimbWidth)
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
    lmbRef :: RefU,
    -- | How wide this limb is
    lmbWidth :: Width,
    -- | The offset of this limb
    lmbOffset :: Int
  }
  deriving (Show)

allocLimb :: (GaloisField n, Integral n) => Width -> Int -> M n Limb
allocLimb w offset = do
  refU <- freshRefU w
  mapM_ addBooleanConstraint [RefUBit w refU i | i <- [0 .. w - 1]]
  return $
    Limb
      { lmbRef = refU,
        lmbWidth = w,
        lmbOffset = offset
      }

-- | Given the UInt width, limb offset, and a limb, construct a sequence of bits.
toBits :: (GaloisField n, Integral n) => Int -> Int -> Bool -> Limb -> Seq (Ref, n)
toBits width powerOffset positive limb =
  Seq.fromFunction
    (lmbWidth limb)
    ( \i ->
        ( B (RefUBit width (lmbRef limb) (lmbOffset limb + i)),
          if positive
            then 2 ^ (powerOffset + i :: Int)
            else -(2 ^ (powerOffset + i :: Int))
        )
    )
