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
import Debug.Trace

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

  let numberOfOperands = length vars

  -- calculate the expected width of the carry limbs, which is logarithimic to the number of operands
  let expectedCarryWidth =
        ceiling (logBase 2 (fromIntegral numberOfOperands + if constant == 0 then 0 else 1) :: Double) `max` 2 :: Int

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
            dimMaxHeight = 2 ^ (carryWidth - 1),
            dimCarryWidth = carryWidth - 1
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
                      operandLimbs = [Limb var currentLimbWidth start (replicate currentLimbWidth sign) | (var, sign) <- vars]
                      -- negative limbs
                      resultLimb = Limb out currentLimbWidth start (replicate currentLimbWidth True)
                      constantSegment = sum [(if Data.Bits.testBit constant (start + i) then 1 else 0) * (2 ^ i) | i <- [0 .. currentLimbWidth - 1]]
                   in (start, currentLimbWidth, constantSegment, resultLimb, operandLimbs)
              )
              [0, limbWidth .. width - 1]
      foldM_
        ( \prevCarries (start, currentLimbWidth, constant', resultLimb, limbs) ->
            addWholeColumn dimensions start currentLimbWidth constant' resultLimb (prevCarries <> limbs)
        )
        []
        ranges

data Dimensions = Dimensions
  { dimUIntWidth :: Int,
    dimMaxHeight :: Int,
    dimCarryWidth :: Int
  }
  deriving (Show)

-- | Compress a column of limbs into a single limb and some carry
--
--              [ operand+ ]
--              [ operand+ ]    positive operands
--  +           [ operand+ ]
-- -----------------------------
--    [ carry  ][  result  ]
addPartialColumn :: (GaloisField n, Integral n) => Dimensions -> Int -> Int -> Limb -> n -> [Limb] -> M n Limb
addPartialColumn dimensions limbStart currentLimbWidth resultLimb constant limbs = do
  let negLimbSize = length $ filter (not . limbIsPositive) limbs

  -- if all limbs are negative, we should add 2^currentLimbWidth to the constant
  let allNegative = negLimbSize == length limbs
  if allNegative
    then do
      let carrySigns = replicate (dimCarryWidth dimensions + 1) False
      carryLimb <- allocCarryLimb (dimCarryWidth dimensions + 1) limbStart carrySigns
      let compensatedConstant = constant
      -- let compensatedConstant = constant + 2 ^ currentLimbWidth
      writeAddWithSeq compensatedConstant $
        -- positive side
        mconcat (map (toBits (dimUIntWidth dimensions) 0 True) limbs)
          -- negative side
          <> toBits (dimUIntWidth dimensions) 0 False resultLimb
          <> toBits (dimUIntWidth dimensions) currentLimbWidth False carryLimb
      return carryLimb
    else do
      let carrySigns = map (not . Data.Bits.testBit negLimbSize) [0 .. dimCarryWidth dimensions - 1]
      carryLimb <- allocCarryLimb (dimCarryWidth dimensions) limbStart carrySigns
      writeAddWithSeq constant $
        -- positive side
        mconcat (map (toBits (dimUIntWidth dimensions) 0 True) limbs)
          -- negative side
          <> toBits (dimUIntWidth dimensions) 0 False resultLimb
          <> toBits (dimUIntWidth dimensions) currentLimbWidth False carryLimb
      return carryLimb

addWholeColumn :: (GaloisField n, Integral n) => Dimensions -> Int -> Int -> n -> Limb -> [Limb] -> M n [Limb]
addWholeColumn dimensions limbStart currentLimbWidth constant finalResultLimb limbs = do
  let (currentBatch, nextBatch) = splitAt (dimMaxHeight dimensions) limbs
  if not (null nextBatch) || (length currentBatch == dimMaxHeight dimensions && constant /= 0)
    then do
      -- inductive case, there are more limbs to be processed
      resultLimb <- allocLimb currentLimbWidth limbStart True
      carryLimb <- addPartialColumn dimensions limbStart currentLimbWidth resultLimb 0 currentBatch
      -- insert the result limb of the current batch to the next batch
      moreCarryLimbs <- addWholeColumn dimensions limbStart currentLimbWidth constant finalResultLimb (resultLimb : nextBatch)
      -- (moreCarryLimbs, compensated') <- addWholeColumn dimensions limbStart currentLimbWidth (constant - if compensated then 2 ^ currentLimbWidth else 0) finalResultLimb (resultLimb : nextBatch)
      return (carryLimb : moreCarryLimbs)
    else do
      -- edge case, all limbs are in the current batch
      carryLimb <- addPartialColumn dimensions limbStart currentLimbWidth finalResultLimb constant currentBatch
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
    lmbOffset :: Int,
    -- | Signs of each bit, LSB first
    lmbSigns :: [Bool]
  }
  deriving (Show)

-- | A limb is considered "positive" if all of its bits are positive
limbIsPositive :: Limb -> Bool
limbIsPositive = and . lmbSigns

fromLimb :: Limb -> RefU
fromLimb = lmbRef

allocLimb :: (GaloisField n, Integral n) => Width -> Int -> Bool -> M n Limb
allocLimb w offset sign = do
  refU <- freshRefU w
  mapM_ addBooleanConstraint [RefUBit w refU i | i <- [0 .. w - 1]]
  return $
    Limb
      { lmbRef = refU,
        lmbWidth = w,
        lmbOffset = offset,
        lmbSigns = replicate w sign
      }

allocCarryLimb :: (GaloisField n, Integral n) => Width -> Int -> [Bool] -> M n Limb
allocCarryLimb w offset signs = do
  refU <- freshRefU w
  mapM_ addBooleanConstraint [RefUBit w refU i | i <- [0 .. w - 1]]
  return $
    Limb
      { lmbRef = refU,
        lmbWidth = w,
        lmbOffset = offset,
        lmbSigns = signs
      }

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
      [0 ..]
      (lmbSigns limb)

toBitsB :: (GaloisField n, Integral n) => Int -> Int -> Bool -> Limb -> Seq (RefB, n)
toBitsB width powerOffset positive limb =
  Seq.fromList $
    zipWith
      ( \i sign ->
          ( RefUBit width (lmbRef limb) (lmbOffset limb + i),
            if (if sign then positive else not positive)
              then 2 ^ (powerOffset + i :: Int)
              else -(2 ^ (powerOffset + i :: Int))
          )
      )
      [0 ..]
      (lmbSigns limb)

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
compileMulU :: (GaloisField n, Integral n) => Int -> RefU -> Either RefU Integer -> Either RefU Integer -> M n ()
compileMulU width out (Right a) (Right b) = do
  let val = a * b
  writeValU width out val
compileMulU width out (Right a) (Left b) = do
  carry <- replicateM width (B <$> freshRefB)
  let bs = [(B (RefUBit width b i), 2 ^ i) | i <- [0 .. width - 1]]
  let carrySegment = zip carry [2 ^ i | i <- [width .. width * 2 - 1]]
  let outputSegment = [(B (RefUBit width out i), 2 ^ i) | i <- [0 .. width - 1]]
  writeMul (fromInteger a, []) (0, bs) (0, outputSegment <> carrySegment)
compileMulU width out (Left a) (Right b) = compileMulU width out (Right b) (Left a)
compileMulU width out (Left a) (Left b) = do
  compileMulVV width out a b
  -- carry <- replicateM width (B <$> freshRefB)

  -- let as = [(B (RefUBit width a i), 2 ^ i) | i <- [0 .. width - 1]]
  -- let bs = [(B (RefUBit width b i), 2 ^ i) | i <- [0 .. width - 1]]
  -- let carrySegment = zip carry [2 ^ i | i <- [width .. width * 2 - 1]]
  -- let outputSegment = [(B (RefUBit width out i), 2 ^ i) | i <- [0 .. width - 1]]

  -- writeMul (0, as) (0, bs) (0, outputSegment <> carrySegment)

mul2Limbs :: (GaloisField n, Integral n) => Width -> Int -> (n, Limb) -> (n, Limb) -> M n (Limb, Limb)
mul2Limbs currentLimbWidth limbStart (a, x) (b, y) = do
  lowerLimb <- allocLimb currentLimbWidth limbStart True
  upperLimb <- allocLimb currentLimbWidth (limbStart + currentLimbWidth) True

  -- traceShowM (toBits currentLimbWidth limbStart True x :: Seq (Ref, n))
  writeMulWithSeq
    (a, toBits currentLimbWidth limbStart True x)
    (b, toBits currentLimbWidth limbStart True y)
    ( 0,
      toBits currentLimbWidth (limbStart + currentLimbWidth) True upperLimb
        <> toBits currentLimbWidth limbStart True lowerLimb
    )

  return (lowerLimb, upperLimb)

compileMulVV :: (GaloisField n, Integral n) => Width -> RefU -> RefU -> RefU -> M n ()
compileMulVV width out x y = do
  fieldInfo <- gets cmField

  -- invariants about widths of carry and limbs:
  --  1. limb width * 2 ≤ field width
  let limbWidth = fieldWidth fieldInfo `div` 2

  case fieldTypeData fieldInfo of
    Binary _ -> throwError $ Error.FieldNotSupported (fieldTypeData fieldInfo)
    Prime 2 -> throwError $ Error.FieldNotSupported (fieldTypeData fieldInfo)
    Prime 3 -> throwError $ Error.FieldNotSupported (fieldTypeData fieldInfo)
    Prime 5 -> throwError $ Error.FieldNotSupported (fieldTypeData fieldInfo)
    Prime 7 -> throwError $ Error.FieldNotSupported (fieldTypeData fieldInfo)
    Prime 11 -> throwError $ Error.FieldNotSupported (fieldTypeData fieldInfo)
    Prime 13 -> throwError $ Error.FieldNotSupported (fieldTypeData fieldInfo)
    _ -> do
      -- TEMP HACK
      if width > limbWidth 
        then throwError $ Error.FieldNotSupported (fieldTypeData fieldInfo)
        else do
          let currentLimbWidth = width
          let limbStart = 0
          let operandLimbX = Limb x currentLimbWidth limbStart (replicate currentLimbWidth True)
          let operandLimbY = Limb y currentLimbWidth limbStart (replicate currentLimbWidth True)
          (lower, _upper) <- mul2Limbs currentLimbWidth limbStart (0, operandLimbX) (0, operandLimbY)

          writeEqU width out (lmbRef lower)

      -- let ranges =
      --       map
      --         ( \start ->
      --             let currentLimbWidth = limbWidth `min` (fieldWidth fieldInfo - start)
      --                 operandLimbX = Limb x currentLimbWidth start (replicate currentLimbWidth True)
      --                 operandLimbY = Limb y currentLimbWidth start (replicate currentLimbWidth True)
      --                 -- negative limbs
      --                 resultLimb = Limb out currentLimbWidth start (replicate currentLimbWidth True)
      --              in (start, currentLimbWidth, resultLimb, operandLimbX, operandLimbY)
      --         )
      --         [0, limbWidth .. fieldWidth fieldInfo - 1]
      -- foldM_
      --   ( \prevCarries (start, currentLimbWidth, resultLimb, operandLimbX, operandLimbY) ->
      --       mul2Limbs currentLimbWidth start (0, operandLimbX) (0, operandLimbY)
      --   )
      --   []
      --   ranges
