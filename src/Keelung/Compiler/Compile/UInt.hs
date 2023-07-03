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
import Keelung.Data.FieldInfo (FieldInfo (..))

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

toBitsC :: (GaloisField n, Integral n) => Int -> Int -> Bool -> Limb -> n -> Seq (Ref, n)
toBitsC width powerOffset positive limb constant =
  Seq.fromList $
    zipWith
      ( \i sign ->
          ( B (RefUBit width (lmbRef limb) (lmbOffset limb + i)),
            constant
              * if (if sign then positive else not positive)
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
compileMulU width out (Right a) (Left b) = compileMulCV width out a b
-- carry <- replicateM width (B <$> freshRefB)
-- let bs = [(B (RefUBit width b i), 2 ^ i) | i <- [0 .. width - 1]]
-- let carrySegment = zip carry [2 ^ i | i <- [width .. width * 2 - 1]]
-- let outputSegment = [(B (RefUBit width out i), 2 ^ i) | i <- [0 .. width - 1]]
-- writeMul (fromInteger a, []) (0, bs) (0, outputSegment <> carrySegment)
compileMulU width out (Left a) (Right b) = compileMulCV width out b a
compileMulU width out (Left a) (Left b) = do
  compileMulVV width out a b

-- carry <- replicateM width (B <$> freshRefB)

-- let as = [(B (RefUBit width a i), 2 ^ i) | i <- [0 .. width - 1]]
-- let bs = [(B (RefUBit width b i), 2 ^ i) | i <- [0 .. width - 1]]
-- let carrySegment = zip carry [2 ^ i | i <- [width .. width * 2 - 1]]
-- let outputSegment = [(B (RefUBit width out i), 2 ^ i) | i <- [0 .. width - 1]]

-- writeMul (0, as) (0, bs) (0, outputSegment <> carrySegment)

compileMulCV :: (GaloisField n, Integral n) => Width -> RefU -> Integer -> RefU -> M n ()
compileMulCV width out c x = do
  fieldInfo <- gets cmField

  -- invariants about widths of carry and limbs:
  --  1. limb width * 2 ≤ field width

  let maxLimbWidth = fieldWidth fieldInfo `div` 2
  let minLimbWidth = 2 -- TEMPORARY HACK FOR ADDITION
  let limbWidth = minLimbWidth `max` widthOf x `min` maxLimbWidth

  let dimensions =
        Dimensions
          { dimUIntWidth = width,
            dimMaxHeight = 2 ^ limbWidth,
            dimCarryWidth = limbWidth
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
      let limbNumber = ceiling (fromIntegral width / fromIntegral limbWidth :: Double) :: Int

      let currentLimbWidth = limbWidth
      let limbStart = 0
      case limbNumber of
        1 -> do
          let x0 = Limb x currentLimbWidth limbStart (replicate currentLimbWidth True)
          mul1x1c dimensions currentLimbWidth limbStart out x0 c
        2 -> do
          let x0 = Limb x currentLimbWidth limbStart (replicate currentLimbWidth True)
          let x1 = Limb x currentLimbWidth (limbStart + currentLimbWidth) (replicate currentLimbWidth True)
          mul2x2c dimensions currentLimbWidth limbStart out x0 x1 c
        3 -> do
          let x0 = Limb x currentLimbWidth limbStart (replicate currentLimbWidth True)
          let x1 = Limb x currentLimbWidth (limbStart + currentLimbWidth) (replicate currentLimbWidth True)
          let x2 = Limb x currentLimbWidth (limbStart + currentLimbWidth * 2) (replicate currentLimbWidth True)
          mul3x3c dimensions currentLimbWidth limbStart out x0 x1 x2 c
        _ -> throwError $ Error.FieldNotSupported (fieldTypeData fieldInfo)

compileMulVV :: (GaloisField n, Integral n) => Width -> RefU -> RefU -> RefU -> M n ()
compileMulVV width out x y = do
  fieldInfo <- gets cmField

  -- invariants about widths of carry and limbs:
  --  1. limb width * 2 ≤ field width
  let maxLimbWidth = fieldWidth fieldInfo `div` 2
  let minLimbWidth = 2 -- TEMPORARY HACK FOR ADDITION
  let limbWidth = minLimbWidth `max` widthOf x `min` maxLimbWidth

  let dimensions =
        Dimensions
          { dimUIntWidth = width,
            dimMaxHeight = 2 ^ limbWidth,
            dimCarryWidth = limbWidth
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
      let limbNumber = ceiling (fromIntegral width / fromIntegral limbWidth :: Double) :: Int

      case limbNumber of
        1 -> do
          let currentLimbWidth = limbWidth
          let limbStart = 0
          let x0 = Limb x currentLimbWidth limbStart (replicate currentLimbWidth True)
          let y0 = Limb y currentLimbWidth limbStart (replicate currentLimbWidth True)
          mul1x1 dimensions currentLimbWidth limbStart out x0 y0
        2 -> do
          let currentLimbWidth = limbWidth
          let limbStart = 0
          let x0 = Limb x currentLimbWidth limbStart (replicate currentLimbWidth True)
          let x1 = Limb x currentLimbWidth (limbStart + currentLimbWidth) (replicate currentLimbWidth True)
          let y0 = Limb y currentLimbWidth limbStart (replicate currentLimbWidth True)
          let y1 = Limb y currentLimbWidth (limbStart + currentLimbWidth) (replicate currentLimbWidth True)
          mul2x2 dimensions currentLimbWidth limbStart out x0 x1 y0 y1
        3 -> do
          let currentLimbWidth = limbWidth
          let limbStart = 0
          let x0 = Limb x currentLimbWidth limbStart (replicate currentLimbWidth True)
          let x1 = Limb x currentLimbWidth (limbStart + currentLimbWidth) (replicate currentLimbWidth True)
          let x2 = Limb x currentLimbWidth (limbStart + currentLimbWidth * 2) (replicate currentLimbWidth True)
          let y0 = Limb y currentLimbWidth limbStart (replicate currentLimbWidth True)
          let y1 = Limb y currentLimbWidth (limbStart + currentLimbWidth) (replicate currentLimbWidth True)
          let y2 = Limb y currentLimbWidth (limbStart + currentLimbWidth * 2) (replicate currentLimbWidth True)
          mul3x3 dimensions currentLimbWidth limbStart out x0 x1 x2 y0 y1 y2
        _ -> throwError $ Error.FieldNotSupported (fieldTypeData fieldInfo)

mul2Limbs :: (GaloisField n, Integral n) => Dimensions -> Width -> Int -> (n, Limb) -> Either n (n, Limb) -> M n (Limb, Limb)
mul2Limbs dimensions currentLimbWidth limbStart (a, x) operand = do
  upperLimb <- allocLimb currentLimbWidth (limbStart + currentLimbWidth) True
  lowerLimb <- allocLimb currentLimbWidth limbStart True
  case operand of
    Left constant ->
      writeAddWithSeq (a * constant) $
        -- operand side
        toBitsC (dimUIntWidth dimensions) 0 True x constant
          -- negative side
          <> toBits (dimUIntWidth dimensions) 0 False lowerLimb
          <> toBits (dimUIntWidth dimensions) currentLimbWidth False upperLimb
    Right (b, y) ->
      writeMulWithSeq
        (a, toBits (dimUIntWidth dimensions) 0 True x)
        (b, toBits (dimUIntWidth dimensions) 0 True y)
        ( 0,
          toBits (dimUIntWidth dimensions) 0 True lowerLimb
            <> toBits (dimUIntWidth dimensions) currentLimbWidth True upperLimb
        )

  return (lowerLimb, upperLimb)

mul2LimbPreallocated :: (GaloisField n, Integral n) => Dimensions -> Width -> Int -> (n, Limb) -> Either n (n, Limb) -> Limb -> M n Limb
mul2LimbPreallocated dimensions currentLimbWidth limbStart (a, x) operand lowerLimb = do
  upperLimb <- allocLimb currentLimbWidth (limbStart + currentLimbWidth) True
  case operand of
    Left constant ->
      writeAddWithSeq (a * constant) $
        -- operand side
        toBitsC (dimUIntWidth dimensions) 0 True x constant
          -- negative side
          <> toBits (dimUIntWidth dimensions) 0 False lowerLimb
          <> toBits (dimUIntWidth dimensions) currentLimbWidth False upperLimb
    Right (b, y) ->
      writeMulWithSeq
        (a, toBits (dimUIntWidth dimensions) 0 True x)
        (b, toBits (dimUIntWidth dimensions) 0 True y)
        ( 0,
          toBits (dimUIntWidth dimensions) 0 True lowerLimb
            <> toBits (dimUIntWidth dimensions) currentLimbWidth True upperLimb
        )

  return upperLimb

-- | 1-limb by 1-limb multiplication
--                             x0
-- x                           y0
-- ------------------------------------------
--                          x0*y0
mul1x1 :: (GaloisField n, Integral n) => Dimensions -> Width -> Int -> RefU -> Limb -> Limb -> M n ()
mul1x1 dimensions currentLimbWidth limbStart out x0 y0 = do
  -- let operandLimbX = Limb x currentLimbWidth limbStart (replicate currentLimbWidth True)
  -- let operandLimbY = Limb y currentLimbWidth limbStart (replicate currentLimbWidth True)
  let resultLimb = Limb out currentLimbWidth limbStart (replicate currentLimbWidth True)
  _upper <- mul2LimbPreallocated dimensions currentLimbWidth limbStart (0, x0) (Right (0, y0)) resultLimb
  -- writeEqU (dimUIntWidth dimensions) out (lmbRef lower)
  return ()

-- | 1-limb by 1-limb multiplication
--                             x0
-- x                           c0
-- ------------------------------------------
--                          c0*y0
mul1x1c :: (GaloisField n, Integral n) => Dimensions -> Width -> Int -> RefU -> Limb -> Integer -> M n ()
mul1x1c dimensions currentLimbWidth limbStart out x0 constant = do
  let constantSegment = sum [(if Data.Bits.testBit constant (limbStart + i) then 1 else 0) * (2 ^ i) | i <- [0 .. currentLimbWidth - 1]]
  -- let operandLimbX = Limb x currentLimbWidth limbStart (replicate currentLimbWidth True)
  -- let operandLimbY = Limb y currentLimbWidth limbStart (replicate currentLimbWidth True)
  let resultLimb = Limb out currentLimbWidth limbStart (replicate currentLimbWidth True)
  _upper <- mul2LimbPreallocated dimensions currentLimbWidth limbStart (0, x0) (Left constantSegment) resultLimb
  return ()

-- | 2-limb by 2-limb multiplication
--                          x1 x0
-- x                        y1 y0
-- ------------------------------------------
--                          x0*y0
--                       x1*y0
--                       x0*y1
--                    x1*y1
-- ------------------------------------------
mul2x2 :: (GaloisField n, Integral n) => Dimensions -> Width -> Int -> RefU -> Limb -> Limb -> Limb -> Limb -> M n ()
mul2x2 dimensions currentLimbWidth limbStart out x0 x1 y0 y1 = do
  (lowerX0Y0, upperX0Y0) <- mul2Limbs dimensions currentLimbWidth limbStart (0, x0) (Right (0, y0))
  (lowerX1Y0, _upperX1Y0) <- mul2Limbs dimensions currentLimbWidth (limbStart + currentLimbWidth) (0, x1) (Right (0, y0))
  (lowerX0Y1, _upperX0Y1) <- mul2Limbs dimensions currentLimbWidth (limbStart + currentLimbWidth) (0, x0) (Right (0, y1))
  -- (_lowerX1Y1, _upperX1Y1) <- mul2Limbs dimensions currentLimbWidth (limbStart + currentLimbWidth * 2) (0, x1) (0, y1)

  -- column 0
  writeEqU currentLimbWidth out (lmbRef lowerX0Y0)
  -- column 1
  let resultLimb1 = Limb out currentLimbWidth (limbStart + currentLimbWidth) (replicate currentLimbWidth True)
  _ <- addWholeColumn dimensions limbStart currentLimbWidth 0 resultLimb1 [upperX0Y0, lowerX1Y0, lowerX0Y1]
  return ()

-- | 2-limb by 2-limb multiplication
--                          x1 x0
-- x                        y1 y0
-- ------------------------------------------
--                          x0*y0
--                       x1*y0
--                       x0*y1
--                    x1*y1
-- ------------------------------------------
mul2x2c :: (GaloisField n, Integral n) => Dimensions -> Width -> Int -> RefU -> Limb -> Limb -> Integer -> M n ()
mul2x2c dimensions currentLimbWidth limbStart out x0 x1 constant = do
  let c0 = sum [(if Data.Bits.testBit constant (limbStart + i) then 1 else 0) * (2 ^ i) | i <- [0 .. currentLimbWidth - 1]]
  let c1 = sum [(if Data.Bits.testBit constant (limbStart + currentLimbWidth + i) then 1 else 0) * (2 ^ i) | i <- [0 .. currentLimbWidth - 1]]
  (lowerX0Y0, upperX0Y0) <- mul2Limbs dimensions currentLimbWidth limbStart (0, x0) (Left c0)
  (lowerX1Y0, _) <- mul2Limbs dimensions currentLimbWidth (limbStart + currentLimbWidth) (0, x1) (Left c0)
  (lowerX0Y1, _) <- mul2Limbs dimensions currentLimbWidth (limbStart + currentLimbWidth) (0, x0) (Left c1)

  -- column 0
  writeEqU currentLimbWidth out (lmbRef lowerX0Y0)
  -- column 1
  let resultLimb1 = Limb out currentLimbWidth (limbStart + currentLimbWidth) (replicate currentLimbWidth True)
  _ <- addWholeColumn dimensions limbStart currentLimbWidth 0 resultLimb1 [upperX0Y0, lowerX1Y0, lowerX0Y1]
  return ()

-- | 3-limb by 3-limb multiplication
--                          x2 x1 x0
-- x                        y2 y1 y0
-- ------------------------------------------
--                             x0*y0
--                          x1*y0
--                       x2*y0
--                          x0*y1
--                       x1*y1
--                    x2*y1
--                       x0*y2
--                    x1*y2
--                 x2*y2
-- ------------------------------------------
mul3x3 :: (GaloisField n, Integral n) => Dimensions -> Width -> Int -> RefU -> Limb -> Limb -> Limb -> Limb -> Limb -> Limb -> M n ()
mul3x3 dimensions currentLimbWidth limbStart out x0 x1 x2 y0 y1 y2 = do
  (lowerX0Y0, upperX0Y0) <- mul2Limbs dimensions currentLimbWidth limbStart (0, x0) (Right (0, y0))
  (lowerX1Y0, upperX1Y0) <- mul2Limbs dimensions currentLimbWidth (limbStart + currentLimbWidth) (0, x1) (Right (0, y0))
  (lowerX2Y0, _upperX2Y0) <- mul2Limbs dimensions currentLimbWidth (limbStart + currentLimbWidth * 2) (0, x2) (Right (0, y0))
  (lowerX0Y1, upperX0Y1) <- mul2Limbs dimensions currentLimbWidth (limbStart + currentLimbWidth) (0, x0) (Right (0, y1))
  (lowerX1Y1, _upperX1Y1) <- mul2Limbs dimensions currentLimbWidth (limbStart + currentLimbWidth * 2) (0, x1) (Right (0, y1))
  (_lowerX2Y1, _upperX2Y1) <- mul2Limbs dimensions currentLimbWidth (limbStart + currentLimbWidth * 3) (0, x2) (Right (0, y1))
  (lowerX0Y2, _upperX0Y2) <- mul2Limbs dimensions currentLimbWidth (limbStart + currentLimbWidth * 2) (0, x0) (Right (0, y2))
  -- (lowerX1Y2, upperX1Y2) <- mul2Limbs dimensions currentLimbWidth (limbStart + currentLimbWidth * 3) (0, x1) (0, y2)
  -- (lowerX2Y2, upperX2Y2) <- mul2Limbs dimensions currentLimbWidth (limbStart + currentLimbWidth * 4) (0, x2) (0, y2)

  -- column 0
  writeEqU currentLimbWidth out (lmbRef lowerX0Y0)
  -- column 1
  let resultLimb1 = Limb out currentLimbWidth (limbStart + currentLimbWidth) (replicate currentLimbWidth True)
  column1CarryLimbs <- addWholeColumn dimensions limbStart currentLimbWidth 0 resultLimb1 [upperX0Y0, lowerX1Y0, lowerX0Y1]
  -- column 2
  let resultLimb2 = Limb out currentLimbWidth (limbStart + currentLimbWidth * 2) (replicate currentLimbWidth True)
  _ <- addWholeColumn dimensions limbStart currentLimbWidth 0 resultLimb2 $ column1CarryLimbs <> [upperX1Y0, upperX0Y1, lowerX2Y0, lowerX1Y1, lowerX0Y2]
  return ()

-- | 3-limb by 3-limb multiplication
--                          x2 x1 x0
-- x                        y2 y1 y0
-- ------------------------------------------
--                             x0*y0
--                          x1*y0
--                       x2*y0
--                          x0*y1
--                       x1*y1
--                    x2*y1
--                       x0*y2
--                    x1*y2
--                 x2*y2
-- ------------------------------------------
mul3x3c :: (GaloisField n, Integral n) => Dimensions -> Width -> Int -> RefU -> Limb -> Limb -> Limb -> Integer -> M n ()
mul3x3c dimensions currentLimbWidth limbStart out x0 x1 x2 constant = do
  let c0 = sum [(if Data.Bits.testBit constant (limbStart + i) then 1 else 0) * (2 ^ i) | i <- [0 .. currentLimbWidth - 1]]
  let c1 = sum [(if Data.Bits.testBit constant (limbStart + currentLimbWidth + i) then 1 else 0) * (2 ^ i) | i <- [0 .. currentLimbWidth - 1]]
  let c2 = sum [(if Data.Bits.testBit constant (limbStart + currentLimbWidth * 2 + i) then 1 else 0) * (2 ^ i) | i <- [0 .. currentLimbWidth - 1]]
  (lowerX0Y0, upperX0Y0) <- mul2Limbs dimensions currentLimbWidth limbStart (0, x0) (Left c0)
  (lowerX1Y0, upperX1Y0) <- mul2Limbs dimensions currentLimbWidth (limbStart + currentLimbWidth) (0, x1) (Left c0)
  (lowerX2Y0, _upperX2Y0) <- mul2Limbs dimensions currentLimbWidth (limbStart + currentLimbWidth * 2) (0, x2) (Left c0)
  (lowerX0Y1, upperX0Y1) <- mul2Limbs dimensions currentLimbWidth (limbStart + currentLimbWidth) (0, x0) (Left c1)
  (lowerX1Y1, _upperX1Y1) <- mul2Limbs dimensions currentLimbWidth (limbStart + currentLimbWidth * 2) (0, x1) (Left c1)
  (_lowerX2Y1, _upperX2Y1) <- mul2Limbs dimensions currentLimbWidth (limbStart + currentLimbWidth * 3) (0, x2) (Left c1)
  (lowerX0Y2, _upperX0Y2) <- mul2Limbs dimensions currentLimbWidth (limbStart + currentLimbWidth * 2) (0, x0) (Left c2)

  -- column 0
  writeEqU currentLimbWidth out (lmbRef lowerX0Y0)
  -- column 1
  let resultLimb1 = Limb out currentLimbWidth (limbStart + currentLimbWidth) (replicate currentLimbWidth True)
  column1CarryLimbs <- addWholeColumn dimensions limbStart currentLimbWidth 0 resultLimb1 [upperX0Y0, lowerX1Y0, lowerX0Y1]
  -- column 2
  let resultLimb2 = Limb out currentLimbWidth (limbStart + currentLimbWidth * 2) (replicate currentLimbWidth True)
  _ <- addWholeColumn dimensions limbStart currentLimbWidth 0 resultLimb2 $ column1CarryLimbs <> [upperX1Y0, upperX0Y1, lowerX2Y0, lowerX1Y1, lowerX0Y2]
  return ()