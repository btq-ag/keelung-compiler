module Keelung.Compiler.Compile.UInt
  ( compileAddU,
    compileSubU,
    compileMulU,
    -- compileModInv,
    assertLTE,
    assertGTE,
  )
where

import Control.Monad.Except
import Control.Monad.State
import Data.Bits qualified
import Data.Field.Galois (GaloisField)
import Data.Foldable (toList)
import Data.IntMap.Strict qualified as IntMap
import Data.Sequence qualified as Seq
import Keelung (FieldType (..), HasWidth (widthOf))
import Keelung.Compiler.Compile.Error qualified as Error
import Keelung.Compiler.Compile.LC
import Keelung.Compiler.Compile.Limb
import Keelung.Compiler.Compile.LimbColumn (LimbColumn)
import Keelung.Compiler.Compile.LimbColumn qualified as LimbColumn
import Keelung.Compiler.Compile.Util
import Keelung.Compiler.Constraint
import Keelung.Compiler.ConstraintModule (ConstraintModule (..))
import Keelung.Data.FieldInfo (FieldInfo (..))
import Keelung.Syntax (Width)

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
            dimMaxHeight = if carryWidth > 21 then 1048576 else 2 ^ (carryWidth - 1), -- HACK
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
  if allNegative
    then do
      let carrySigns = replicate (dimCarryWidth dimensions + 1) False
      carryLimb <- allocCarryLimb (dimCarryWidth dimensions + 1) limbStart carrySigns
      writeAddWithSeq constant $
        -- positive side
        mconcat (map (toBits 0 True) limbs)
          -- negative side
          <> toBits 0 False resultLimb
          <> toBits currentLimbWidth False carryLimb
      return $ LimbColumn.singleton carryLimb
    else
      if length limbs == 1 && constant == 0
        then do
          forM_ [0 .. currentLimbWidth - 1] $ \i -> do
            let limb = head limbs
            writeEqB (RefUBit (dimUIntWidth dimensions) (lmbRef resultLimb) (lmbOffset resultLimb + i)) (RefUBit (dimUIntWidth dimensions) (lmbRef limb) (lmbOffset limb + i))
          return mempty
        else do
          -- more than limbs
          let carrySigns = map (not . Data.Bits.testBit negLimbSize) [0 .. dimCarryWidth dimensions - 1]
          carryLimb <- allocCarryLimb (dimCarryWidth dimensions) limbStart carrySigns
          writeAddWithSeq constant $
            -- positive side
            mconcat (map (toBits 0 True) limbs)
              -- negative side
              <> toBits 0 False resultLimb
              <> toBits currentLimbWidth False carryLimb
          return $ LimbColumn.singleton carryLimb

addWholeColumn :: (GaloisField n, Integral n) => Dimensions -> Int -> Int -> Limb -> LimbColumn -> M n LimbColumn
addWholeColumn dimensions limbStart currentLimbWidth finalResultLimb column = do
  let constant = LimbColumn.constant column
  let (currentBatch, nextBatch) = Seq.splitAt (dimMaxHeight dimensions) (LimbColumn.limbs column)
  if not (null nextBatch) || (length currentBatch == dimMaxHeight dimensions && constant /= 0)
    then do
      -- inductive case, there are more limbs to be processed
      resultLimb <- allocLimb currentLimbWidth limbStart True
      carryLimb <- addPartialColumn dimensions limbStart currentLimbWidth resultLimb 0 (toList currentBatch)
      -- insert the result limb of the current batch to the next batch
      moreCarryLimbs <- addWholeColumn dimensions limbStart currentLimbWidth finalResultLimb (LimbColumn.new (toInteger constant) (resultLimb : toList nextBatch))
      return (carryLimb <> moreCarryLimbs)
    else do
      -- edge case, all limbs are in the current batch
      addPartialColumn dimensions limbStart currentLimbWidth finalResultLimb (fromInteger constant) (toList currentBatch)

compileSubU :: (GaloisField n, Integral n) => Width -> RefU -> Either RefU Integer -> Either RefU Integer -> M n ()
compileSubU width out (Right a) (Right b) = compileAddU width out [] (a - b)
compileSubU width out (Right a) (Left b) = compileAddU width out [(b, False)] a
compileSubU width out (Left a) (Right b) = compileAddU width out [(a, True)] (-b)
compileSubU width out (Left a) (Left b) = compileAddU width out [(a, True), (b, False)] 0

allocLimb :: (GaloisField n, Integral n) => Width -> Int -> Bool -> M n Limb
allocLimb w offset sign = do
  refU <- freshRefU w
  mapM_ addBooleanConstraint [RefUBit w refU i | i <- [0 .. w - 1]]
  return $
    Limb
      { lmbRef = refU,
        lmbWidth = w,
        lmbOffset = offset,
        lmbSigns = Left sign
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
        lmbSigns = Right signs
      }

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
compileMulU width out (Right a) (Left b) = compileMul width out b (Right a)
compileMulU width out (Left a) (Right b) = compileMul width out a (Right b)
compileMulU width out (Left a) (Left b) = compileMul width out a (Left b)

compileMul :: (GaloisField n, Integral n) => Width -> RefU -> RefU -> Either RefU Integer -> M n ()
compileMul width out x y = do
  fieldInfo <- gets cmField

  -- invariants about widths of carry and limbs:
  --  1. limb width * 2 ≤ field width

  let maxLimbWidth = fieldWidth fieldInfo `div` 2
  let minLimbWidth = 2 -- TEMPORARY HACK FOR ADDITION
  let limbWidth = minLimbWidth `max` widthOf x `min` maxLimbWidth

  let dimensions =
        Dimensions
          { dimUIntWidth = width,
            dimMaxHeight = if limbWidth > 20 then 1048576 else 2 ^ limbWidth, -- HACK
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
      mulnxn dimensions limbWidth limbNumber out x y

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
      writeAddWithSeq (a * constant) $
        -- operand side
        toBitsC 0 True x constant
          -- negative side
          <> toBits 0 False lowerLimb
          <> toBits currentLimbWidth False upperLimb
      return (LimbColumn.singleton lowerLimb, LimbColumn.singleton upperLimb)
    Right (b, y) -> do
      upperLimb <- allocLimb currentLimbWidth (limbStart + currentLimbWidth) True
      lowerLimb <- allocLimb currentLimbWidth limbStart True
      writeMulWithSeq
        (a, toBits 0 True x)
        (b, toBits 0 True y)
        ( 0,
          toBits 0 True lowerLimb
            <> toBits currentLimbWidth True upperLimb
        )
      return (LimbColumn.singleton lowerLimb, LimbColumn.singleton upperLimb)

_mul2LimbPreallocated :: (GaloisField n, Integral n) => Width -> Int -> (n, Limb) -> Either n (n, Limb) -> Limb -> M n Limb
_mul2LimbPreallocated currentLimbWidth limbStart (a, x) operand lowerLimb = do
  upperLimb <- allocLimb currentLimbWidth (limbStart + currentLimbWidth) True
  case operand of
    Left constant ->
      writeAddWithSeq (a * constant) $
        -- operand side
        toBitsC 0 True x constant
          -- negative side
          <> toBits 0 False lowerLimb
          <> toBits currentLimbWidth False upperLimb
    Right (b, y) ->
      writeMulWithSeq
        (a, toBits 0 True x)
        (b, toBits 0 True y)
        ( 0,
          toBits 0 True lowerLimb
            <> toBits currentLimbWidth True upperLimb
        )

  return upperLimb

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
mulnxn :: (GaloisField n, Integral n) => Dimensions -> Width -> Int -> RefU -> RefU -> Either RefU Integer -> M n ()
mulnxn dimensions limbWidth arity out var operand = do
  -- generate pairs of indices for choosing limbs
  let indices = [(xi, columnIndex - xi) | columnIndex <- [0 .. arity - 1], xi <- [0 .. columnIndex]]
  -- generate pairs of limbs to be added together
  limbColumns <-
    foldM
      ( \columns (xi, yi) -> do
          -- current limb width may be smaller than the default limb width in the highest limbs
          let currentLimbWidthX = limbWidth `min` (dimUIntWidth dimensions - (limbWidth * xi))
          let currentLimbWidthY = limbWidth `min` (dimUIntWidth dimensions - (limbWidth * yi))

          let x = Limb var currentLimbWidthX (limbWidth * xi) (Left True)
          let y = case operand of
                Right constant -> Left $ sum [(if Data.Bits.testBit constant (limbWidth * yi + i) then 1 else 0) * (2 ^ i) | i <- [0 .. currentLimbWidthY - 1]]
                Left variable -> Right (0, Limb variable currentLimbWidthY (limbWidth * yi) (Left True))
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
        let currentLimbWidth = limbWidth `min` (dimUIntWidth dimensions - limbStart)
        let resultLimb = Limb out currentLimbWidth (limbWidth * index) (Left True)
        addWholeColumn dimensions limbStart currentLimbWidth resultLimb (previousCarryLimbs <> limbs)
    )
    mempty
    (IntMap.toList limbColumns)

-- --------------------------------------------------------------------------------

-- -- | Division with remainder on UInts
-- --    1. dividend = divisor * quotient + remainder
-- --    2. 0 ≤ remainder < divisor
-- --    3. 0 < divisor
-- assertDivModU ::
--   (GaloisField n, Integral n) =>
--   Width ->
--   Either RefU Integer -> -- dividend
--   Either RefU Integer -> -- divisor
--   Either RefU Integer -> -- quotient
--   Either RefU Integer -> -- remainder
--   M n ()
-- assertDivModU = undefined

--------------------------------------------------------------------------------

-- | Assert that a UInt is less than or equal to some constant
-- reference doc: A.3.2.2 Range Check https://zips.z.cash/protocol/protocol.pdf
assertLTE :: (GaloisField n, Integral n) => Width -> Either RefU Integer -> Integer -> M n ()
assertLTE _ (Right a) bound = if fromIntegral a <= bound then return () else throwError $ Error.AssertComparisonError (toInteger a) LT (succ bound)
assertLTE width (Left a) bound
  | bound < 0 = throwError $ Error.AssertLTEBoundTooSmallError bound
  | bound >= 2 ^ width - 1 = throwError $ Error.AssertLTEBoundTooLargeError bound width
  | bound == 0 = do
      -- there's only 1 possible value for `a`, which is `0`
      writeValU width a 0
  | bound == 1 = do
      -- there are 2 possible values for `a`, which are `0` and `1`
      -- we can use these 2 values as the only roots of the following multiplicative polynomial
      -- (a - 0) * (a - 1) = 0

      fieldInfo <- gets cmField

      let maxLimbWidth = fieldWidth fieldInfo
      let minLimbWidth = 1
      let limbWidth = minLimbWidth `max` widthOf a `min` maxLimbWidth

      -- `(a - 0) * (a - 1) = 0` on the smallest limb
      let bits = [(B (RefUBit width a i), 2 ^ i) | i <- [0 .. limbWidth - 1]]
      writeMul (0, bits) (-1, bits) (0, [])
      -- assign the rest of the limbs to `0`
      forM_ [limbWidth .. width - 1] $ \j ->
        writeValB (RefUBit width a j) False
  | bound == 2 = do
      -- there are 3 possible values for `a`, which are `0`, `1` and `2`
      -- we can use these 3 values as the only roots of the following 2 multiplicative polynomial
      -- (a - 0) * (a - 1) * (a - 2) = 0

      fieldInfo <- gets cmField

      let maxLimbWidth = fieldWidth fieldInfo
      let minLimbWidth = 1
      let limbWidth = minLimbWidth `max` widthOf a `min` maxLimbWidth

      -- cannot encode the `(a - 0) * (a - 1) * (a - 2) = 0` polynomial
      -- if the field is only 1-bit wide
      let isSmallField = case fieldTypeData fieldInfo of
            Binary _ -> True
            Prime 2 -> True
            Prime 3 -> True
            Prime _ -> False

      if isSmallField
        then -- because we don't have to execute the `go` function for trailing ones of `c`
        -- we can limit the range of bits of c from `[width-1, width-2 .. 0]` to `[width-1, width-2 .. countTrailingOnes]`
          foldM_ (go a) Nothing [width - 1, width - 2 .. (width - 2) `min` countTrailingOnes]
        else do
          -- `(a - 0) * (a - 1) * (a - 2) = 0` on the smallest limb
          let bits = [(B (RefUBit width a i), 2 ^ i) | i <- [0 .. limbWidth - 1]]
          temp <- freshRefF
          writeMul (0, bits) (-1, bits) (0, [(F temp, 1)])
          writeMul (0, [(F temp, 1)]) (-2, bits) (0, [])
          -- assign the rest of the limbs to `0`
          forM_ [limbWidth .. width - 1] $ \j ->
            writeValB (RefUBit width a j) False
  | otherwise = do
      -- because we don't have to execute the `go` function for trailing ones of `c`
      -- we can limit the range of bits of c from `[width-1, width-2 .. 0]` to `[width-1, width-2 .. countTrailingOnes]`
      foldM_ (go a) Nothing [width - 1, width - 2 .. (width - 2) `min` countTrailingOnes]
  where
    -- for counting the number of trailing ones of `c`
    countTrailingOnes :: Int
    countTrailingOnes =
      fst $
        foldl
          ( \(count, keepCounting) i ->
              if keepCounting && Data.Bits.testBit bound i then (count + 1, True) else (count, False)
          )
          (0, True)
          [0 .. width - 1]

    go :: (GaloisField n, Integral n) => RefU -> Maybe Ref -> Int -> M n (Maybe Ref)
    go ref Nothing i =
      let aBit = RefUBit width ref i
       in -- have not found the first bit in 'c' that is 1 yet
          if Data.Bits.testBit bound i
            then do
              return $ Just (B aBit) -- when found, return a[i]
            else do
              -- a[i] = 0
              writeValB aBit False
              return Nothing -- otherwise, continue searching
    go ref (Just acc) i =
      let aBit = B (RefUBit width ref i)
       in if Data.Bits.testBit bound i
            then do
              -- constraint for the next accumulator
              -- acc * a[i] = acc'
              -- such that if a[i] = 1
              --    then acc' = acc
              --    else acc' = 0
              acc' <- freshRefF
              writeMul (0, [(acc, 1)]) (0, [(aBit, 1)]) (0, [(F acc', 1)])
              return $ Just (F acc')
            else do
              -- constraint on a[i]
              -- (1 - acc - a[i]) * a[i] = 0
              -- such that if acc = 0 then a[i] = 0 or 1 (don't care)
              --           if acc = 1 then a[i] = 0
              writeMul (1, [(acc, -1), (aBit, -1)]) (0, [(aBit, 1)]) (0, [])
              -- pass down the accumulator
              return $ Just acc

--------------------------------------------------------------------------------

-- | Assert that a UInt is greater than or equal to some constant
assertGTE :: (GaloisField n, Integral n) => Width -> Either RefU Integer -> Integer -> M n ()
assertGTE _ (Right a) c = if fromIntegral a >= c then return () else throwError $ Error.AssertComparisonError (succ (toInteger a)) GT c
assertGTE width (Left a) bound
  | bound < 1 = throwError $ Error.AssertGTEBoundTooSmallError bound
  | bound >= 2 ^ width = throwError $ Error.AssertGTEBoundTooLargeError bound width
  | bound == 2 ^ width - 1 = do
      -- there's only 1 possible value for `a`, which is `2^width - 1`
      writeValU width a (2 ^ width - 1)
  | bound == 2 ^ width - 2 = do
      -- there's only 2 possible value for `a`, which is `2^width - 1` or `2^width - 2`
      -- we can use these 2 values as the only roots of the following multiplicative polynomial
      -- (a - 2^width + 1) * (a - 2^width + 2) = 0
      -- that is, either all bits are 1 or only the smallest bit is 0

      fieldInfo <- gets cmField

      let maxLimbWidth = fieldWidth fieldInfo
      let minLimbWidth = 1
      let limbWidth = minLimbWidth `max` widthOf a `min` maxLimbWidth

      -- `(a - 2^limbWidth + 1) * (a - 2^limbWidth + 2) = 0` on the smallest limb
      let bits = [(B (RefUBit width a i), 2 ^ i) | i <- [0 .. limbWidth - 1]]
      writeMul (1 - 2 ^ limbWidth, bits) (2 - 2 ^ limbWidth, bits) (0, [])
      -- assign the rest of the limbs to `1`
      forM_ [limbWidth .. width - 1] $ \j ->
        writeValB (RefUBit width a j) True
  | bound == 2 ^ width - 3 = do
      -- there's only 3 possible value for `a`, which is `2^width - 1`, `2^width - 2` or `2^width - 3`
      -- we can use these 3 values as the only roots of the following 2 multiplicative polynomial

      fieldInfo <- gets cmField

      let maxLimbWidth = fieldWidth fieldInfo
      let minLimbWidth = 1
      let limbWidth = minLimbWidth `max` widthOf a `min` maxLimbWidth

      -- cannot encode the `(a - 0) * (a - 1) * (a - 2) = 0` polynomial
      -- if the field is only 1-bit wide
      let isSmallField = case fieldTypeData fieldInfo of
            Binary _ -> True
            Prime 2 -> True
            Prime 3 -> True
            Prime _ -> False

      if isSmallField
        then runDefault
        else do
          -- `(a - 2^limbWidth + 1) * (a - 2^limbWidth + 2) * (a - 2^limbWidth + 3) = 0` on the smallest limb
          let bits = [(B (RefUBit width a i), 2 ^ i) | i <- [0 .. limbWidth - 1]]
          -- writeMul (1 - 2 ^ limbWidth, bits) (2 - 2 ^ limbWidth, bits) (0, [])

          temp <- freshRefF
          writeMul (1 - 2 ^ limbWidth, bits) (2 - 2 ^ limbWidth, bits) (0, [(F temp, 1)])
          writeMul (0, [(F temp, 1)]) (3 - 2 ^ limbWidth, bits) (0, [])

          -- assign the rest of the limbs to `1`
          forM_ [limbWidth .. width - 1] $ \j ->
            writeValB (RefUBit width a j) True
  | bound == 1 = do
      -- a ≥ 1 → a > 0 → a is not zero
      -- there exists a number m such that the product of a and m is 1
      assertNonZero width a
  | otherwise = runDefault
  where
    runDefault = do
      flag <- freshRefF
      writeValF flag 1
      -- because we don't have to execute the `go` function for trailing zeros of `bound`
      -- we can limit the range of bits of c from `[width-1, width-2 .. 0]` to `[width-1, width-2 .. countTrailingZeros]`
      foldM_ (go a) (F flag) [width - 1, width - 2 .. (width - 2) `min` countTrailingZeros]

    -- for counting the number of trailing zeros of `bound`
    countTrailingZeros :: Int
    countTrailingZeros =
      fst $
        foldl
          ( \(count, keepCounting) i ->
              if keepCounting && not (Data.Bits.testBit bound i) then (count + 1, True) else (count, False)
          )
          (0, True)
          [0 .. width - 1]

    go :: (GaloisField n, Integral n) => RefU -> Ref -> Int -> M n Ref
    go ref flag i =
      let aBit = RefUBit width ref i
          bBit = Data.Bits.testBit bound i
       in if bBit
            then do
              -- constraint on bit
              -- (flag + bit - 1) * bit = flag
              -- such that if flag = 0 then bit = 0 or 1 (don't care)
              --           if flag = 1 then bit = 1
              writeMul (-1, [(B aBit, 1), (flag, 1)]) (0, [(B aBit, 1)]) (0, [(flag, 1)])
              return flag
            else do
              flag' <- freshRefF
              -- flag' := flag * (1 - bit)
              writeMul (0, [(flag, 1)]) (1, [(B aBit, -1)]) (0, [(F flag', 1)])
              return (F flag')

--------------------------------------------------------------------------------

-- | Assert that the given UInt is not zero.
assertNonZero :: (GaloisField n, Integral n) => Width -> RefU -> M n ()
assertNonZero width ref = do
  let bits = [RefUBit width ref i | i <- [0 .. width - 1]]
  assertNonZeroOnRefBs bits
  where
    assertNonZeroOnRefBs :: (GaloisField n, Integral n) => [RefB] -> M n ()
    assertNonZeroOnRefBs bits = do
      fieldInfo <- gets cmField
      case fieldTypeData fieldInfo of
        Binary _ -> throwError $ Error.FieldNotSupported (fieldTypeData fieldInfo)
        Prime 2 -> linearCase bits
        Prime 3 -> linearCase bits
        Prime n -> fasterCase (fromInteger n) bits

    -- Using N constraints on N-bits UInt to assert that the UInt is not zero.
    linearCase :: (GaloisField n, Integral n) => [RefB] -> M n ()
    linearCase bits = do
      nonZero <- freshRefB
      writeValB nonZero False
      final <- foldM go nonZero bits
      -- assert that the final `nonZero` is 1
      writeValB final True
      where
        -- we enforce this constraint:
        --    nonZero' = nonZero `or` bit
        --             = nonZero + bit - nonZero * bit
        -- such that:
        --    if `nonZero = 0` then `nonZero' = bit`
        --    if `nonZero = 1` then `nonZero' = 1`
        -- and assert the final `nonZero' = 1`
        go :: (GaloisField n, Integral n) => RefB -> RefB -> M n RefB
        go nonZero bit = do
          nonZero' <- freshRefB
          writeMul (0, [(B nonZero, 1)]) (0, [(B bit, 1)]) (0, [(B nonZero, 1), (B bit, 1), (B nonZero', -1)])
          return nonZero'

    fasterCase :: (GaloisField n, Integral n) => Int -> [RefB] -> M n ()
    fasterCase order bits = do
      -- we can only add at most `order - 1` bits at a time
      let (currentBatch, nextBatch) = splitAt (order - 1) bits
      result <- compress currentBatch
      if null nextBatch
        then do
          -- edge case
          writeValB result True
        else do
          -- inductive case
          fasterCase order (result : nextBatch)
      where
        -- add all bits up and see if it's non-zero
        -- reduce N bits to 2 constraints
        compress :: (GaloisField n, Integral n) => [RefB] -> M n RefB
        compress chunk = do
          result <- eqZero False (mconcat (map (\x -> 1 @ B x) chunk))
          case result of
            Left var -> return var
            Right _ -> error "[ panic ] assertNonZero: impossible case"

-- --------------------------------------------------------------------------------

-- -- | Modular multiplicative inverse.
-- --  Let a⁻¹ = a `modInv` p:
-- --  The following constraints should be generated:
-- --    * a * a⁻¹ = np + 1
-- --    * n ≤ p
-- -- See: https://github.com/btq-ag/keelung-compiler/issues/14
-- compileModInv :: (GaloisField n, Integral n) => Width -> RefU -> Either RefU Integer -> Integer -> M n ()
-- compileModInv width out a p = do
--   -- prod = a * out
--   prod <- freshRefU (width * 2)
--   compileMulU (width * 2) prod a (Left out)
--   -- prod = np + 1
--   np <- freshRefU (width * 2)
--   compileMulU (width * 2) np (Right p) (Left prod)
--   compileAddU (width * 2) np [(prod, True)] 1
--   -- n ≤ p
--   -- assertLTE (width * 2) (Left np) p
--   -- hints for witness generation
--   addModInvHint width a (Left out) (Left prod) p