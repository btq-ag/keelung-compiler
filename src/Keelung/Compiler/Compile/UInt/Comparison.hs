module Keelung.Compiler.Compile.UInt.Comparison (assertLTE, assertLT, assertGTE, assertGT, assertNonZero) where

import Control.Monad.Except
import Control.Monad.RWS
import Data.Bits qualified
import Data.Field.Galois (GaloisField)
import Keelung (HasWidth (widthOf), Width)
import Keelung.Compiler.Compile.Error qualified as Error
import Keelung.Compiler.Compile.Monad
import Keelung.Compiler.ConstraintModule (ConstraintModule (..))
import Keelung.Compiler.Options
import Keelung.Data.FieldInfo
import Keelung.Data.LC ((@))
import Keelung.Data.Reference
import Keelung.Data.Slice (Slice (Slice))
import Keelung.Data.U (U)
import Keelung.Field

--------------------------------------------------------------------------------

-- | Assert that a UInt is less than or equal to some constant
-- reference doc: A.3.2.2 Range Check https://zips.z.cash/protocol/protocol.pdf
assertLTE :: (GaloisField n, Integral n) => Width -> Either RefU U -> Integer -> M n ()
assertLTE _ (Right a) bound = if fromIntegral a <= bound then return () else throwError $ Error.AssertComparisonError (toInteger a) LT (succ bound)
assertLTE width (Left a) bound
  | bound < 0 = throwError $ Error.AssertLTEBoundTooSmallError (toInteger bound)
  | bound >= 2 ^ width - 1 = throwError $ Error.AssertLTEBoundTooLargeError (toInteger bound) width
  | bound == 0 = do
      -- there's only 1 possible value for `a`, which is `0`
      writeRefUVal a 0
  | bound == 1 = do
      -- there are 2 possible values for `a`, which are `0` and `1`
      -- we can use these 2 values as the only roots of the following multiplicative polynomial
      -- (a - 0) * (a - 1) = 0
      -- `(a - 0) * (a - 1) = 0` on the LSB
      let slice = Slice a 0 width
      writeMul (0, [], [(slice, 1)]) (-1, [], [(slice, 1)]) (0, [], [])
      -- assign the rest of the bits to `0`
      writeSliceVal (Slice a 1 width) 0
  | bound == 2 = do
      -- there are 3 possible values for `a`, which are `0`, `1` and `2`
      -- we can use these 3 values as the only roots of the following 2 multiplicative polynomial
      -- (a - 0) * (a - 1) * (a - 2) = 0

      fieldInfo <- gets (optFieldInfo . cmOptions)

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
        then -- because we don't have to execute the `step` function for trailing ones of `c`
        -- we can limit the range of bits of c from `[width-1, width-2 .. 0]` to `[width-1, width-2 .. countTrailingOnes]`
          foldM_ (step a) (Left 0) [width - 1, width - 2 .. (width - 2) `min` countTrailingOnes]
        else do
          -- `(a - 0) * (a - 1) * (a - 2) = 0` on the smallest limb
          let slice = Slice a 0 limbWidth
          temp <- freshRefF
          writeMul (0, [], [(slice, 1)]) (-1, [], [(slice, 1)]) (0, [(F temp, 1)], [])
          writeMul (0, [(F temp, 1)], []) (-2, [], [(slice, 1)]) (0, [], [])
          -- assign the rest of the limbs to `0`
          writeSliceVal (Slice a limbWidth width) 0
  | otherwise = do
      -- because we don't have to execute the `step` function for trailing ones of `c`
      -- we can limit the range of bits of c from `[width-1, width-2 .. 0]` to `[width-1, width-2 .. countTrailingOnes]`
      foldM_ (step a) (Left 0) [width - 1, width - 2 .. (width - 2) `min` countTrailingOnes]
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

    -- starts from the MSB
    step :: (GaloisField n, Integral n) => RefU -> Either Int (Either Slice Ref) -> Int -> M n (Either Int (Either Slice Ref))
    step ref (Left leadingZeros) i =
      -- have not found the first bit in 'c' that is 1 yet
      let bit = Slice ref i (i + 1)
       in if Data.Bits.testBit bound i
            then return $ Right (Left bit) -- when found, return a[i]
            else do
              writeSliceVal bit 0
              return (Left (leadingZeros + 1)) -- otherwise, continue searching
    step ref (Right acc) i =
      let bit = Slice ref i (i + 1)
       in if Data.Bits.testBit bound i
            then do
              -- constraint for the next accumulator
              -- acc * a[i] = acc'
              -- such that if a[i] = 1
              --    then acc' = acc
              --    else acc' = 0
              acc' <- freshRefF
              case acc of
                Left accSlice -> writeMul (0, [], [(accSlice, 1)]) (0, [], [(bit, 1)]) (0, [(F acc', 1)], [])
                Right accRef -> writeMul (0, [(accRef, 1)], []) (0, [], [(bit, 1)]) (0, [(F acc', 1)], [])
              return $ Right (Right (F acc'))
            else do
              -- constraint on a[i]
              -- (1 - acc - a[i]) * a[i] = 0
              -- such that if acc = 0 then a[i] = 0 or 1 (don't care)
              --           if acc = 1 then a[i] = 0
              case acc of
                Left accSlice -> writeMul (1, [], [(accSlice, -1), (bit, -1)]) (0, [], [(bit, 1)]) (0, [], [])
                Right accRef -> writeMul (1, [(accRef, -1)], [(bit, -1)]) (0, [], [(bit, 1)]) (0, [], [])
              -- pass down the accumulator
              return $ Right acc

-- | Assert that a UInt is less than some constant
assertLT :: (GaloisField n, Integral n) => Width -> Either RefU U -> Integer -> M n ()
assertLT width a c = do
  -- check if the bound is within the range of the UInt
  when (c < 1) $
    throwError $
      Error.AssertLTBoundTooSmallError c
  when (c >= 2 ^ width) $
    throwError $
      Error.AssertLTBoundTooLargeError c width
  -- otherwise, assert that a <= c - 1
  assertLTE width a (c - 1)

--------------------------------------------------------------------------------

-- | Assert that a UInt is greater than or equal to some constant
assertGTE :: (GaloisField n, Integral n) => Width -> Either RefU U -> Integer -> M n ()
assertGTE _ (Right a) c = if fromIntegral a >= c then return () else throwError $ Error.AssertComparisonError (succ (toInteger a)) GT c
assertGTE width (Left a) bound
  | bound < 1 = throwError $ Error.AssertGTEBoundTooSmallError (toInteger bound)
  | bound == 1 = do
      -- a ≥ 1 → a > 0 → a is not zero
      -- there exists a number m such that the product of a and m is 1
      assertNonZero width a
  | bound >= 2 ^ width = throwError $ Error.AssertGTEBoundTooLargeError (toInteger bound) width
  | bound == 2 ^ width - 1 = do
      -- there's only 1 possible value for `a`, which is `2^width - 1`
      writeRefUVal a (2 ^ width - 1)
  | bound == 2 ^ width - 2 = do
      -- there's only 2 possible value for `a`, which is `2^width - 1` or `2^width - 2`
      -- we can use these 2 values as the only roots of the following multiplicative polynomial
      -- (a - 2^width + 1) * (a - 2^width + 2) = 0
      -- that is, either all bits are 1 or only the smallest bit is 0
      fieldInfo <- gets (optFieldInfo . cmOptions)

      let maxLimbWidth = fieldWidth fieldInfo
      let minLimbWidth = 1
      let limbWidth = minLimbWidth `max` widthOf a `min` maxLimbWidth

      let isBinaryField = case fieldTypeData fieldInfo of
            Binary _ -> True
            Prime _ -> False

      if isBinaryField
        then do
          -- `(a - 2^limbWidth + 1) * (a - 2^limbWidth + 2) = 0`
          -- the LSB is either 0 or 1
          let lsb = Slice a 0 1
          writeMul (0, [], [(lsb, 1)]) (1, [], [(lsb, 1)]) (0, [], [])
          -- the other bits are all 1
          forM_ [1 .. width - 1] $ \j ->
            writeSliceVal (Slice a j (j + 1)) 1
        else do
          -- `(a - 2^limbWidth + 1) * (a - 2^limbWidth + 2) = 0` on the smallest limb
          let slice = Slice a 0 limbWidth
          writeMul (1 - 2 ^ limbWidth, [], [(slice, 1)]) (2 - 2 ^ limbWidth, [], [(slice, 1)]) (0, [], [])
          -- assign the rest of the limbs to `1`
          forM_ [limbWidth .. width - 1] $ \j ->
            writeSliceVal (Slice a j (j + 1)) 1
  | bound == 2 ^ width - 3 = do
      -- there's only 3 possible value for `a`, which is `2^width - 1`, `2^width - 2` or `2^width - 3`
      -- we can use these 3 values as the only roots of the following 2 multiplicative polynomial

      fieldInfo <- gets (optFieldInfo . cmOptions)

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
          let slice = Slice a 0 limbWidth

          temp <- freshRefF
          writeMul (1 - 2 ^ limbWidth, [], [(slice, 1)]) (2 - 2 ^ limbWidth, [], [(slice, 1)]) (0, [(F temp, 1)], [])
          writeMul (0, [(F temp, 1)], []) (3 - 2 ^ limbWidth, [], [(slice, 1)]) (0, [], [])

          -- assign the rest of the limbs to `1`
          forM_ [limbWidth .. width - 1] $ \j ->
            writeSliceVal (Slice a j (j + 1)) 1
  | otherwise = runDefault
  where
    runDefault = do
      flag <- freshRefF
      writeRefFVal flag 1
      -- because we don't have to execute the `step` function for trailing zeros of `bound`
      -- we can limit the range of bits of c from `[width-1, width-2 .. 0]` to `[width-1, width-2 .. countTrailingZeros]`
      foldM_ (step a) (F flag) [width - 1, width - 2 .. (width - 2) `min` countTrailingZeros]

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

    step :: (GaloisField n, Integral n) => RefU -> Ref -> Int -> M n Ref
    step ref flag i =
      let aBit = RefUBit ref i
          bBit = Data.Bits.testBit bound i
       in if bBit
            then do
              -- constraint on bit
              -- (flag + bit - 1) * bit = flag
              -- such that if flag = 0 then bit = 0 or 1 (don't care)
              --           if flag = 1 then bit = 1
              writeMul (-1, [(B aBit, 1), (flag, 1)], []) (0, [(B aBit, 1)], []) (0, [(flag, 1)], [])
              return flag
            else do
              flag' <- freshRefF
              -- flag' := flag * (1 - bit)
              writeMul (0, [(flag, 1)], []) (1, [(B aBit, -1)], []) (0, [(F flag', 1)], [])
              return (F flag')

-- | Assert that a UInt is greater than some constant
assertGT :: (GaloisField n, Integral n) => Width -> Either RefU U -> Integer -> M n ()
assertGT width a c = do
  -- check if the bound is within the range of the UInt
  when (c < 0) $
    throwError $
      Error.AssertGTBoundTooSmallError c
  when (c >= 2 ^ width - 1) $
    throwError $
      Error.AssertGTBoundTooLargeError c width
  -- otherwise, assert that a >= c + 1
  assertGTE width a (c + 1)

--------------------------------------------------------------------------------

-- | Assert that the given UInt is not zero.
assertNonZero :: (GaloisField n, Integral n) => Width -> RefU -> M n ()
assertNonZero width ref = do
  let bits = [RefUBit ref i | i <- [0 .. width - 1]]
  assertNonZeroOnRefBs bits
  where
    assertNonZeroOnRefBs :: (GaloisField n, Integral n) => [RefB] -> M n ()
    assertNonZeroOnRefBs bits = do
      fieldInfo <- gets (optFieldInfo . cmOptions)
      case fieldTypeData fieldInfo of
        Binary _ -> linearCase bits
        Prime 2 -> linearCase bits
        Prime 3 -> linearCase bits
        Prime n -> fasterCase (fromInteger n) bits

    -- Using N constraints on N-bits UInt to assert that the UInt is not zero.
    linearCase :: (GaloisField n, Integral n) => [RefB] -> M n ()
    linearCase bits = do
      nonZero <- freshRefB
      writeRefBVal nonZero False
      final <- foldM step nonZero bits
      -- assert that the final `nonZero` is 1
      writeRefBVal final True
      where
        -- we enforce this constraint:
        --    nonZero' = nonZero `or` bit
        --             = nonZero + bit - nonZero * bit
        -- such that:
        --    if `nonZero = 0` then `nonZero' = bit`
        --    if `nonZero = 1` then `nonZero' = 1`
        -- and assert the final `nonZero' = 1`
        step :: (GaloisField n, Integral n) => RefB -> RefB -> M n RefB
        step nonZero bit = do
          nonZero' <- freshRefB
          writeMul (0, [(B nonZero, 1)], []) (0, [(B bit, 1)], []) (0, [(B nonZero, 1), (B bit, 1), (B nonZero', -1)], [])
          return nonZero'

    fasterCase :: (GaloisField n, Integral n) => Int -> [RefB] -> M n ()
    fasterCase order bits = do
      -- we can only add at most `order - 1` bits at a time
      let (currentBatch, nextBatch) = splitAt (order - 1) bits
      result <- compress currentBatch
      if null nextBatch
        then do
          -- edge case
          writeRefBVal result True
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
