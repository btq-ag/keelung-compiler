{-# LANGUAGE TupleSections #-}

module Keelung.Compiler.Compile.UInt.Addition (addLimbColumn, compileAdd, compileSub) where

import Control.Monad.Except
import Control.Monad.RWS
import Data.Bits qualified
import Data.Field.Galois (GaloisField)
import Data.Foldable (Foldable (toList))
import Keelung.Compiler.Compile.Error qualified as Error
import Keelung.Compiler.Compile.Monad
import Keelung.Compiler.Compile.UInt.Addition.LimbColumn (LimbColumn)
import Keelung.Compiler.Compile.UInt.Addition.LimbColumn qualified as LimbColumn
import Keelung.Compiler.Compile.Util
import Keelung.Compiler.ConstraintModule (ConstraintModule (..))
import Keelung.Data.FieldInfo
import Keelung.Data.Limb (Limb (..))
import Keelung.Data.Limb qualified as Limb
import Keelung.Data.Reference
import Keelung.Field (FieldType (..))
import Keelung.Syntax (Width)

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

compileAdd :: (GaloisField n, Integral n) => Width -> RefU -> [(RefU, Bool)] -> Integer -> M n ()
compileAdd width out vars constant = do
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

  -- the maximum number of limbs that can be added up at a time
  let maxHeight = if carryWidth > 21 then 1048576 else 2 ^ carryWidth -- HACK
  case fieldTypeData fieldInfo of
    Binary _ -> compileAddOnBinaryField width out vars constant
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
                      column = LimbColumn.new constantSegment [Limb.new var currentLimbWidth start (Left sign) | (var, sign) <- vars]
                      -- negative limbs
                      resultLimb = Limb.new out currentLimbWidth start (Left True)
                   in (column, resultLimb)
              )
              [0, limbWidth .. width - 1] -- index of the first bit of each limb
      foldM_
        ( \prevCarries (column, resultLimb) -> addLimbColumn maxHeight resultLimb (prevCarries <> column)
        )
        mempty
        ranges

-- | Subtraction is implemented as addition with negated operands
compileSub :: (GaloisField n, Integral n) => Width -> RefU -> Either RefU Integer -> Either RefU Integer -> M n ()
compileSub width out (Right a) (Right b) = compileAdd width out [] (a - b)
compileSub width out (Right a) (Left b) = compileAdd width out [(b, False)] a
compileSub width out (Left a) (Right b) = compileAdd width out [(a, True)] (-b)
compileSub width out (Left a) (Left b) = compileAdd width out [(a, True), (b, False)] 0

--------------------------------------------------------------------------------

-- | Binary field addition
compileAddOnBinaryField :: (GaloisField n, Integral n) => Width -> RefU -> [(RefU, Bool)] -> Integer -> M n ()
compileAddOnBinaryField _ out [(as, True)] 0 = writeRefUEq out as
compileAddOnBinaryField width out [(as, True)] c = compileAddBPosConst width out as c
compileAddOnBinaryField width out [(as, False)] c = compileAddBNegConst width out as c
compileAddOnBinaryField width out [(as, True), (bs, True)] 0 = compileAddBPosPos width out as bs
compileAddOnBinaryField width out [(as, True), (bs, False)] 0 = compileAddBPosNeg width out as bs
compileAddOnBinaryField _ _ _ _ = error "[ panic ] compileAddB: not implemented"

-- | Adds two positive variables together on a binary field:
--   Assume `as` and `bs` to the operands
--    constraints of a full adder: 
--      out[i] = as[i] + bs[i] + carry[i]
--      carry[i+1] = as[i] * bs[i] + as[i] * carry[i] + bs[i] * carry[i]
--    edge case: carry[0] = 0
compileAddBPosPos :: (GaloisField n, Integral n) => Width -> RefU -> RefU -> RefU -> M n ()
compileAddBPosPos width out as bs = do
  -- only need `width - 1` carry bits
  carryBits <- freshRefU (width - 1)

  forM_ [0 .. width - 1] $ \index -> do
    let a = B (RefUBit width as index)
    let b = B (RefUBit width bs index)
    let c = B (RefUBit width out index)
    let prevCarry = if index == 0 then Nothing else Just (B (RefUBit (width - 1) carryBits (index - 1)))
    let nextCarry = if index == width - 1 then Nothing else Just (B (RefUBit (width - 1) carryBits index))

    -- out[index] = a + b + prevCarry
    -- nextCarry = a * b + a * prevCarry + b * prevCarry
    case (prevCarry, nextCarry) of
      (Nothing, Nothing) -> do
        -- c = a + b
        writeAdd 0 [(a, 1), (b, 1), (c, -1)]
      (Nothing, Just next) -> do
        -- c = a + b
        writeAdd 0 [(a, 1), (b, 1), (c, -1)]
        -- next = a * b
        writeMul (0, [(a, 1)]) (0, [(b, 1)]) (0, [(next, 1)])
      (Just prev, Nothing) -> do
        -- c = a + b + prev
        writeAdd 0 [(a, 1), (b, 1), (prev, 1), (c, -1)]
      (Just prev, Just next) -> do
        -- c = a + b + prev
        writeAdd 0 [(a, 1), (b, 1), (prev, 1), (c, -1)]
        -- next = a * b + a * prev + b * prev
        ab <- freshRefB
        aPrev <- freshRefB
        bPrev <- freshRefB
        -- ab = a * b
        writeMul (0, [(a, 1)]) (0, [(b, 1)]) (0, [(B ab, 1)])
        -- aPrev = a * prev
        writeMul (0, [(a, 1)]) (0, [(prev, 1)]) (0, [(B aPrev, 1)])
        -- bPrev = b * prev
        writeMul (0, [(b, 1)]) (0, [(prev, 1)]) (0, [(B bPrev, 1)])
        -- next = ab + aPrev + bPrev
        writeAdd 0 [(B ab, 1), (B aPrev, 1), (B bPrev, 1), (next, -1)]

-- | Adds a positive variable and a constant together on a binary field:
--   Assume `as` to the variable and `bs` to be the constant
--    constraints of a full adder: 
--      out[i] = as[i] + bs[i] + carry[i]
--      carry[i+1] = as[i] * bs[i] + as[i] * carry[i] + bs[i] * carry[i]
--    edge case: carry[0] = 0
compileAddBPosConst :: (GaloisField n, Integral n) => Width -> RefU -> RefU -> Integer -> M n ()
compileAddBPosConst width out as bs = do
  -- only need `width - 1` carry bits
  carryBits <- freshRefU (width - 1)

  forM_ [0 .. width - 1] $ \index -> do
    let a = B (RefUBit width as index)
    let b = if Data.Bits.testBit bs index then 1 else 0
    let c = B (RefUBit width out index)
    let prevCarry = if index == 0 then Nothing else Just (B (RefUBit (width - 1) carryBits (index - 1)))
    let nextCarry = if index == width - 1 then Nothing else Just (B (RefUBit (width - 1) carryBits index))

    -- out[index] = a + b + prevCarry
    -- nextCarry = a * b + a * prevCarry + b * prevCarry
    case (prevCarry, nextCarry) of
      (Nothing, Nothing) -> do
        -- c = a + b
        writeAdd b [(a, 1), (c, -1)]
      (Nothing, Just next) -> do
        -- c = a + b
        writeAdd b [(a, 1), (c, -1)]
        -- next = a * b
        writeAdd 0 [(a, b), (next, -1)]
      (Just prev, Nothing) -> do
        -- c = a + b + prev
        writeAdd b [(a, 1), (prev, 1), (c, -1)]
      (Just prev, Just next) -> do
        -- c = a + b + prev
        writeAdd b [(a, 1), (prev, 1), (c, -1)]
        aPrev <- freshRefB
        -- aPrev = a * prev
        writeMul (0, [(a, 1)]) (0, [(prev, 1)]) (0, [(B aPrev, 1)])
        -- next = ab + aPrev + bPrev
        writeAdd 0 [(a, b), (B aPrev, 1), (prev, b), (next, -1)]

-- | Adds a negative variable and a constant together on a binary field:
--   Assume `as` to the variable and `bs` to be the constant
--    constraints of a full adder: 
--      out[i] = as[i] + bs[i] + carry[i] + 1
--      carry[i+1] = (1 + as[i]) * bs[i] + (1 + as[i]) * carry[i] + bs[i] * carry[i]
--      carry[i+1] = as[i] * bs[i] + as[i] * carry[i] + bs[i] * carry[i] + bs[i] + carry[i]
--    edge case: carry[0] = 1
compileAddBNegConst :: (GaloisField n, Integral n) => Width -> RefU -> RefU -> Integer -> M n ()
compileAddBNegConst width out as bs = do
  -- only need `width - 1` carry bits
  carryBits <- freshRefU (width - 1)

  forM_ [0 .. width - 1] $ \index -> do
    let a = B (RefUBit width as index)
    let b = if Data.Bits.testBit bs index then 1 else 0
    let c = B (RefUBit width out index)
    let prevCarry = if index == 0 then Nothing else Just (B (RefUBit (width - 1) carryBits (index - 1)))
    let nextCarry = if index == width - 1 then Nothing else Just (B (RefUBit (width - 1) carryBits index))

    -- out[index] = a + b + prevCarry + 1
    -- nextCarry = a * b + a * prevCarry + b * prevCarry + b + prevCarry
    case (prevCarry, nextCarry) of
      (Nothing, Nothing) -> do
        -- c = a + b + prev + 1
        --   = a + b
        writeAdd b [(a, 1), (c, -1)]
      (Nothing, Just next) -> do
        -- c = a + b + prev + 1
        --   = a + b
        writeAdd b [(a, 1), (c, -1)]
        -- next = a * b + a * prev + b * prev + b + prev
        --      = a * (b + 1) + 1
        writeAdd 1 [(a, b + 1), (next, -1)]
      (Just prev, Nothing) -> do
        -- c = a + b + prev + 1
        writeAdd (b + 1) [(a, 1), (prev, 1), (c, -1)]
      (Just prev, Just next) -> do
        -- c = a + b + prev + 1
        writeAdd (b + 1) [(a, 1), (prev, 1), (c, -1)]
        -- next = a * b + a * prev + (b + 1) * prev + b + prev
        aPrev <- freshRefB
        -- aPrev = a * prev
        writeMul (0, [(a, 1)]) (0, [(prev, 1)]) (0, [(B aPrev, 1)])
        -- next = ab + aPrev + bPrev + b + prev
        writeAdd b [(a, b), (B aPrev, 1), (prev, b + 1), (next, -1)]

-- | Adds a positive variable with a negative variable on a binary field:
--   Assume `as` to be the positive operand and `bs` to be the negative operand
--    constraints of a full adder: 
--      out[i] = as[i] + bs[i] + carry[i] + 1
--      carry[i+1] = as[i] * bs[i] + as[i] * carry[i] + bs[i] * carry[i] + as[i] + carry[i]
--    edge case: carry[0] = 1
compileAddBPosNeg :: (GaloisField n, Integral n) => Width -> RefU -> RefU -> RefU -> M n ()
compileAddBPosNeg width out as bs = do
  -- only need `width - 1` carry bits
  carryBits <- freshRefU (width - 1)

  forM_ [0 .. width - 1] $ \index -> do
    let a = B (RefUBit width as index)
    let b = B (RefUBit width bs index)
    let c = B (RefUBit width out index)
    let prevCarry = if index == 0 then Nothing else Just (B (RefUBit (width - 1) carryBits (index - 1)))
    let nextCarry = if index == width - 1 then Nothing else Just (B (RefUBit (width - 1) carryBits index))

    -- out[index] = a + b + prevCarry + 1
    -- nextCarry = a * b + a * prevCarry + b * prevCarry + a + prevCarry
    case (prevCarry, nextCarry) of
      (Nothing, Nothing) -> do
        -- c = a + b + prev + 1
        --   = a + b
        writeAdd 0 [(a, 1), (b, 1), (c, -1)]
      (Nothing, Just next) -> do
        -- c = a + b + prev + 1
        --   = a + b
        writeAdd 0 [(a, 1), (b, 1), (c, -1)]
        -- next = a * b + a * prev + b * prev + a + prev
        --      = a * b + b + 1
        writeMul (0, [(a, 1)]) (0, [(b, 1)]) (-1, [(next, 1), (b, -1)])
      (Just prev, Nothing) -> do
        -- c = a + b + prev + 1
        writeAdd 1 [(a, 1), (b, 1), (prev, 1), (c, -1)]
      (Just prev, Just next) -> do
        -- c = a + b + prev + 1
        writeAdd 1 [(a, 1), (b, 1), (prev, 1), (c, -1)]
        -- next = a * b + a * prev + b * prev + a + prev
        ab <- freshRefB
        aPrev <- freshRefB
        bPrev <- freshRefB
        -- ab = a * b
        writeMul (0, [(a, 1)]) (0, [(b, 1)]) (0, [(B ab, 1)])
        -- aPrev = a * prev
        writeMul (0, [(a, 1)]) (0, [(prev, 1)]) (0, [(B aPrev, 1)])
        -- bPrev = b * prev
        writeMul (0, [(b, 1)]) (0, [(prev, 1)]) (0, [(B bPrev, 1)])
        -- next = ab + aPrev + bPrev + a + prev
        writeAdd 0 [(B ab, 1), (B aPrev, 1), (B bPrev, 1), (a, 1), (prev, 1), (next, -1)]

--------------------------------------------------------------------------------

-- | Add a column of limbs, and return a column of carry limbs
addLimbColumn :: (GaloisField n, Integral n) => Int -> Limb -> LimbColumn -> M n LimbColumn
addLimbColumn maxHeight finalResultLimb limbs = do
  -- trim the limbs so that their width does not exceed that of the result limb
  let trimmedLimbs = LimbColumn.trim (lmbWidth finalResultLimb) limbs
  -- split the limbs into a stack of limbs and the rest of the column
  let (stack, rest) = LimbColumn.view maxHeight trimmedLimbs
  case rest of
    Nothing -> do
      -- base case, there are no more limbs to be processed
      result <- addLimbColumnView finalResultLimb stack
      case result of
        Nothing -> return mempty
        Just carryLimb -> return (LimbColumn.singleton carryLimb)
    Just rest' -> do
      -- inductive case, there are more limbs to be processed
      resultLimb <- allocLimb (lmbWidth finalResultLimb) (lmbOffset finalResultLimb) True
      result <- addLimbColumnView resultLimb stack
      -- insert the result limb of the current batch to the next batch
      moreCarryLimbs <- addLimbColumn maxHeight finalResultLimb (LimbColumn.insert resultLimb rest')
      case result of
        Nothing -> return moreCarryLimbs
        Just carryLimb -> return $ LimbColumn.insert carryLimb moreCarryLimbs

-- | Compress a column of limbs into a single limb and some carry
--
--              [ operand ]
--              [ operand ]   operands
--  +           [ operand ]
-- -----------------------------
--    [ carry  ][  result  ]
addLimbColumnView :: (GaloisField n, Integral n) => Limb -> LimbColumn.View -> M n (Maybe Limb)
addLimbColumnView resultLimb (LimbColumn.OneConstantOnly constant) = do
  -- no limb => result = constant, no carry
  writeLimbVal resultLimb constant
  return Nothing
addLimbColumnView resultLimb (LimbColumn.OneLimbOnly limb) = do
  writeLimbEq resultLimb limb
  return Nothing
addLimbColumnView resultLimb (LimbColumn.Ordinary constant limbs) = do
  let carrySigns = calculateCarrySigns (lmbWidth resultLimb) constant limbs
  carryLimb <- allocCarryLimb (length carrySigns) (lmbOffset resultLimb) carrySigns
  writeAddWithLimbs (fromInteger constant) $
    -- negative side
    (resultLimb, -1)
      : (carryLimb, -(2 ^ lmbWidth resultLimb))
      -- positive side
      : fmap (,1) (toList limbs)
  return $ Just carryLimb