module Keelung.Compiler.Compile.UInt.Addition.Binary (compileAddB) where

import Control.Monad.Except
import Data.Bits qualified
import Data.Field.Galois (GaloisField)
import Keelung.Compiler.Compile.Monad
import Keelung.Data.Reference
import Keelung.Data.U (U)
import Keelung.Syntax (Width)

--------------------------------------------------------------------------------

-- | Binary field addition
compileAddB :: (GaloisField n, Integral n) => Width -> RefU -> [(RefU, Bool)] -> U -> M n ()
compileAddB _ out [] constant = writeRefUVal out constant
compileAddB _ out [(var, True)] 0 = writeRefUEq out var
compileAddB width out [(var, True)] constant = compileAddBPosConst width out var constant
compileAddB width out [(var, False)] constant = compileAddBNegConst width out var constant
compileAddB width out ((var1, sign1) : (var2, sign2) : vars) constant = do
  temp <- freshRefU width
  case (sign1, sign2) of
    (True, True) -> do
      compileAddBPosPos width temp var1 var2
      compileAddB width out ((temp, True) : vars) constant
    (True, False) -> do
      compileAddBPosNeg width temp var1 var2
      compileAddB width out ((temp, True) : vars) constant
    (False, True) -> do
      compileAddBPosNeg width temp var2 var1
      compileAddB width out ((temp, True) : vars) constant
    (False, False) -> do
      compileAddBPosPos width temp var1 var2
      compileAddB width out ((temp, False) : vars) constant -- NOTE: temp is negative here

-- temp <- freshRefU width
-- compileAddB width temp vars constant
-- if sign
--   then compileAddBPosPos width out temp var
--   else compileAddBPosNeg width out temp var

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
--   Assume `as` to be the variable and `bs` to be the constant
--    constraints of a full adder:
--      out[i] = as[i] + bs[i] + carry[i]
--      carry[i+1] = as[i] * bs[i] + as[i] * carry[i] + bs[i] * carry[i]
--    edge case: carry[0] = 0
compileAddBPosConst :: (GaloisField n, Integral n) => Width -> RefU -> RefU -> U -> M n ()
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
compileAddBNegConst :: (GaloisField n, Integral n) => Width -> RefU -> RefU -> U -> M n ()
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