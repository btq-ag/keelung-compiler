module Keelung.Compiler.Compile.UInt.Addition.Binary (compile) where

import Control.Monad.Except
import Data.Bits qualified
import Data.Field.Galois (GaloisField)
import Keelung (widthOf)
import Keelung.Compiler.Compile.Monad
import Keelung.Data.Reference
import Keelung.Data.Slice (Slice (Slice))
import Keelung.Data.U (U)
import Keelung.Syntax (Width)
import qualified Keelung.Data.Slice as Slice

--------------------------------------------------------------------------------

-- | Binary field addition
compile :: (GaloisField n, Integral n) => RefU -> [(RefU, Bool)] -> U -> M n ()
compile out [] constant = writeRefUVal out constant
compile out (x : xs) constant =
  let outputWidth = widthOf out
      operandsWidth = widthOf (fst x)
   in if outputWidth > operandsWidth
        then do
          -- add to the LO bits
          compileAddB outputWidth out x xs constant
        else -- -- write 0 to the HI bits
        -- writeSliceVal (Slice out operandsWidth outputWidth) 0
          compileAddB outputWidth out x xs constant

compileAddB :: (GaloisField n, Integral n) => Width -> RefU -> (RefU, Bool) -> [(RefU, Bool)] -> U -> M n ()
compileAddB _ out (var, True) [] 0 = 
  case widthOf out `compare` widthOf var of 
    LT -> do 
      let varLO = Slice var 0 (widthOf out)
      writeSliceEq varLO (Slice.fromRefU out)
    EQ -> writeRefUEq out var
    GT -> do 
      let outLO = Slice out 0 (widthOf var)
      let outHI = Slice out (widthOf var) (widthOf out)
      writeSliceEq outLO (Slice.fromRefU var)
      writeSliceVal outHI 0
compileAddB _ out (var, True) [] constant = compileAddBPosConst out var constant
compileAddB _ out (var, False) [] constant = compileAddBNegConst out var constant
compileAddB width out (var1, sign1) ((var2, sign2) : vars) constant = do
  temp <- freshRefU width
  case (sign1, sign2) of
    (True, True) -> do
      compileAddBPosPos temp var1 var2
      compileAddB width out (temp, True) vars constant
    (True, False) -> do
      compileAddBPosNeg width temp var1 var2
      compileAddB width out (temp, True) vars constant
    (False, True) -> do
      compileAddBPosNeg width temp var2 var1
      compileAddB width out (temp, True) vars constant
    (False, False) -> do
      compileAddBPosPos temp var1 var2
      compileAddB width out (temp, False) vars constant -- NOTE: temp is negative here

-- | Adds two positive variables together on a binary field:
--   Assume `as` and `bs` to the operands
--    constraints of a full adder:
--      out[i] = as[i] + bs[i] + carry[i]
--      carry[i+1] = as[i] * bs[i] + as[i] * carry[i] + bs[i] * carry[i]
--    edge case: carry[0] = 0
compileAddBPosPos :: (GaloisField n, Integral n) => RefU -> RefU -> RefU -> M n ()
compileAddBPosPos out as bs = do
  

  let outputWidth = widthOf out
  -- allocates `outputWidth - 1` carry bits
  carryBits <- freshRefU (outputWidth - 1)

  forM_ [0 .. outputWidth - 1] $ \index -> do
    let a =
          if index >= widthOf as
            then Nothing
            else Just $ Slice as index (index + 1)
    let b =
          if index >= widthOf bs
            then Nothing
            else Just $ Slice bs index (index + 1)
    let c = Slice out index (index + 1)
    let prevCarry = if index == 0 then Nothing else Just (Slice carryBits (index - 1) index)
    let nextCarry = if index == outputWidth - 1 then Nothing else Just (Slice carryBits index (index + 1))

    -- out[index] = a + b + prevCarry
    -- nextCarry = a * b + a * prevCarry + b * prevCarry
    case (prevCarry, nextCarry) of
      (Nothing, Nothing) -> do
        -- c = a + b
        case (a, b) of
          (Just refA, Just refB) -> writeAdd 0 [] [(refA, 1), (refB, 1), (c, -1)] -- c = a + b
          (Just refA, Nothing) -> writeSliceEq c refA -- c = a
          (Nothing, Just refB) -> writeSliceEq c refB -- c = b
          (Nothing, Nothing) -> writeSliceVal c 0 -- c = 0
      (Nothing, Just next) -> do
        case (a, b) of
          (Just refA, Just refB) -> do
            -- c = a + b
            writeAdd 0 [] [(refA, 1), (refB, 1), (c, -1)]
            -- next = a * b
            writeMul (0, [], [(refA, 1)]) (0, [], [(refB, 1)]) (0, [], [(next, 1)])
          (Just refA, Nothing) -> do
            -- c = a
            writeSliceEq c refA
            -- next = 0
            writeSliceVal next 0
          (Nothing, Just refB) -> do
            -- c = b
            writeSliceEq c refB
            -- next = 0
            writeSliceVal next 0
          (Nothing, Nothing) -> do
            -- c = 0
            writeSliceVal c 0
            -- next = 0
            writeSliceVal next 0
      (Just prev, Nothing) -> do
        case (a, b) of
          (Just refA, Just refB) -> do
            -- c = a + b + prev
            writeAdd 0 [] [(refA, 1), (refB, 1), (prev, 1), (c, -1)]
          (Just refA, Nothing) -> do
            -- c = a + prev
            writeAdd 0 [] [(refA, 1), (prev, 1), (c, -1)]
          (Nothing, Just refB) -> do
            -- c = b + prev
            writeAdd 0 [] [(refB, 1), (prev, 1), (c, -1)]
          (Nothing, Nothing) -> do
            -- c = prev
            writeSliceEq c prev
      (Just prev, Just next) -> do
        case (a, b) of
          (Just refA, Just refB) -> do
            -- c = a + b + prev
            writeAdd 0 [] [(refA, 1), (refB, 1), (prev, 1), (c, -1)]
            -- next = a * b + a * prev + b * prev
            ab <- freshRefB
            aPrev <- freshRefB
            bPrev <- freshRefB
            -- ab = a * b
            writeMul (0, [], [(refA, 1)]) (0, [], [(refB, 1)]) (0, [(B ab, 1)], [])
            -- aPrev = a * prev
            writeMul (0, [], [(refA, 1)]) (0, [], [(prev, 1)]) (0, [(B aPrev, 1)], [])
            -- bPrev = b * prev
            writeMul (0, [], [(refB, 1)]) (0, [], [(prev, 1)]) (0, [(B bPrev, 1)], [])
            -- next = ab + aPrev + bPrev
            writeAdd 0 [(B ab, 1), (B aPrev, 1), (B bPrev, 1)] [(next, -1)]
          (Just refA, Nothing) -> do
            -- c = a + prev
            writeAdd 0 [] [(refA, 1), (prev, 1), (c, -1)]
            -- next = 0 + a * prev + 0
            writeMul (0, [], [(refA, 1)]) (0, [], [(prev, 1)]) (0, [], [(next, 1)])
          (Nothing, Just refB) -> do
            -- c = b + prev
            writeAdd 0 [] [(refB, 1), (prev, 1), (c, -1)]
            -- next = 0 + b * prev + 0
            writeMul (0, [], [(refB, 1)]) (0, [], [(prev, 1)]) (0, [], [(next, 1)])
          (Nothing, Nothing) -> do
            -- c = prev
            writeSliceEq c prev
            -- next = 0
            writeSliceVal next 0

-- | Adds a positive variable and a constant together on a binary field:
--   Assume `as` to be the variable and `bs` to be the constant
--    constraints of a full adder:
--      out[i] = as[i] + bs[i] + carry[i]
--      carry[i+1] = as[i] * bs[i] + as[i] * carry[i] + bs[i] * carry[i]
--    edge case: carry[0] = 0
compileAddBPosConst :: (GaloisField n, Integral n) => RefU -> RefU -> U -> M n ()
compileAddBPosConst out as bs = do
  let outputWidth = widthOf out
  -- allocates `outputWidth - 1` carry bits
  carryBits <- freshRefU (outputWidth - 1)

  forM_ [0 .. outputWidth - 1] $ \index -> do
    let a =
          if index >= widthOf as
            then Nothing
            else Just $ Slice as index (index + 1)
    let b
          | index >= widthOf bs = 0
          | Data.Bits.testBit bs index = 1
          | otherwise = 0
    let c = Slice out index (index + 1)
    let prevCarry = if index == 0 then Nothing else Just (Slice carryBits (index - 1) index)
    let nextCarry = if index == outputWidth - 1 then Nothing else Just (Slice carryBits index (index + 1))

    -- out[index] = a + b + prevCarry
    -- nextCarry = a * b + a * prevCarry + b * prevCarry
    case (prevCarry, nextCarry) of
      (Nothing, Nothing) -> do
        case a of
          Nothing -> writeSliceVal c (toInteger b) -- c = b
          Just refA -> writeAdd b [] [(refA, 1), (c, -1)] -- c = a + b
      (Nothing, Just next) -> do
        case a of
          Nothing -> do
            -- c = b
            writeSliceVal c (toInteger b)
            -- next = 0
            writeSliceVal next 0
          Just refA -> do
            -- c = a + b
            writeAdd b [] [(refA, 1), (c, -1)]
            -- next = a * b
            writeAdd 0 [] [(refA, b), (next, -1)]
      (Just prev, Nothing) -> do
        case a of
          Nothing -> writeAdd b [] [(prev, 1), (c, -1)] -- c = b + prev
          Just refA -> writeAdd b [] [(refA, 1), (prev, 1), (c, -1)] -- c = a + b + prev
      (Just prev, Just next) -> do
        case a of
          Nothing -> do
            -- c = b + prev
            writeAdd b [] [(prev, 1), (c, -1)]
            -- next = bPrev
            writeAdd 0 [] [(prev, b), (next, -1)]
          Just refA -> do
            -- c = a + b + prev
            writeAdd b [] [(refA, 1), (prev, 1), (c, -1)]
            aPrev <- freshRefB
            -- aPrev = a * prev
            writeMul (0, [], [(refA, 1)]) (0, [], [(prev, 1)]) (0, [(B aPrev, 1)], [])
            -- next = ab + aPrev + bPrev
            writeAdd 0 [(B aPrev, 1)] [(refA, b), (prev, b), (next, -1)]

-- | Adds a negative variable and a constant together on a binary field:
--   Assume `as` to the variable and `bs` to be the constant
--    constraints of a full adder:
--      out[i] = as[i] + bs[i] + carry[i] + 1
--      carry[i+1] = (1 + as[i]) * bs[i] + (1 + as[i]) * carry[i] + bs[i] * carry[i]
--      carry[i+1] = as[i] * bs[i] + as[i] * carry[i] + bs[i] * carry[i] + bs[i] + carry[i]
--    edge case: carry[0] = 1
compileAddBNegConst :: (GaloisField n, Integral n) => RefU -> RefU -> U -> M n ()
compileAddBNegConst out as bs = do
  let outputWidth = widthOf out
  -- allocates `outputWidth - 1` carry bits
  carryBits <- freshRefU (outputWidth - 1)

  forM_ [0 .. outputWidth - 1] $ \index -> do
    let a = B (RefUBit as index)
    let b = if Data.Bits.testBit bs index then 1 else 0
    let c = B (RefUBit out index)
    let prevCarry = if index == 0 then Nothing else Just (B (RefUBit carryBits (index - 1)))
    let nextCarry = if index == outputWidth - 1 then Nothing else Just (B (RefUBit carryBits index))
    -- out[index] = a + b + prevCarry + 1
    -- nextCarry = a * b + a * prevCarry + b * prevCarry + b + prevCarry
    case (prevCarry, nextCarry) of
      (Nothing, Nothing) -> do
        -- c = a + b + prev + 1
        --   = a + b
        writeAdd b [(a, 1), (c, -1)] []
      (Nothing, Just next) -> do
        -- c = a + b + prev + 1
        --   = a + b
        writeAdd b [(a, 1), (c, -1)] []
        -- next = a * b + a * prev + b * prev + b + prev
        --      = a * (b + 1) + 1
        writeAdd 1 [(a, b + 1), (next, -1)] []
      (Just prev, Nothing) -> do
        -- c = a + b + prev + 1
        writeAdd (b + 1) [(a, 1), (prev, 1), (c, -1)] []
      (Just prev, Just next) -> do
        -- c = a + b + prev + 1
        writeAdd (b + 1) [(a, 1), (prev, 1), (c, -1)] []
        -- next = a * b + a * prev + (b + 1) * prev + b + prev
        aPrev <- freshRefB
        -- aPrev = a * prev
        writeMul (0, [(a, 1)], []) (0, [(prev, 1)], []) (0, [(B aPrev, 1)], [])
        -- next = ab + aPrev + bPrev + b + prev
        writeAdd b [(a, b), (B aPrev, 1), (prev, b + 1), (next, -1)] []

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
    let a = B (RefUBit as index)
    let b = B (RefUBit bs index)
    let c = B (RefUBit out index)
    let prevCarry = if index == 0 then Nothing else Just (B (RefUBit carryBits (index - 1)))
    let nextCarry = if index == width - 1 then Nothing else Just (B (RefUBit carryBits index))

    -- out[index] = a + b + prevCarry + 1
    -- nextCarry = a * b + a * prevCarry + b * prevCarry + a + prevCarry
    case (prevCarry, nextCarry) of
      (Nothing, Nothing) -> do
        -- c = a + b + prev + 1
        --   = a + b
        writeAdd 0 [(a, 1), (b, 1), (c, -1)] []
      (Nothing, Just next) -> do
        -- c = a + b + prev + 1
        --   = a + b
        writeAdd 0 [(a, 1), (b, 1), (c, -1)] []
        -- next = a * b + a * prev + b * prev + a + prev
        --      = a * b + b + 1
        writeMul (0, [(a, 1)], []) (0, [(b, 1)], []) (-1, [(next, 1), (b, -1)], [])
      (Just prev, Nothing) -> do
        -- c = a + b + prev + 1
        writeAdd 1 [(a, 1), (b, 1), (prev, 1), (c, -1)] []
      (Just prev, Just next) -> do
        -- c = a + b + prev + 1
        writeAdd 1 [(a, 1), (b, 1), (prev, 1), (c, -1)] []
        -- next = a * b + a * prev + b * prev + a + prev
        ab <- freshRefB
        aPrev <- freshRefB
        bPrev <- freshRefB
        -- ab = a * b
        writeMul (0, [(a, 1)], []) (0, [(b, 1)], []) (0, [(B ab, 1)], [])
        -- aPrev = a * prev
        writeMul (0, [(a, 1)], []) (0, [(prev, 1)], []) (0, [(B aPrev, 1)], [])
        -- bPrev = b * prev
        writeMul (0, [(b, 1)], []) (0, [(prev, 1)], []) (0, [(B bPrev, 1)], [])
        -- next = ab + aPrev + bPrev + a + prev
        writeAdd 0 [(B ab, 1), (B aPrev, 1), (B bPrev, 1), (a, 1), (prev, 1), (next, -1)] []