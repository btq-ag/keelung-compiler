{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Compilation.Experiment (run, tests) where

import Keelung hiding (MulU, VarUI)
import Keelung.Compiler.Syntax.Internal
import Keelung.Syntax.Counters qualified as Counters
import Test.Arbitrary ()
import Test.Hspec
import Test.Util

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

-- | Equalities:
--    introduce a new variable m
--    if input = 0 then m = 0 else m = recip input
--    Equality:
--      input * m = 1 - output
--      input * output = 0
tests :: SpecWith ()
tests = describe "Experiment" $ do

    describe "performDivMod" $ do
      it "variable dividend / variable divisor" $ do
        let program = do
              dividend <- input Public :: Comp (UInt 8)
              divisor <- input Public
              performDivMod dividend divisor

        let (dividend, divisor) = (4, 35)
        let expected = [dividend `div` divisor, dividend `mod` divisor]
        -- forM_ [gf181, Prime 17] $ \field -> do
        checkO0 gf181 program [dividend, divisor] [] expected
          -- check field program [dividend, divisor] [] expected
          
  -- describe "variable-width multiplication" $ do
  --   -- it "0" $ do
  --   --   let internal2 = constructSyntaxVV 6 4 :: Internal GF181
  --   --   checkI gf181 internal2 [10, 7] [] [6]
  --   --   assertCountI gf181 internal2 17

  --   it "2 positive variables / Byte" $ do
  --     let internal2 = constructSyntaxVV 8 8 :: Internal GF181
  --     checkI (Prime 17) internal2 [0, 0] [] [0]

_constructSyntaxVV :: Width -> Width -> Internal n
_constructSyntaxVV outputWidth operandWidth =
  Internal
    { internalExpr = [(0, ExprU (MulUV outputWidth (VarUI operandWidth 0) (VarUI operandWidth 1)))],
      internalFieldBitWidth = 4,
      internalCounters = Counters.addCount (Counters.Output, Counters.WriteUInt outputWidth) 1 $ Counters.addCount (Counters.PublicInput, Counters.WriteUInt operandWidth) 2 mempty,
      internalAssertions = [],
      internalSideEffects = mempty
    }