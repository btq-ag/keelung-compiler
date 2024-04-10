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
  -- describe "freshVarField" $ do
  --   it "equals zero" $ do
  --     let program = do
  --           x <- inputField Public
  --           out <- freshVarField
  --           m <- freshVarField
  --           assert $ (x * m) `eq` (1 - out)
  --           assert $ (x * out) `eq` 0
  --           return out
  --     solve gf181 program [2] [] `shouldReturn` [0]
  --     solve gf181 program [1] [] `shouldReturn` [0]
  --     solve gf181 program [0] [] `shouldReturn` [1]

  describe "variable-width multiplication" $ do
    it "0" $ do
      let internal2 = constructSyntaxVV 6 4 :: Internal GF181
      -- debugI gf181 internal2
      checkI gf181 internal2 [10, 7] [] [6]
      assertCountI gf181 internal2 3

constructSyntaxVV :: Width -> Width -> Internal n
constructSyntaxVV outputWidth operandWidth =
  Internal
    { internalExpr = [(0, ExprU (MulUV outputWidth (VarUI operandWidth 0) (VarUI operandWidth 1)))],
      internalFieldBitWidth = 181,
      internalCounters = Counters.addCount (Counters.Output, Counters.WriteUInt outputWidth) 1 $ Counters.addCount (Counters.PublicInput, Counters.WriteUInt operandWidth) 2 mempty,
      internalAssertions = [],
      internalSideEffects = mempty
    }