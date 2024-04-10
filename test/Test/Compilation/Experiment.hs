{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Compilation.Experiment (run, tests) where

import Keelung hiding (MulU, VarUI)
import Keelung.Compiler.Syntax.Internal
import Keelung.Syntax.Counters qualified as Counters
import Test.Arbitrary ()
import Test.Compilation.Util
import Test.Hspec

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
  --     solveOutput gf181 program [2] [] `shouldReturn` [0]
  --     solveOutput gf181 program [1] [] `shouldReturn` [0]
  --     solveOutput gf181 program [0] [] `shouldReturn` [1]

  describe "variable-width multiplication" $ do
    it "0" $ do
      -- let program = do
      --       x <- input Public :: Comp (UInt 8)
      --       y <- input Public :: Comp (UInt 8)
      --       return $ x * y
      -- let elaborated = Compiler.elaborateAndEncode program :: Either (Compiler.Error GF181) Compiler.Elaborated
      -- let internal = ToInternal.run gf181Info <$> elaborated :: Either (Compiler.Error GF181) (Compiler.Internal GF181)
      -- case internal of
      --   Left err -> print err
      --   Right syntax -> validateInternalSyntax syntax [20, 20] [] [144]

      let internal2 = constructSyntaxVV 6 4 :: Internal GF181
      validateInternalSyntax internal2 [10, 7] [] [20]

constructSyntaxVV :: Width -> Width -> Internal n
constructSyntaxVV outputWidth operandWidth =
  Internal
    { internalExpr = [(0, ExprU (MulU outputWidth (VarUI operandWidth 0) (VarUI operandWidth 1)))],
      internalFieldBitWidth = 181,
      internalCounters = Counters.addCount (Counters.Output, Counters.WriteUInt outputWidth) 1 $ Counters.addCount (Counters.PublicInput, Counters.WriteUInt operandWidth) 2 mempty,
      internalAssertions = [],
      internalSideEffects = mempty
    }