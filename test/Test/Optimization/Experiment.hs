{-# LANGUAGE DataKinds #-}

module Test.Optimization.Experiment (tests, run) where

import Keelung hiding (compileO0)
import Keelung.Compiler.Options qualified as Options
import Keelung.Compiler.Syntax.Internal as I
import Keelung.Syntax.Counters qualified as Counters
import Test.Hspec
import Test.Optimization.Util

run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = describe "Experiment" $ do
  -- describe "pow" $ do
  --   let program power = do
  --         n <- input Public
  --         return (n `pow` power)
  --   describe "Frobenius endomorphism" $ do
  --     it "n^256 = n (Binary 283)" $ do
  --       (cs, cs') <- executeGF181 $ do
  --         x <- input Public
  --         y <- input Public
  --         return $ x * y
  --       cs `shouldHaveSize` 42
  --       cs' `shouldHaveSize` 33
  -- it "n^255 = n (Binary 283)" $ do
  --   property $ \(n :: Binary 283) -> do
  --     validate (Binary 283) (program 255) [toInteger n] [] [1]
  -- it "n^254 = n (Binary 283)" $ do
  --   property $ \(n :: Binary 283) -> do
  --     validate (Binary 283) (program 254) [toInteger n] [] [toInteger (n ^ (254 :: Int))]

  -- 4 * 3 for input / output
  -- 4 for output
  -- 1 for multiplication
  -- 8 - 2 for multiplication output

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
      -- validateInternalSyntax internal2 [10, 7] [] [20]
      debugI internal2
      shouldHaveSizeWithOptsI Options.defaultOptions internal2 17


constructSyntaxVV :: Width -> Width -> Internal n
constructSyntaxVV outputWidth operandWidth =
  I.Internal
    { internalExpr = [(0, I.ExprU (I.MulU outputWidth (I.VarUI operandWidth 0) (I.VarUI operandWidth 1)))],
      internalFieldBitWidth = 181,
      internalCounters = Counters.addCount (Counters.Output, Counters.WriteUInt outputWidth) 1 $ Counters.addCount (Counters.PublicInput, Counters.WriteUInt operandWidth) 2 mempty,
      internalAssertions = [],
      internalSideEffects = mempty
    }