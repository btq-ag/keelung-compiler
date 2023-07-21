{-# LANGUAGE DataKinds #-}

module Test.Interpreter.UInt.DivMod (tests, run) where

import Keelung hiding (compile)
import Keelung.Compiler.Compile.Error qualified as Compiler
import Keelung.Compiler.Error (Error (..))
import Keelung.Interpreter qualified as Interpreter
import Test.Hspec
import Test.Interpreter.Util
import Test.QuickCheck hiding ((.&.))

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests =
  describe "DivMod" $ do
    -- it "performDivMod (quotient & remainder unknown)" $ do
    --   let program = do
    --         dividend <- input Public :: Comp (UInt 8)
    --         divisor <- input Public
    --         performDivMod dividend divisor

    --   let genPair = do
    --         dividend <- choose (0, 255)
    --         divisor <- choose (1, 255)
    --         return (dividend, divisor)

    --   forAll genPair $ \(dividend, divisor) -> do
    --     let expected = [dividend `div` divisor, dividend `mod` divisor]
    --     runAll gf181 program [dividend, divisor] [] expected
    --     runAll (Prime 17) program [dividend, divisor] [] expected

    -- it "performDivMod (on constants) (issue #18)" $ do
    --   let program dividend divisor = performDivMod (fromInteger dividend) (fromInteger divisor :: UInt 4)
    --   let genPair = do
    --         dividend <- choose (0, 15)
    --         divisor <- choose (1, 15)
    --         return (dividend, divisor)
    --   forAll genPair $ \(dividend, divisor) -> do
    --     let expected = [dividend `div` divisor, dividend `mod` divisor]
    --     runAll gf181 (program dividend divisor) [] [] expected
    --     runAll (Prime 17) (program dividend divisor) [] [] expected

    -- it "assertDivMod (with wrong quotient constant)" $ do
    --   let program = assertDivMod 7 (3 :: UInt 4) 3 1
    --   throwBoth
    --     (Prime 17)
    --     program
    --     []
    --     []
    --     (InterpreterError (Interpreter.DivModQuotientError 7 3 2 3))
    --     (CompilerError (Compiler.ConflictingValuesB True False) :: Error GF181)

    -- it "assertDivMod (with wrong remainder constant)" $ do
    --   let program = assertDivMod 7 (3 :: UInt 4) 2 0
    --   throwBoth
    --     (Prime 17)
    --     program
    --     []
    --     []
    --     (InterpreterError (Interpreter.DivModRemainderError 7 3 1 0))
    --     (CompilerError (Compiler.ConflictingValuesB False True) :: Error GF181)

    -- it "assertDivMod (multiple statements)" $ do
    --   let program = do
    --         a <- input Public :: Comp (UInt 5)
    --         b <- input Public
    --         c <- input Private
    --         d <- input Public
    --         (q0, r0) <- performDivMod a b
    --         (q1, r1) <- performDivMod c d
    --         return [q0, r0, q1, r1]
    --   runAll (Prime 17) program [20, 7, 8] [21] [2, 6, 2, 5]

    -- it "assertDivMod (multiple statements chained together)" $ do
    --   let program = do
    --         a <- input Public :: Comp (UInt 5)
    --         b <- input Public
    --         (q0, r0) <- performDivMod a b
    --         (q1, r1) <- performDivMod q0 b
    --         return [q0, r0, q1, r1]
    --   runAll (Prime 17) program [25, 3] [] [8, 1, 2, 2]

    -- it "performDivMod (before assertions)" $ do
    --   let program = do
    --         a <- input Public :: Comp (UInt 5)
    --         b <- input Public
    --         (q, r) <- performDivMod a b
    --         assert $ q `eq` r
    --   runAll (Prime 17) program [10, 4] [] []

    -- it "performDivMod (before reuse)" $ do
    --   let program = do
    --         a <- input Public :: Comp (UInt 5)
    --         b <- input Public
    --         (q, _) <- performDivMod a b
    --         reuse q
    --   runAll (Prime 17) program [10, 4] [] [2]

    -- it "performDivMod (after reuse)" $ do
    --   let program = do
    --         a <- reuse =<< input Public :: Comp (UInt 5)
    --         b <- input Public
    --         (q, r) <- performDivMod a b
    --         assert $ q `eq` r
    --   runAll (Prime 17) program [10, 4] [] []

    -- it "performDivMod (dividend unknown)" $ do
    --   let program dividend divisor = performDivMod (fromInteger dividend) (fromInteger divisor :: UInt 4)
    --   let genPair = do
    --         dividend <- choose (0, 15)
    --         divisor <- choose (1, 15)
    --         return (dividend, divisor)
    --   forAll genPair $ \(dividend, divisor) -> do
    --     let expected = [dividend `div` divisor, dividend `mod` divisor]
    --     runAll gf181 (program dividend divisor) [] [] expected
    --     runAll (Prime 17) (program dividend divisor) [] [] expected

    -- it "assertDivMod (dividend unknown)" $ do
    --   let program = do
    --         dividend <- freshVarUInt
    --         divisor <- input Public :: Comp (UInt 6)
    --         quotient <- input Public
    --         remainder <- input Private
    --         assertDivMod dividend divisor quotient remainder
    --         return dividend
    --   runAll gf181 program [14, 12] [0] [40]

    -- let genPair = do
    --       divisor <- choose (1, 63)
    --       quotient <- choose (0, 63)
    --       remainder <- choose (0, 63)
    --       return (divisor, quotient, remainder)
    -- forAll genPair $ \(divisor, quotient, remainder) -> do
    --   let expected = [(quotient * divisor + remainder) `mod` 64]
    --   runAll gf181 program [divisor, quotient] [remainder] expected
    --   runAll (Prime 17) program [divisor, quotient] [remainder] expected

    it "assertDivMod (divisor & remainder unknown)" $ do
      let program = do
            dividend <- input Public :: Comp (UInt 4)
            divisor <- freshVarUInt
            quotient <- input Public
            remainder <- freshVarUInt
            assertDivMod dividend divisor quotient remainder
            return (divisor, remainder)

      -- let genPair = do
      --       dividend <- choose (0, 15)
      --       quotient <- choose (0, 15)
      --       return (dividend, quotient)
      -- forAll genPair $ \(dividend, quotient) -> do
      --   let expected =
      --         if quotient == 0
      --           then [0, dividend]
      --           else [dividend `div` quotient, dividend `mod` quotient]
      --   -- runAll gf181 program [dividend, quotient] [] expected
      --   runAll (Prime 17) program [dividend, quotient] [] expected
      runAll (Prime 17) program [1, 13] [] [0, 1]

    -- it "assertDivMod (quotient & remainder unknown)" $ do
    --   let program = do
    --         dividend <- input Public :: Comp (UInt 6)
    --         divisor <- input Public
    --         quotient <- freshVarUInt
    --         remainder <- freshVarUInt
    --         assertDivMod dividend divisor quotient remainder
    --         return (quotient, remainder)
            
    --   let genPair = do
    --         dividend <- choose (0, 15)
    --         divisor <- choose (1, 15)
    --         return (dividend, divisor)
    --   forAll genPair $ \(dividend, divisor) -> do
    --     let expected = [dividend `div` divisor, dividend `mod` divisor]
    --     runAll gf181 program [dividend, divisor] [] expected
    --     runAll (Prime 17) program [dividend, divisor] [] expected

    -- it "assertDivMod (quotient & remainder unknown)" $ do
    --   let program = do
    --         dividend <- input Public :: Comp (UInt 6)
    --         divisor <- freshVarUInt
    --         quotient <- input Public
    --         remainder <- input Public
    --         assertDivMod dividend divisor quotient remainder
    --         return divisor
            
    --   let genPair = do
    --         dividend <- choose (0, 63)
    --         quotient <- choose (0, 63)
    --         remainder <- choose (0, 63)
    --         return (dividend, divisor)
    --   forAll genPair $ \(dividend, divisor) -> do
    --     let expected = [dividend `div` divisor, dividend `mod` divisor]
    --     runAll gf181 program [dividend, divisor] [] expected
    --     runAll (Prime 17) program [dividend, divisor] [] expected

--   runAll (Prime 17) program [34, 6] [] [5, 4]