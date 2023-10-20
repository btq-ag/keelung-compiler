{-# LANGUAGE DataKinds #-}

module Test.Compilation.UInt.DivMod (tests, run) where

import Data.Field.Galois (Prime)
import Keelung hiding (compile)
import Keelung.Compiler.Error (Error (..))
import Keelung.Interpreter qualified as Interpreter
import Keelung.Solver.Monad qualified as Solver
import Test.Hspec
import Test.Compilation.Util
import Test.QuickCheck hiding ((.&.))

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests =
  describe "DivMod" $ do
    it "performDivMod (quotient & remainder unknown)" $ do
      let program = do
            dividend <- input Public :: Comp (UInt 8)
            divisor <- input Public
            performDivMod dividend divisor

      let genPair = do
            dividend <- choose (0, 255)
            divisor <- choose (1, 255)
            return (dividend, divisor)

      forAll genPair $ \(dividend, divisor) -> do
        let expected = [dividend `div` divisor, dividend `mod` divisor]
        runAll gf181 program [dividend, divisor] [] expected
        runAll (Prime 17) program [dividend, divisor] [] expected
    -- let dividend = 13
    -- let divisor = 6
    -- let expected = [dividend `div` divisor, dividend `mod` divisor]
    -- -- debug gf181 program
    -- -- debug (Prime 17) program

    -- runAll gf181 program [dividend, divisor] [] expected
    -- runAll (Prime 17) program [dividend, divisor] [] expected

    -- runAll (Prime 17) program [dividend, divisor] [] expected

    it "performDivMod (on constants) (issue #18)" $ do
      let program dividend divisor = performDivMod (fromInteger dividend) (fromInteger divisor :: UInt 4)
      let genPair = do
            dividend <- choose (0, 15)
            divisor <- choose (1, 15)
            return (dividend, divisor)
      forAll genPair $ \(dividend, divisor) -> do
        let expected = [dividend `div` divisor, dividend `mod` divisor]
        runAll gf181 (program dividend divisor) [] [] expected
        runAll (Prime 17) (program dividend divisor) [] [] expected
    -- let dividend = 13
    -- let divisor = 6
    -- let expected = [dividend `div` divisor, dividend `mod` divisor]
    -- runAll gf181 (program dividend divisor) [] [] expected
    -- runAll (Prime 17) (program dividend divisor) [] [] expected

    it "assertDivMod (with wrong quotient constant)" $ do
      let program = assertDivMod 7 (3 :: UInt 4) 3 1
      throwBoth
        (Prime 17)
        program
        []
        []
        (InterpreterError (Interpreter.DivModQuotientError False 7 3 2 3))
        (SolverError Solver.ConflictingValues :: Error (Prime 17))

    it "assertDivMod (with wrong remainder constant)" $ do
      let program = assertDivMod 7 (3 :: UInt 4) 2 0
      throwBoth
        (Prime 17)
        program
        []
        []
        (InterpreterError (Interpreter.DivModRemainderError False 7 3 1 0))
        (SolverError Solver.ConflictingValues :: Error (Prime 17))

    it "performDivMod (multiple statements)" $ do
      let program = do
            a <- input Public :: Comp (UInt 5)
            b <- input Public
            c <- input Private
            d <- input Public
            (q0, r0) <- performDivMod a b
            (q1, r1) <- performDivMod c d
            return [q0, r0, q1, r1]
      runAll (Prime 17) program [20, 7, 8] [21] [2, 6, 2, 5]

    it "performDivMod (multiple statements chained together)" $ do
      let program = do
            a <- input Public :: Comp (UInt 5)
            b <- input Public
            (q0, r0) <- performDivMod a b
            (q1, r1) <- performDivMod q0 b
            return [q0, r0, q1, r1]
      runAll (Prime 17) program [25, 3] [] [8, 1, 2, 2]

    it "performDivMod (before assertions)" $ do
      let program = do
            a <- input Public :: Comp (UInt 5)
            b <- input Public
            (q, r) <- performDivMod a b
            assert $ q `eq` r
      runAll (Prime 17) program [10, 4] [] []

    it "performDivMod (before reuse)" $ do
      let program = do
            a <- input Public :: Comp (UInt 5)
            b <- input Public
            (q, _) <- performDivMod a b
            reuse q
      runAll (Prime 17) program [10, 4] [] [2]

    it "performDivMod (after reuse)" $ do
      let program = do
            a <- reuse =<< input Public :: Comp (UInt 5)
            b <- input Public
            (q, r) <- performDivMod a b
            assert $ q `eq` r
      runAll (Prime 17) program [10, 4] [] []

    it "performDivMod (dividend unknown)" $ do
      let program dividend divisor = performDivMod (fromInteger dividend) (fromInteger divisor :: UInt 4)
      let genPair = do
            dividend <- choose (0, 15)
            divisor <- choose (1, 15)
            return (dividend, divisor)
      forAll genPair $ \(dividend, divisor) -> do
        let expected = [dividend `div` divisor, dividend `mod` divisor]
        runAll gf181 (program dividend divisor) [] [] expected
        runAll (Prime 17) (program dividend divisor) [] [] expected

    -- it "assertDivMod (dividend unknown)" $ do
    --   let program = do
    --         dividend <- freshVarUInt
    --         divisor <- input Public :: Comp (UInt 6)
    --         quotient <- input Public
    --         remainder <- input Private
    --         assertDivMod dividend divisor quotient remainder
    --         return dividend
    --   -- runAll gf181 program [14, 12] [0] [40]

    --   let genPair = do
    --         divisor <- choose (1, 63)
    --         quotient <- choose (0, 63)
    --         remainder <- choose (0, divisor - 1)
    --         return (divisor, quotient, remainder)
    --   forAll genPair $ \(divisor, quotient, remainder) -> do
    --     let expected = [(quotient * divisor + remainder) `mod` 64]
    --     runAll gf181 program [divisor, quotient] [remainder] expected
    --     runAll (Prime 17) program [divisor, quotient] [remainder] expected

    it "assertDivMod (divisor & remainder unknown & quotient = 0)" $ do
      let program = do
            dividend <- input Public :: Comp (UInt 4)
            divisor <- freshVarUInt
            quotient <- input Public
            remainder <- freshVarUInt
            assertDivMod dividend divisor quotient remainder
            return (divisor, remainder)

      forAll (choose (1, 15)) $ \dividend -> do
        throwBoth
          (Prime 17)
          program
          [dividend, 0]
          []
          (InterpreterError Interpreter.DivModQuotientIsZeroError)
          (SolverError (Solver.QuotientIsZeroError [(4, Left 12)]) :: Error (Prime 17))

    it "assertDivMod (divisor & remainder unknown & dividend = 0)" $ do
      let program = do
            dividend <- input Public :: Comp (UInt 4)
            divisor <- freshVarUInt
            quotient <- input Public
            remainder <- freshVarUInt
            assertDivMod dividend divisor quotient remainder
            return (divisor, remainder)

      forAll (choose (1, 15)) $ \quotient -> do
        throwBoth
          (Prime 17)
          program
          [0, quotient]
          []
          (InterpreterError Interpreter.DivModDividendIsZeroError)
          (SolverError (Solver.DividendIsZeroError [(4, Left 8)]) :: Error (Prime 17))

    it "assertDivMod (divisor & remainder unknown)" $ do
      let program = do
            dividend <- input Public :: Comp (UInt 4)
            divisor <- freshVarUInt
            quotient <- input Public
            remainder <- freshVarUInt
            assertDivMod dividend divisor quotient remainder
            return (divisor, remainder)

      let genPair = do
            dividend <- choose (1, 15)
            quotient <- choose (1, 15)
            let (divisor, remainder) = dividend `divMod` quotient
            if remainder >= divisor
              then genPair
              else return (dividend, quotient)

      forAll genPair $ \(dividend, quotient) -> do
        let expected = [dividend `div` quotient, dividend `mod` quotient]
        runAll (Prime 17) program [dividend, quotient] [] expected
        runAll gf181 program [dividend, quotient] [] expected

    it "assertDivMod (quotient & remainder unknown)" $ do
      let program = do
            dividend <- input Public :: Comp (UInt 6)
            divisor <- input Public
            quotient <- freshVarUInt
            remainder <- freshVarUInt
            assertDivMod dividend divisor quotient remainder
            return (quotient, remainder)

      let genPair = do
            dividend <- choose (0, 15)
            divisor <- choose (1, 15)
            return (dividend, divisor)
      forAll genPair $ \(dividend, divisor) -> do
        let expected = [dividend `div` divisor, dividend `mod` divisor]
        runAll gf181 program [dividend, divisor] [] expected
        runAll (Prime 17) program [dividend, divisor] [] expected