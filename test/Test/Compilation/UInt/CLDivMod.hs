{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Compilation.UInt.CLDivMod (tests, run) where

import Data.Field.Galois (Prime)
import Keelung
import Keelung.Compiler.Error (Error (..))
import Keelung.Data.U qualified as U
import Keelung.Interpreter qualified as Interpreter
import Keelung.Solver qualified as Solver
import Test.Compilation.Util
import Test.Hspec
import Test.QuickCheck hiding ((.&.))

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

-- | Carry-less division on Integer
clDiv :: Width -> Integer -> Integer -> Integer
clDiv width x y = U.uValue (U.new width x `U.clDiv` U.new width y)

-- | Carry-less modolu on Integer
clMod :: Width -> Integer -> Integer -> Integer
clMod width x y = U.uValue (U.new width x `U.clMod` U.new width y)

tests :: SpecWith ()
tests =
  describe "Carry-less Div/Mod" $ do
    it "performCLDivMod (quotient & remainder unknown)" $ do
      let width = 8
      let program = do
            dividend <- input Public :: Comp (UInt 8)
            divisor <- input Public
            performCLDivMod dividend divisor

      let genPair = do
            dividend <- choose (0, 255)
            divisor <- choose (1, 255)
            return (dividend, divisor)

      forAll genPair $ \(dividend, divisor) -> do
        let expected = [clDiv width dividend divisor, clMod width dividend divisor]
        runAll gf181 program [dividend, divisor] [] expected
        runAll (Prime 17) program [dividend, divisor] [] expected

    it "assertCLDivMod (with wrong quotient constant)" $ do
      let program = assertCLDivMod 7 (3 :: UInt 4) 3 1
      throwBoth
        (Prime 17)
        program
        []
        []
        (InterpreterError (Interpreter.DivModQuotientError True 7 3 2 3))
        (SolverError Solver.ConflictingValues :: Error (Prime 17))

    it "assertCLDivMod (with wrong remainder constant)" $ do
      let program = assertCLDivMod 7 (3 :: UInt 4) 2 0
      throwBoth
        (Prime 17)
        program
        []
        []
        (InterpreterError (Interpreter.DivModRemainderError True 7 3 1 0))
        (SolverError Solver.ConflictingValues :: Error (Prime 17))

    it "performCLDivMod (single statements)" $ do
      let program = do
            a <- input Public :: Comp (UInt 5)
            b <- input Public
            (q0, r0) <- performCLDivMod a b
            return [q0, r0]
      runAll (Prime 17) program [20, 7] [] [7, 1]

    it "performCLDivMod (multiple statements)" $ do
      let program = do
            a <- input Public :: Comp (UInt 5)
            b <- input Public
            (q0, r0) <- performCLDivMod a b
            c <- input Public
            d <- input Public
            (q1, r1) <- performCLDivMod c d
            return [q0, r0, q1, r1]
      runAll gf181 program [20, 7, 21, 8] [] [7, 1, 2, 5]

    it "performCLDivMod (multiple statements chained together)" $ do
      let program = do
            a <- input Public :: Comp (UInt 5)
            b <- input Public
            (q0, r0) <- performCLDivMod a b
            (q1, r1) <- performCLDivMod q0 b
            return [q0, r0, q1, r1]
      runAll (Prime 17) program [25, 3] [] [8, 1, 7, 1]

    it "performCLDivMod (before assertions)" $ do
      let program = do
            a <- input Public :: Comp (UInt 5)
            b <- input Public
            (q, r) <- performCLDivMod a b
            assert $ q `eq` r
      runAll (Prime 17) program [10, 4] [] []

    it "performCLDivMod (before reuse)" $ do
      let program = do
            a <- input Public :: Comp (UInt 5)
            b <- input Public
            (q, _) <- performCLDivMod a b
            reuse q
      runAll (Prime 17) program [10, 4] [] [2]

    it "performCLDivMod (after reuse)" $ do
      let program = do
            a <- reuse =<< input Public :: Comp (UInt 5)
            b <- input Public
            (q, r) <- performCLDivMod a b
            assert $ q `eq` r
      runAll (Prime 17) program [10, 4] [] []

    it "performCLDivMod (dividend unknown)" $ do
      let program dividend divisor = performCLDivMod (fromInteger dividend) (fromInteger divisor :: UInt 4)
      let genPair = do
            dividend <- choose (0, 15)
            divisor <- choose (1, 15)
            return (dividend, divisor)
      forAll genPair $ \(dividend, divisor) -> do
        let expected = [clDiv 4 dividend divisor, clMod 4 dividend divisor]
        runAll gf181 (program dividend divisor) [] [] expected
        runAll (Prime 17) (program dividend divisor) [] [] expected

    it "assertCLDivMod (divisor & remainder unknown & quotient = 0)" $ do
      let program = do
            dividend <- input Public :: Comp (UInt 4)
            divisor <- freshVarUInt
            quotient <- input Public
            remainder <- freshVarUInt
            assertCLDivMod dividend divisor quotient remainder
            return (divisor, remainder)

      forAll (choose (1, 15)) $ \dividend -> do
        throwBoth
          (Prime 17)
          program
          [dividend, 0]
          []
          (InterpreterError Interpreter.DivModQuotientIsZeroError)
          (SolverError (Solver.QuotientIsZeroError (4, Left 12)) :: Error (Prime 17))

    it "assertCLDivMod (divisor & remainder unknown & dividend = 0)" $ do
      let program = do
            dividend <- input Public :: Comp (UInt 4)
            divisor <- freshVarUInt
            quotient <- input Public
            remainder <- freshVarUInt
            assertCLDivMod dividend divisor quotient remainder
            return (divisor, remainder)

      forAll (choose (1, 15)) $ \quotient -> do
        throwBoth
          (Prime 17)
          program
          [0, quotient]
          []
          (InterpreterError Interpreter.DivModDividendIsZeroError)
          (SolverError (Solver.DividendIsZeroError (4, Left 8)) :: Error (Prime 17))

    -- it "assertCLDivMod (divisor & remainder unknown)" $ do
    --   let program = do
    --         dividend <- input Public :: Comp (UInt 4)
    --         divisor <- freshVarUInt
    --         quotient <- input Public
    --         remainder <- freshVarUInt
    --         assertCLDivMod dividend divisor quotient remainder
    --         return (divisor, remainder)

    --   let genPair = do
    --         dividend <- choose (1, 15)
    --         quotient <- choose (1, 15)
    --         let divisor = clDiv 4 dividend quotient
    --         let remainder = clMod 4 dividend quotient
    --         if remainder >= divisor
    --           then genPair
    --           else return (dividend, quotient)

    --   forAll genPair $ \(dividend, quotient) -> do
    --     let expected = [clDiv 4 dividend quotient, clMod 4 dividend quotient]
    --     runAll (Prime 17) program [dividend, quotient] [] expected
    --     runAll gf181 program [dividend, quotient] [] expected

    it "assertCLDivMod (quotient & remainder unknown)" $ do
      let program = do
            dividend <- input Public :: Comp (UInt 6)
            divisor <- input Public
            quotient <- freshVarUInt
            remainder <- freshVarUInt
            assertCLDivMod dividend divisor quotient remainder
            return (quotient, remainder)

      let genPair = do
            dividend <- choose (0, 15)
            divisor <- choose (1, 15)
            return (dividend, divisor)
      forAll genPair $ \(dividend, divisor) -> do
        let expected = [clDiv 4 dividend divisor, clMod 4 dividend divisor]
        runAll gf181 program [dividend, divisor] [] expected
        runAll (Prime 17) program [dividend, divisor] [] expected