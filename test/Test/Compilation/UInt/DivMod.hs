{-# LANGUAGE DataKinds #-}

module Test.Compilation.UInt.DivMod (tests, run) where

import Control.Monad
import Data.Field.Galois (Binary, Prime)
import Keelung hiding (compile)
import Keelung.Compiler.Compile.Error qualified as Compiler
import Keelung.Compiler.Error (Error (..))
import Keelung.Compiler.Options
import Keelung.Interpreter qualified as Interpreter
import Keelung.Solver.Monad qualified as Solver
import Test.Compilation.Util
import Test.Hspec
import Test.QuickCheck hiding ((.&.))

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests =
  describe "DivMod" $ do
    describe "performDivMod" $ do
      it "variable dividend / variable divisor" $ do
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
          forM_ [gf181, Prime 17] $ \field -> do
            testCompiler field program [dividend, divisor] [] expected
          forM_ [Binary 7] $ \field -> do
            testCompiler field program [dividend, divisor] [] expected

      it "constant dividend / variable divisor" $ do
        let program dividend = do
              divisor <- input Public :: Comp (UInt 8)
              performDivMod dividend divisor

        let genPair = do
              dividend <- choose (0, 255)
              divisor <- choose (1, 255)
              return (dividend, divisor)

        forAll genPair $ \(dividend, divisor) -> do
          let expected = [dividend `div` divisor, dividend `mod` divisor]
          forM_ [gf181, Prime 17] $ \field -> do
            testCompiler field (program (fromIntegral dividend)) [divisor] [] expected
          forM_ [Binary 7] $ \field -> do
            testCompiler field (program (fromIntegral dividend)) [divisor] [] expected

      it "variable dividend / constant divisor" $ do
        let program divisor = do
              dividend <- input Public :: Comp (UInt 8)
              performDivMod dividend divisor

        let genPair = do
              dividend <- choose (0, 255)
              divisor <- choose (1, 255)
              return (dividend, divisor)

        forAll genPair $ \(dividend, divisor) -> do
          let expected = [dividend `div` divisor, dividend `mod` divisor]
          forM_ [gf181, Prime 17] $ \field -> do
            let options = defaultOptions {optDisableTestingOnO0 = True}
            testCompilerWithOpts options field (program (fromIntegral divisor)) [dividend] [] expected
          forM_ [Binary 7] $ \field -> do
            testCompiler field (program (fromIntegral divisor)) [dividend] [] expected

      it "constant dividend / constant divisor" $ do
        let program dividend divisor = performDivMod (fromIntegral dividend) (fromIntegral divisor :: UInt 8)
        let genPair = do
              dividend <- choose (0, 255)
              divisor <- choose (1, 255)
              return (dividend, divisor)
        forAll genPair $ \(dividend, divisor) -> do
          let expected = [dividend `div` divisor, dividend `mod` divisor]
          forM_ [gf181, Prime 17] $ \field -> do
            let options = defaultOptions {optDisableTestingOnO0 = True}
            testCompilerWithOpts options field (program dividend divisor) [] [] expected
          forM_ [Binary 7] $ \field -> do
            testCompiler field (program dividend divisor) [] [] expected

      describe "statements" $ do
        it "multiple separate statements" $ do
          let program = do
                a <- input Public :: Comp (UInt 5)
                b <- input Public
                c <- input Private
                d <- input Public
                (q0, r0) <- performDivMod a b
                (q1, r1) <- performDivMod c d
                return [q0, r0, q1, r1]

          forM_ [gf181, Prime 17, Binary 7] $ \field -> do
            testCompiler field program [20, 7, 8] [21] [2, 6, 2, 5]

        it "multiple statements chained together" $ do
          let program = do
                a <- input Public :: Comp (UInt 5)
                b <- input Public
                (q0, r0) <- performDivMod a b
                (q1, r1) <- performDivMod q0 b
                return [q0, r0, q1, r1]
          forM_ [gf181, Prime 17, Binary 7] $ \field -> do
            testCompiler field program [25, 3] [] [8, 1, 2, 2]

        it "before reuse" $ do
          let program = do
                a <- input Public :: Comp (UInt 5)
                b <- input Public
                (q, _) <- performDivMod a b
                reuse q
          forM_ [gf181, Prime 17, Binary 7] $ \field -> do
            testCompiler field program [10, 4] [] [2]

        it "after reuse" $ do
          let program = do
                a <- reuse =<< input Public :: Comp (UInt 5)
                b <- input Public
                (q, r) <- performDivMod a b
                assert $ q `eq` r
          forM_ [gf181, Prime 17, Binary 7] $ \field -> do
            testCompiler field program [10, 4] [] []

        it "before assertions" $ do
          let program = do
                a <- input Public :: Comp (UInt 5)
                b <- input Public
                (q, r) <- performDivMod a b
                assert $ q `eq` r
          forM_ [gf181, Prime 17, Binary 7] $ \field -> do
            testCompiler field program [10, 4] [] []

    describe "assertDivMod" $ do
      it "quotient & remainder unknown" $ do
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
          forM_ [gf181, Prime 17, Binary 7] $ \field -> do
            testCompiler field program [dividend, divisor] [] expected

      it "divisor & remainder unknown" $ do
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
          forM_ [gf181, Prime 17, Binary 7] $ \field -> do
            testCompiler field program [dividend, quotient] [] expected

      it "dividend unknown" $ do
        let program = do
              dividend <- freshVarUInt
              divisor <- input Public :: Comp (UInt 4)
              quotient <- input Public
              remainder <- input Public
              assertDivMod dividend divisor quotient remainder
              return dividend

        let genPair = do
              dividend <- chooseInt (0, 15)
              divisor <- chooseInt (1, 15)
              return (dividend, divisor)
        forAll genPair $ \(dividend, divisor) -> do
          let quotient = dividend `div` divisor
              remainder = dividend `mod` divisor
          let expected = [toInteger dividend]
          forM_ [gf181, Prime 17, Binary 7] $ \field -> do
            testCompiler field program (map toInteger [divisor, quotient, remainder]) [] expected

      describe "errors" $ do
        it "with wrong quotient constant" $ do
          let program = assertDivMod 7 (3 :: UInt 4) 3 1
          throwBoth
            gf181
            program
            []
            []
            (InterpreterError (Interpreter.DivModQuotientError False 7 3 2 3))
            (if optUseUIntUnionFind defaultOptions
              then SolverError Solver.ConflictingValues  
              else CompilerError (Compiler.ConflictingValuesU 9 6) :: Error GF181)
          throwBoth
            (Prime 17)
            program
            []
            []
            (InterpreterError (Interpreter.DivModQuotientError False 7 3 2 3))
            (if optUseUIntUnionFind defaultOptions
              then SolverError Solver.ConflictingValues  
              else CompilerError (Compiler.ConflictingValuesU 9 2) :: Error (Prime 17))
          throwBoth
            (Binary 7)
            program
            []
            []
            (InterpreterError (Interpreter.DivModQuotientError False 7 3 2 3))
            (if optUseUIntUnionFind defaultOptions
              then SolverError Solver.ConflictingValues  
              else CompilerError (Compiler.ConflictingValuesU 9 6) :: Error (Binary 7))

        it "with wrong remainder constant" $ do
          let program = assertDivMod 7 (3 :: UInt 4) 2 0
          throwBoth
            gf181
            program
            []
            []
            (InterpreterError (Interpreter.DivModRemainderError False 7 3 1 0))
            (if optUseUIntUnionFind defaultOptions
              then SolverError Solver.ConflictingValues  
              else CompilerError (Compiler.ConflictingValuesU 6 7) :: Error GF181)
          -- (SolverError Solver.ConflictingValues :: Error GF181)
          throwBoth
            (Prime 17)
            program
            []
            []
            (InterpreterError (Interpreter.DivModRemainderError False 7 3 1 0))
            (if optUseUIntUnionFind defaultOptions
              then SolverError Solver.ConflictingValues  
              else CompilerError (Compiler.ConflictingValuesU 6 3) :: Error (Prime 17))
          throwBoth
            (Binary 7)
            program
            []
            []
            (InterpreterError (Interpreter.DivModRemainderError False 7 3 1 0))
            (if optUseUIntUnionFind defaultOptions
              then SolverError Solver.ConflictingValues  
              else CompilerError (Compiler.ConflictingValuesU 6 7) :: Error (Binary 7))

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
              gf181
              program
              [dividend, 0]
              []
              (InterpreterError Interpreter.DivModQuotientIsZeroError)
              (SolverError (Solver.QuotientIsZeroError [(4, Left 12)]) :: Error GF181)
            throwBoth
              (Prime 17)
              program
              [dividend, 0]
              []
              (InterpreterError Interpreter.DivModQuotientIsZeroError)
              (SolverError (Solver.QuotientIsZeroError [(4, Left 12)]) :: Error (Prime 17))
            throwBoth
              (Binary 7)
              program
              [dividend, 0]
              []
              (InterpreterError Interpreter.DivModQuotientIsZeroError)
              (SolverError (Solver.QuotientIsZeroError [(4, Left 12)]) :: Error (Binary 7))

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
              gf181
              program
              [0, quotient]
              []
              (InterpreterError Interpreter.DivModDividendIsZeroError)
              (SolverError (Solver.DividendIsZeroError [(4, Left 8)]) :: Error GF181)
            throwBoth
              (Prime 17)
              program
              [0, quotient]
              []
              (InterpreterError Interpreter.DivModDividendIsZeroError)
              (SolverError (Solver.DividendIsZeroError [(4, Left 8)]) :: Error (Prime 17))
            throwBoth
              (Binary 7)
              program
              [0, quotient]
              []
              (InterpreterError Interpreter.DivModDividendIsZeroError)
              (SolverError (Solver.DividendIsZeroError [(4, Left 8)]) :: Error (Binary 7))
