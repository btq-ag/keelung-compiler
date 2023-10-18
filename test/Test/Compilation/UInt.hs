{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

module Test.Compilation.UInt (tests, run) where

import Keelung hiding (compile)
import Keelung.Compiler (Error (..))
import Keelung.Compiler.Compile.Error qualified as Compiler
import Keelung.Interpreter qualified as Interpreter
import Keelung.Solver qualified as Solver
import Test.Compilation.UInt.AESMul qualified as AESMul
import Test.Compilation.UInt.Addition qualified as Addition
import Test.Compilation.UInt.Bitwise qualified as Bitwise
import Test.Compilation.UInt.CLMul qualified as CLMul
import Test.Compilation.UInt.Comparison qualified as Comparison
import Test.Compilation.UInt.DivMod qualified as DivMod
import Test.Compilation.UInt.Logical qualified as Logical
import Test.Compilation.UInt.ModInv qualified as ModInv
import Test.Compilation.UInt.Multiplication qualified as Multiplication
import Test.Compilation.Util
import Test.Hspec
import Test.QuickCheck hiding ((.&.))

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests = do
  describe "Unsigned Integers" $ do
    Addition.tests
    Multiplication.tests
    CLMul.tests
    AESMul.tests

    DivMod.tests
    ModInv.tests

    Comparison.tests
    Logical.tests
    Bitwise.tests

    describe "Big Int I/O" $ do
      it "10 bit / GF257" $ do
        let program = inputUInt @10 Public
        runAll (Prime 257) program [300] [] [300]

    describe "Conditionals" $ do
      it "with inputs" $ do
        let program = do
              x <- input Public :: Comp (UInt 4)
              y <- input Public
              return $ cond true x y
        runAll gf181 program [5, 6] [] [5]

      it "with literals" $ do
        let program = do
              return $ cond true (3 :: UInt 2) 2
        runAll gf181 program [] [] [3]

    describe "Equalities" $ do
      it "eq: variable / constant" $ do
        let program = do
              x <- inputUInt @4 Public
              return (x `eq` 13)
        forAll (choose (0, 15)) $ \x -> do
          let expected = [if x == 13 then 1 else 0]
          runAll (Prime 13) program [x `mod` 16] [] expected

      it "eq: variables (Prime 13)" $ do
        let program = do
              x <- inputUInt @4 Public
              y <- inputUInt @4 Public
              return (x `eq` y)
        let genPair = do
              x <- choose (0, 15)
              y <- choose (0, 15)
              return (x, y)
        forAll genPair $ \(x, y) -> do
          let expected = [if x == y then 1 else 0]
          runAll (Prime 13) program [x, y] [] expected

      it "eq: variables (GF181)" $ do
        let program = do
              x <- inputUInt @4 Public
              y <- inputUInt @4 Public
              return (x `eq` y)
        let genPair = do
              x <- choose (0, 15)
              y <- choose (0, 15)
              return (x, y)
        forAll genPair $ \(x, y) -> do
          let expected = [if x == y then 1 else 0]
          runAll gf181 program [x, y] [] expected

      it "neq: variable / constant" $ do
        let program = do
              x <- inputUInt @4 Public
              return (x `neq` 13)

        -- runAll (Prime 13) program [0] [] [0]
        -- runAll (Prime 13) program [4, 4] [] [1]
        forAll (choose (0, 15)) $ \x -> do
          let expected = [if x == 13 then 0 else 1]
          runAll (Prime 13) program [x `mod` 16] [] expected

      it "neq: variables (Prime 13)" $ do
        let program = do
              x <- inputUInt @4 Public
              y <- inputUInt @4 Public
              return (x `eq` y)
        let genPair = do
              x <- choose (0, 15)
              y <- choose (0, 15)
              return (x, y)
        forAll genPair $ \(x, y) -> do
          let expected = [if x /= y then 0 else 1]
          runAll (Prime 13) program [x, y] [] expected

      it "neq: variables (GF181)" $ do
        let program = do
              x <- inputUInt @4 Public
              y <- inputUInt @4 Public
              return (x `eq` y)
        let genPair = do
              x <- choose (0, 15)
              y <- choose (0, 15)
              return (x, y)
        forAll genPair $ \(x, y) -> do
          let expected = [if x /= y then 0 else 1]
          runAll gf181 program [x, y] [] expected

      it "neq (40 bits / Prime 13)" $ do
        let program = do
              x <- inputUInt @40 Public
              y <- inputUInt @40 Public
              return (x `neq` y)
        -- debugPrime  (Prime 13)  program
        runAll (Prime 13) program [12345, 12344] [] [1]
        runAll (Prime 13) program [12340000001, 12340000000] [] [1]
        runAll (Prime 13) program [1234, 1234] [] [0]

      it "neq 2" $ do
        let program = do
              x <- inputUInt @4 Public
              return (x `neq` 3)
        runAll gf181 program [5] [] [1]
        runAll gf181 program [3] [] [0]

      it "neq 3" $ do
        let program = do
              x <- inputUInt @4 Public
              assert $ x `neq` 3
        runAll gf181 program [5] [] []
        throwBoth
          gf181
          program
          [3]
          []
          (InterpreterError $ Interpreter.AssertionError "¬ ($UI₄0 = 3)")
          (SolverError Solver.ConflictingValues :: Error GF181)

      it "neq 4" $ do
        let program = do
              assert $ 3 `neq` (3 :: UInt 4)
        throwBoth
          gf181
          program
          []
          []
          (InterpreterError $ Interpreter.AssertionError "¬ (3 = 3)")
          (CompilerError (Compiler.ConflictingValuesB True False) :: Error GF181)
