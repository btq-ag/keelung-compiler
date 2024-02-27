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
import Test.Compilation.UInt.CLDivMod qualified as CLDivMod
import Test.Compilation.UInt.CLMul qualified as CLMul
import Test.Compilation.UInt.Comparison qualified as Comparison
import Test.Compilation.UInt.DivMod qualified as DivMod
import Test.Compilation.UInt.Equality qualified as Equality
import Test.Compilation.UInt.Inequality qualified as Inequality
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
    CLDivMod.tests
    Equality.tests
    Inequality.tests
    ModInv.tests

    Comparison.tests
    Logical.tests
    Bitwise.tests

    describe "Big Int I/O" $ do
      it "10 bit / GF257" $ do
        let program = inputUInt @10 Public
        testCompiler (Prime 257) program [300] [] [300]

    describe "Conditionals" $ do
      it "variable / variable / variable" $ do
        let program = do
              p <- input Public
              x <- input Public :: Comp (UInt 4)
              y <- input Public
              return $ cond p x y
        let genParam = do
              p <- arbitrary
              x <- chooseInt (0, 15)
              y <- chooseInt (0, 15)
              return (p, x, y)
        forAll genParam $ \(p, x, y) -> do
          let expected = [fromIntegral $ if p then x else y]
          testCompiler gf181 program [if p then 1 else 0, fromIntegral x, fromIntegral y] [] expected

      it "variable / variable / constant" $ do
        let program y = do
              p <- input Public
              x <- input Public :: Comp (UInt 4)
              return $ cond p x y
        let genParam = do
              p <- arbitrary
              x <- chooseInt (0, 15)
              y <- chooseInt (0, 15)
              return (p, x, y)
        forAll genParam $ \(p, x, y) -> do
          let expected = [fromIntegral $ if p then x else y]
          testCompiler gf181 (program (fromIntegral y)) [if p then 1 else 0, fromIntegral x] [] expected

      it "variable / constant / variable" $ do
        let program x = do
              p <- input Public
              y <- input Public :: Comp (UInt 4)
              return $ cond p x y
        let genParam = do
              p <- arbitrary
              x <- chooseInt (0, 15)
              y <- chooseInt (0, 15)
              return (p, x, y)
        forAll genParam $ \(p, x, y) -> do
          let expected = [fromIntegral $ if p then x else y]
          testCompiler gf181 (program (fromIntegral x)) [if p then 1 else 0, fromIntegral y] [] expected

      it "variable / constant / constant" $ do
        let program x y = do
              p <- input Public
              return $ cond p x y
        let genParam = do
              p <- arbitrary
              x <- chooseInt (0, 15)
              y <- chooseInt (0, 15)
              return (p, x, y)
        forAll genParam $ \(p, x, y) -> do
          let expected = [fromIntegral $ if p then x else y]
          testCompiler gf181 (program (fromIntegral x :: UInt 4) (fromIntegral y)) [if p then 1 else 0] [] expected

      it "constant predicate" $ do
        let program = do
              return $ cond true (3 :: UInt 2) 2
        testCompiler gf181 program [] [] [3]

    describe "Equalities" $ do
      it "variable / constant" $ do
        let program = do
              x <- input Public :: Comp (UInt 4)
              return (x `eq` 13)
        forAll (choose (0, 15)) $ \x -> do
          let expected = [if x == 13 then 1 else 0]
          testCompiler gf181 program [x] [] expected
          testCompiler (Prime 13) program [x] [] expected
          testCompiler (Binary 7) program [x] [] expected

      it "variables (Prime 13)" $ do
        let program = do
              x <- input Public :: Comp (UInt 4)
              y <- input Public
              return (x `eq` y)
        let genPair = do
              x <- choose (0, 15)
              y <- choose (0, 15)
              return (x, y)
        forAll genPair $ \(x, y) -> do
          let expected = [if x == y then 1 else 0]
          testCompiler gf181 program [x, y] [] expected
          testCompiler (Prime 13) program [x, y] [] expected
          testCompiler (Binary 7) program [x, y] [] expected

      it "neq: variable / constant" $ do
        let program = do
              x <- inputUInt @4 Public
              return (x `neq` 13)

        forAll (choose (0, 15)) $ \x -> do
          let expected = [if x == 13 then 0 else 1]
          testCompiler (Prime 13) program [x `mod` 16] [] expected

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
          testCompiler (Prime 13) program [x, y] [] expected

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
          testCompiler gf181 program [x, y] [] expected

      it "neq (40 bits / Prime 13)" $ do
        let program = do
              x <- inputUInt @40 Public
              y <- inputUInt @40 Public
              return (x `neq` y)
        -- debugPrime  (Prime 13)  program
        testCompiler (Prime 13) program [12345, 12344] [] [1]
        testCompiler (Prime 13) program [12340000001, 12340000000] [] [1]
        testCompiler (Prime 13) program [1234, 1234] [] [0]

      it "neq 2" $ do
        let program = do
              x <- inputUInt @4 Public
              return (x `neq` 3)
        testCompiler gf181 program [5] [] [1]
        testCompiler gf181 program [3] [] [0]

      it "neq 3" $ do
        let program = do
              x <- inputUInt @4 Public
              assert $ x `neq` 3
        testCompiler gf181 program [5] [] []
        throwErrors
          gf181
          program
          [3]
          []
          (InterpreterError $ Interpreter.AssertionError "¬ ($UI₄0 = 3)")
          (SolverError (Solver.ConflictingValues "at eliminateIfHold") :: Error GF181)

      it "neq 4" $ do
        let program = do
              assert $ 3 `neq` (3 :: UInt 4)
        throwErrors
          gf181
          program
          []
          []
          (InterpreterError $ Interpreter.AssertionError "¬ (3 = 3)")
          (CompilerError (Compiler.ConflictingValuesB True False) :: Error GF181)
