{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

module Test.Compilation.UInt (tests, run) where

import Keelung hiding (compile)
import Keelung.Compiler (Error (..))
import Keelung.Compiler.Compile.Error qualified as Compiler
import Keelung.Data.U qualified as U
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
        validate (Prime 257) program [300] [] [300]

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
          validate gf181 program [if p then 1 else 0, fromIntegral x, fromIntegral y] [] expected

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
          validate gf181 (program (fromIntegral y)) [if p then 1 else 0, fromIntegral x] [] expected

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
          validate gf181 (program (fromIntegral x)) [if p then 1 else 0, fromIntegral y] [] expected

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
          validate gf181 (program (fromIntegral x :: UInt 4) (fromIntegral y)) [if p then 1 else 0] [] expected

      it "constant predicate" $ do
        let program = do
              return $ cond true (3 :: UInt 2) 2
        validate gf181 program [] [] [3]

    describe "Equalities" $ do
      it "variable / constant" $ do
        let program = do
              x <- input Public :: Comp (UInt 4)
              return (x `eq` 13)
        forAll (choose (0, 15)) $ \x -> do
          let expected = [if x == 13 then 1 else 0]
          validate gf181 program [x] [] expected
          validate (Prime 13) program [x] [] expected
          validate (Binary 7) program [x] [] expected

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
          validate gf181 program [x, y] [] expected
          validate (Prime 13) program [x, y] [] expected
          validate (Binary 7) program [x, y] [] expected

      it "neq: variable / constant" $ do
        let program = do
              x <- inputUInt @4 Public
              return (x `neq` 13)

        forAll (choose (0, 15)) $ \x -> do
          let expected = [if x == 13 then 0 else 1]
          validate (Prime 13) program [x `mod` 16] [] expected

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
          validate (Prime 13) program [x, y] [] expected

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
          validate gf181 program [x, y] [] expected

      it "neq (40 bits / Prime 13)" $ do
        let program = do
              x <- inputUInt @40 Public
              y <- inputUInt @40 Public
              return (x `neq` y)
        -- debugPrime  (Prime 13)  program
        validate (Prime 13) program [12345, 12344] [] [1]
        validate (Prime 13) program [12340000001, 12340000000] [] [1]
        validate (Prime 13) program [1234, 1234] [] [0]

      it "neq 2" $ do
        let program = do
              x <- inputUInt @4 Public
              return (x `neq` 3)
        validate gf181 program [5] [] [1]
        validate gf181 program [3] [] [0]

      it "neq 3" $ do
        let program = do
              x <- inputUInt @4 Public
              assert $ x `neq` 3
        validate gf181 program [5] [] []
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
    describe "Slice" $ do
      it "should throw exception when the starting index < 0" $ do
        let program = do
              x <- input Public :: Comp (UInt 8)
              return $ slice x (-1, 3) :: Comp (UInt 4)
        validate (Binary 7) program [0] [] [0] `shouldThrow` anyException
        validate (Prime 17) program [0] [] [0] `shouldThrow` anyException
        validate gf181 program [0] [] [0] `shouldThrow` anyException

      it "should throw exception when the ending index is smaller than the starting index" $ do
        let program = do
              x <- input Public :: Comp (UInt 8)
              return $ slice x (3, 1) :: Comp (UInt 4)
        validate (Binary 7) program [0] [] [0] `shouldThrow` anyException
        validate (Prime 17) program [0] [] [0] `shouldThrow` anyException
        validate gf181 program [0] [] [0] `shouldThrow` anyException

      it "should throw exception when the ending index is greater than the bit width" $ do
        let program = do
              x <- input Public :: Comp (UInt 8)
              return $ slice x (3, 9) :: Comp (UInt 4)
        validate (Binary 7) program [0] [] [0] `shouldThrow` anyException
        validate (Prime 17) program [0] [] [0] `shouldThrow` anyException
        validate gf181 program [0] [] [0] `shouldThrow` anyException

      it "should throw exception when the range does not match with the type" $ do
        let program = do
              x <- input Public :: Comp (UInt 8)
              return $ slice x (3, 6) :: Comp (UInt 4)
        validate (Binary 7) program [0] [] [0] `shouldThrow` anyException
        validate (Prime 17) program [0] [] [0] `shouldThrow` anyException
        validate gf181 program [0] [] [0] `shouldThrow` anyException

      it "constant (slice width = 4)" $ do
        let genParam = do
              i <- chooseInt (0, 4)
              val <- choose (0, 255)
              return (val, i)

        let program x (i, j) = do
              let u = fromInteger x :: UInt 8
              return $ slice u (i, j) :: Comp (UInt 4)
        forAll genParam $ \(val, i) -> do
          let expected = [toInteger (U.slice (U.new 8 val) (i, i + 4))]
          validate (Binary 7) (program val (i, i + 4)) [] [] expected
          validate (Prime 17) (program val (i, i + 4)) [] [] expected
          validate gf181 (program val (i, i + 4)) [] [] expected

      it "variable (slice width = 4)" $ do
        let genParam = do
              i <- chooseInt (0, 4)
              val <- choose (0, 255)
              return (val, i)

        let program (i, j) = do
              x <- input Public :: Comp (UInt 8)
              return $ slice x (i, j) :: Comp (UInt 4)
        forAll genParam $ \(val, i) -> do
          let expected = [toInteger (U.slice (U.new 8 val) (i, i + 4))]
          validate (Binary 7) (program (i, i + 4)) [val] [] expected
          validate (Prime 17) (program (i, i + 4)) [val] [] expected
          validate gf181 (program (i, i + 4)) [val] [] expected

    describe "Join" $ do
      it "constant (slice width: 4 / 4)" $ do
        let genParam = do
              x <- chooseInteger (0, 15)
              y <- chooseInteger (0, 15)
              return (x, y)

        let program x y = do
              let u = fromInteger x :: UInt 4
              let v = fromInteger y :: UInt 4
              return $ u `join` v :: Comp (UInt 8)

        forAll genParam $ \(x, y) -> do
          let expected = [toInteger (U.join (U.new 4 x) (U.new 4 y))]
          validate (Binary 7) (program x y) [] [] expected
          validate (Prime 17) (program x y) [] [] expected
          validate gf181 (program x y) [] [] expected

      it "constant (slice width: 2 / 6)" $ do
        let genParam = do
              x <- chooseInteger (0, 3)
              y <- chooseInteger (0, 63)
              return (x, y)

        let program x y = do
              let u = fromInteger x :: UInt 2
              let v = fromInteger y :: UInt 6
              return $ u `join` v :: Comp (UInt 8)

        forAll genParam $ \(x, y) -> do
          let expected = [toInteger (U.join (U.new 2 x) (U.new 6 y))]
          validate (Binary 7) (program x y) [] [] expected
          validate (Prime 17) (program x y) [] [] expected
          validate gf181 (program x y) [] [] expected

      it "variable (slice width: 2 / 6)" $ do
        let genParam = do
              x <- chooseInteger (0, 3)
              y <- chooseInteger (0, 63)
              return (x, y)

        let program = do
              u <- input Public :: Comp (UInt 2)
              v <- input Public :: Comp (UInt 6)
              return $ u `join` v :: Comp (UInt 8)

        forAll genParam $ \(x, y) -> do
          let expected = [toInteger (U.join (U.new 2 x) (U.new 6 y))]
          validate (Binary 7) program [x, y] [] expected
          validate (Prime 17) program [x, y] [] expected
          validate gf181 program [x, y] [] expected