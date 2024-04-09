{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Compilation.UInt.Comparison (tests, run) where

import Control.Monad
import Data.Field.Galois (Binary, Prime)
import Data.Word (Word8)
import Keelung hiding (compile)
import Keelung.Compiler.Compile.Error qualified as Compiler
import Keelung.Compiler.Error (Error (..))
import Keelung.Interpreter qualified as Interpreter
import Keelung.Solver qualified as Solver
import Test.Compilation.Util
import Test.Hspec
import Test.QuickCheck

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests = describe "Comparisons" $ do
  describe "assertLTE" $ do
    let program bound = do
          x <- input Public :: Comp (UInt 4)
          assertLTE x bound
    let width = 4

    describe "bound too small" $ do
      let bound = -1
      let x = 1
      it "GF181" $ do
        throwErrors
          gf181
          (program bound)
          [fromInteger x]
          []
          (InterpreterError (Interpreter.AssertLTEBoundTooSmallError bound))
          (CompilerError (Compiler.AssertLTEBoundTooSmallError bound) :: Error GF181)
      it "Prime 2" $ do
        throwErrors
          (Prime 2)
          (program bound)
          [fromInteger x]
          []
          (InterpreterError (Interpreter.AssertLTEBoundTooSmallError bound))
          (CompilerError (Compiler.AssertLTEBoundTooSmallError bound) :: Error (Prime 2))
      it "Binary 7" $ do
        throwErrors
          (Binary 7)
          (program bound)
          [fromInteger x]
          []
          (InterpreterError (Interpreter.AssertLTEBoundTooSmallError bound))
          (CompilerError (Compiler.AssertLTEBoundTooSmallError bound) :: Error (Binary 7))

    describe "bound too large" $ do
      let bound = 15
      let x = 1
      it "GF181" $ do
        throwErrors
          gf181
          (program bound)
          [fromInteger x]
          []
          (InterpreterError (Interpreter.AssertLTEBoundTooLargeError bound width))
          (CompilerError (Compiler.AssertLTEBoundTooLargeError bound width) :: Error GF181)
      it "Prime 2" $ do
        throwErrors
          (Prime 2)
          (program bound)
          [fromInteger x]
          []
          (InterpreterError (Interpreter.AssertLTEBoundTooLargeError bound width))
          (CompilerError (Compiler.AssertLTEBoundTooLargeError bound width) :: Error (Prime 2))
      it "Binary 7" $ do
        throwErrors
          (Binary 7)
          (program bound)
          [fromInteger x]
          []
          (InterpreterError (Interpreter.AssertLTEBoundTooLargeError bound width))
          (CompilerError (Compiler.AssertLTEBoundTooLargeError bound width) :: Error (Binary 7))

    describe "bound normal" $ do
      it "GF181" $ do
        forAll (choose (0, 14)) $ \bound -> do
          forM_ [0 .. 15] $ \x -> do
            if x <= bound
              then validate gf181 (program bound) [fromInteger x] [] []
              else
                throwErrors
                  gf181
                  (program bound)
                  [fromInteger x]
                  []
                  (InterpreterError (Interpreter.AssertLTEError (fromInteger x) bound))
                  (SolverError (Solver.ConflictingValues "at eliminateIfHold") :: Error GF181)
      it "Prime 2" $ do
        forAll (choose (0, 14)) $ \bound -> do
          forM_ [0 .. 15] $ \x -> do
            if x <= bound
              then validate (Prime 2) (program bound) [fromInteger x] [] []
              else
                throwErrors
                  (Prime 2)
                  (program bound)
                  [fromInteger x]
                  []
                  (InterpreterError (Interpreter.AssertLTEError (fromInteger x) bound))
                  (SolverError (Solver.ConflictingValues "at eliminateIfHold") :: Error (Prime 2))
      it "Binary 7" $ do
        forAll (choose (0, 14)) $ \bound -> do
          forM_ [0 .. 15] $ \x -> do
            if x <= bound
              then validate (Binary 7) (program bound) [fromInteger x] [] []
              else
                throwErrors
                  (Binary 7)
                  (program bound)
                  [fromInteger x]
                  []
                  (InterpreterError (Interpreter.AssertLTEError (fromInteger x) bound))
                  (SolverError (Solver.ConflictingValues "at eliminateIfHold") :: Error (Binary 7))

  describe "assertLT" $ do
    let program bound = do
          x <- input Public :: Comp (UInt 4)
          assertLT x bound
    let width = 4
    describe "bound too small" $ do
      let bound = 0
      let x = 1
      it "GF181" $ do
        throwErrors
          gf181
          (program bound)
          [fromInteger x]
          []
          (InterpreterError (Interpreter.AssertLTBoundTooSmallError bound))
          (CompilerError (Compiler.AssertLTBoundTooSmallError bound) :: Error GF181)
      it "Prime 2" $ do
        throwErrors
          (Prime 2)
          (program bound)
          [fromInteger x]
          []
          (InterpreterError (Interpreter.AssertLTBoundTooSmallError bound))
          (CompilerError (Compiler.AssertLTBoundTooSmallError bound) :: Error (Prime 2))
      it "Binary 7" $ do
        throwErrors
          (Binary 7)
          (program bound)
          [fromInteger x]
          []
          (InterpreterError (Interpreter.AssertLTBoundTooSmallError bound))
          (CompilerError (Compiler.AssertLTBoundTooSmallError bound) :: Error (Binary 7))

    describe "bound too large" $ do
      let bound = 16
      let x = 1
      it "GF181" $ do
        throwErrors
          gf181
          (program bound)
          [fromInteger x]
          []
          (InterpreterError (Interpreter.AssertLTBoundTooLargeError bound width))
          (CompilerError (Compiler.AssertLTBoundTooLargeError bound width) :: Error GF181)
      it "Prime 2" $ do
        throwErrors
          (Prime 2)
          (program bound)
          [fromInteger x]
          []
          (InterpreterError (Interpreter.AssertLTBoundTooLargeError bound width))
          (CompilerError (Compiler.AssertLTBoundTooLargeError bound width) :: Error (Prime 2))
      it "Binary 7" $ do
        throwErrors
          (Binary 7)
          (program bound)
          [fromInteger x]
          []
          (InterpreterError (Interpreter.AssertLTBoundTooLargeError bound width))
          (CompilerError (Compiler.AssertLTBoundTooLargeError bound width) :: Error (Binary 7))

    describe "bound normal" $ do
      it "GF181" $ do
        forAll (choose (1, 15)) $ \bound -> do
          forM_ [0 .. 15] $ \x -> do
            if x < bound
              then validate gf181 (program bound) [fromInteger x] [] []
              else
                throwErrors
                  gf181
                  (program bound)
                  [fromInteger x]
                  []
                  (InterpreterError (Interpreter.AssertLTError (fromInteger x) bound))
                  (SolverError (Solver.ConflictingValues "at eliminateIfHold") :: Error GF181)
      it "Prime 2" $ do
        forAll (choose (1, 15)) $ \bound -> do
          forM_ [0 .. 15] $ \x -> do
            if x < bound
              then validate (Prime 2) (program bound) [fromInteger x] [] []
              else
                throwErrors
                  (Prime 2)
                  (program bound)
                  [fromInteger x]
                  []
                  (InterpreterError (Interpreter.AssertLTError (fromInteger x) bound))
                  (SolverError (Solver.ConflictingValues "at eliminateIfHold") :: Error (Prime 2))
      it "Binary 7" $ do
        forAll (choose (1, 15)) $ \bound -> do
          forM_ [0 .. 15] $ \x -> do
            if x < bound
              then validate (Binary 7) (program bound) [fromInteger x] [] []
              else
                throwErrors
                  (Binary 7)
                  (program bound)
                  [fromInteger x]
                  []
                  (InterpreterError (Interpreter.AssertLTError (fromInteger x) bound))
                  (SolverError (Solver.ConflictingValues "at eliminateIfHold") :: Error (Binary 7))

  describe "assertGTE" $ do
    let program bound = do
          x <- input Public :: Comp (UInt 4)
          assertGTE x bound
    let width = 4
    describe "bound too small" $ do
      let bound = 0
      let x = 1
      it "GF181" $ do
        throwErrors
          gf181
          (program bound)
          [fromInteger x]
          []
          (InterpreterError (Interpreter.AssertGTEBoundTooSmallError bound))
          (CompilerError (Compiler.AssertGTEBoundTooSmallError bound) :: Error GF181)
      it "Prime 2" $ do
        throwErrors
          (Prime 2)
          (program bound)
          [fromInteger x]
          []
          (InterpreterError (Interpreter.AssertGTEBoundTooSmallError bound))
          (CompilerError (Compiler.AssertGTEBoundTooSmallError bound) :: Error (Prime 2))
      it "Binary 7" $ do
        throwErrors
          (Binary 7)
          (program bound)
          [fromInteger x]
          []
          (InterpreterError (Interpreter.AssertGTEBoundTooSmallError bound))
          (CompilerError (Compiler.AssertGTEBoundTooSmallError bound) :: Error (Binary 7))

    describe "bound too large" $ do
      let bound = 16
      let x = 1
      it "GF181" $ do
        throwErrors
          gf181
          (program bound)
          [fromInteger x]
          []
          (InterpreterError (Interpreter.AssertGTEBoundTooLargeError bound width))
          (CompilerError (Compiler.AssertGTEBoundTooLargeError bound width) :: Error GF181)
      it "Prime 2" $ do
        throwErrors
          (Prime 2)
          (program bound)
          [fromInteger x]
          []
          (InterpreterError (Interpreter.AssertGTEBoundTooLargeError bound width))
          (CompilerError (Compiler.AssertGTEBoundTooLargeError bound width) :: Error (Prime 2))
      it "Binary 7" $ do
        throwErrors
          (Binary 7)
          (program bound)
          [fromInteger x]
          []
          (InterpreterError (Interpreter.AssertGTEBoundTooLargeError bound width))
          (CompilerError (Compiler.AssertGTEBoundTooLargeError bound width) :: Error (Binary 7))

    describe "bound normal" $ do
      it "GF181" $ do
        forAll (choose (1, 15)) $ \bound -> do
          forM_ [0 .. 15] $ \x -> do
            if x >= bound
              then validate gf181 (program bound) [fromInteger x] [] []
              else
                throwErrors
                  gf181
                  (program bound)
                  [fromInteger x]
                  []
                  (InterpreterError (Interpreter.AssertGTEError (fromInteger x) bound))
                  (SolverError (Solver.ConflictingValues "at eliminateIfHold") :: Error GF181)
      it "Prime 2" $ do
        forAll (choose (1, 15)) $ \bound -> do
          forM_ [0 .. 15] $ \x -> do
            if x >= bound
              then validate (Prime 2) (program bound) [fromInteger x] [] []
              else
                throwErrors
                  (Prime 2)
                  (program bound)
                  [fromInteger x]
                  []
                  (InterpreterError (Interpreter.AssertGTEError (fromInteger x) bound))
                  (SolverError (Solver.ConflictingValues "at eliminateIfHold") :: Error (Prime 2))
      it "Binary 7" $ do
        forAll (choose (1, 15)) $ \bound -> do
          forM_ [0 .. 15] $ \x -> do
            if x >= bound
              then validate (Binary 7) (program bound) [fromInteger x] [] []
              else
                throwErrors
                  (Binary 7)
                  (program bound)
                  [fromInteger x]
                  []
                  (InterpreterError (Interpreter.AssertGTEError (fromInteger x) bound))
                  (SolverError (Solver.ConflictingValues "at eliminateIfHold") :: Error (Binary 7))

  describe "assertGT" $ do
    let program bound = do
          x <- input Public :: Comp (UInt 4)
          assertGT x bound
    let width = 4
    describe "bound too small" $ do
      let bound = -1
      let x = 1
      it "GF181" $ do
        throwErrors
          gf181
          (program bound)
          [fromInteger x]
          []
          (InterpreterError (Interpreter.AssertGTBoundTooSmallError bound))
          (CompilerError (Compiler.AssertGTBoundTooSmallError bound) :: Error GF181)
      it "Prime 2" $ do
        throwErrors
          (Prime 2)
          (program bound)
          [fromInteger x]
          []
          (InterpreterError (Interpreter.AssertGTBoundTooSmallError bound))
          (CompilerError (Compiler.AssertGTBoundTooSmallError bound) :: Error (Prime 2))
      it "Binary 7" $ do
        throwErrors
          (Binary 7)
          (program bound)
          [fromInteger x]
          []
          (InterpreterError (Interpreter.AssertGTBoundTooSmallError bound))
          (CompilerError (Compiler.AssertGTBoundTooSmallError bound) :: Error (Binary 7))

    describe "bound too large" $ do
      let bound = 15
      let x = 1
      it "GF181" $ do
        throwErrors
          gf181
          (program bound)
          [fromInteger x]
          []
          (InterpreterError (Interpreter.AssertGTBoundTooLargeError bound width))
          (CompilerError (Compiler.AssertGTBoundTooLargeError bound width) :: Error GF181)
      it "Prime 2" $ do
        throwErrors
          (Prime 2)
          (program bound)
          [fromInteger x]
          []
          (InterpreterError (Interpreter.AssertGTBoundTooLargeError bound width))
          (CompilerError (Compiler.AssertGTBoundTooLargeError bound width) :: Error (Prime 2))
      it "Binary 7" $ do
        throwErrors
          (Binary 7)
          (program bound)
          [fromInteger x]
          []
          (InterpreterError (Interpreter.AssertGTBoundTooLargeError bound width))
          (CompilerError (Compiler.AssertGTBoundTooLargeError bound width) :: Error (Binary 7))

    describe "bound normal" $ do
      it "GF181" $ do
        forAll (choose (0, 14)) $ \bound -> do
          forM_ [0 .. 15] $ \x -> do
            if x > bound
              then validate gf181 (program bound) [fromInteger x] [] []
              else
                throwErrors
                  gf181
                  (program bound)
                  [fromInteger x]
                  []
                  (InterpreterError (Interpreter.AssertGTError (fromInteger x) bound))
                  (SolverError (Solver.ConflictingValues "at eliminateIfHold") :: Error GF181)
      it "Prime 2" $ do
        forAll (choose (0, 14)) $ \bound -> do
          forM_ [0 .. 15] $ \x -> do
            if x > bound
              then validate (Prime 2) (program bound) [fromInteger x] [] []
              else
                throwErrors
                  (Prime 2)
                  (program bound)
                  [fromInteger x]
                  []
                  (InterpreterError (Interpreter.AssertGTError (fromInteger x) bound))
                  (SolverError (Solver.ConflictingValues "at eliminateIfHold") :: Error (Prime 2))
      it "Binary 7" $ do
        forAll (choose (0, 14)) $ \bound -> do
          forM_ [0 .. 15] $ \x -> do
            if x > bound
              then validate (Binary 7) (program bound) [fromInteger x] [] []
              else
                throwErrors
                  (Binary 7)
                  (program bound)
                  [fromInteger x]
                  []
                  (InterpreterError (Interpreter.AssertGTError (fromInteger x) bound))
                  (SolverError (Solver.ConflictingValues "at eliminateIfHold") :: Error (Binary 7))

  describe "computeLTE" $ do
    it "2 variables" $ do
      let program = do
            x <- input Public :: Comp (UInt 8)
            y <- input Public
            return $ x `lte` y

      property $ \(x, y :: Word8) -> do
        forM_ [gf181, Prime 2, Binary 7] $ \field -> do
          if x <= y
            then validate field program [fromIntegral x, fromIntegral y] [] [1]
            else validate field program [fromIntegral x, fromIntegral y] [] [0]

    it "variable + constant" $ do
      let program x = do
            y <- input Public :: Comp (UInt 8)
            return $ x `lte` y

      property $ \(x, y :: Word8) -> do
        forM_ [gf181, Prime 2, Binary 7] $ \field -> do
          if x <= y
            then validate field (program (fromIntegral x)) [fromIntegral y] [] [1]
            else validate field (program (fromIntegral x)) [fromIntegral y] [] [0]

    it "2 constants" $ do
      let program x y = do
            return $ x `lte` (y :: UInt 8)

      property $ \(x, y :: Word8) -> do
        forM_ [gf181, Prime 2, Binary 7] $ \field -> do
          if x <= y
            then validate field (program (fromIntegral x) (fromIntegral y)) [] [] [1]
            else validate field (program (fromIntegral x) (fromIntegral y)) [] [] [0]

  describe "computeLT" $ do
    it "2 variables" $ do
      let program = do
            x <- input Public :: Comp (UInt 8)
            y <- input Public
            return $ x `lt` y

      property $ \(x, y :: Word8) -> do
        forM_ [gf181, Prime 2, Binary 7] $ \field -> do
          if x < y
            then validate field program [fromIntegral x, fromIntegral y] [] [1]
            else validate field program [fromIntegral x, fromIntegral y] [] [0]

    it "variable + constant" $ do
      let program x = do
            y <- input Public :: Comp (UInt 8)
            return $ x `lt` y

      property $ \(x, y :: Word8) -> do
        forM_ [gf181, Prime 2, Binary 7] $ \field -> do
          if x < y
            then validate field (program (fromIntegral x)) [fromIntegral y] [] [1]
            else validate field (program (fromIntegral x)) [fromIntegral y] [] [0]

    it "2 constants" $ do
      let program x y = do
            return $ x `lt` (y :: UInt 8)

      property $ \(x, y :: Word8) -> do
        forM_ [gf181, Prime 2, Binary 7] $ \field -> do
          if x < y
            then validate field (program (fromIntegral x) (fromIntegral y)) [] [] [1]
            else validate field (program (fromIntegral x) (fromIntegral y)) [] [] [0]
