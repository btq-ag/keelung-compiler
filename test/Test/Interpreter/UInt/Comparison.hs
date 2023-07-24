{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

module Test.Interpreter.UInt.Comparison (tests, run) where

import Control.Monad
import Data.Field.Galois (Prime)
import Keelung hiding (compile)
import Keelung.Compiler.Compile.Error qualified as Compiler
import Keelung.Compiler.Error (Error (..))
import Keelung.Interpreter qualified as Interpreter
import Keelung.Solver qualified as Solver
import Test.Hspec
import Test.Interpreter.Util
import Test.QuickCheck hiding ((.&.))

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests = describe "Comparisons" $ do
  it "assertLTE on Prime 2" $ do
    let program bound = do
          x <- inputUInt @4 Public
          assertLTE x bound

    let field = Prime 2
    let width = 4
    forAll (choose (-1, 15)) $ \bound -> do
      when (bound < 0) $ do
        forM_ [0 .. 15] $ \x -> do
          throwBoth
            field
            (program bound)
            [fromInteger x]
            []
            (InterpreterError (Interpreter.AssertLTEBoundTooSmallError bound))
            (CompilerError (Compiler.AssertLTEBoundTooSmallError bound) :: Error (Prime 2))

      when (bound >= 0 && bound < 15) $ do
        forM_ [0 .. 15] $ \x -> do
          if x <= bound
            then runAll field (program bound) [fromInteger x] [] []
            else do
              throwBoth
                field
                (program bound)
                [fromInteger x]
                []
                (InterpreterError (Interpreter.AssertLTEError (fromInteger x) bound))
                (SolverError Solver.ConflictingValues :: Error (Prime 2))

      when (bound >= 15) $ do
        forM_ [0 .. 15] $ \x -> do
          throwBoth
            field
            (program bound)
            [fromInteger x]
            []
            (InterpreterError (Interpreter.AssertLTEBoundTooLargeError bound width))
            (CompilerError (Compiler.AssertLTEBoundTooLargeError bound width) :: Error (Prime 2))

  it "assertLTE on Prime 31" $ do
    let program bound = do
          x <- inputUInt @4 Public
          assertLTE x bound

    let field = Prime 31
    let width = 4
    forAll (choose (-1, 15)) $ \bound -> do
      when (bound < 0) $ do
        forM_ [0 .. 15] $ \x -> do
          throwBoth
            field
            (program bound)
            [fromInteger x]
            []
            (InterpreterError (Interpreter.AssertLTEBoundTooSmallError bound))
            (CompilerError (Compiler.AssertLTEBoundTooSmallError bound) :: Error (Prime 31))

      when (bound >= 0 && bound < 15) $ do
        forM_ [0 .. 15] $ \x -> do
          if x <= bound
            then runAll field (program bound) [fromInteger x] [] []
            else do
              throwBoth
                field
                (program bound)
                [fromInteger x]
                []
                (InterpreterError (Interpreter.AssertLTEError (fromInteger x) bound))
                (SolverError Solver.ConflictingValues :: Error (Prime 31))

      when (bound >= 15) $ do
        forM_ [0 .. 15] $ \x -> do
          throwBoth
            field
            (program bound)
            [fromInteger x]
            []
            (InterpreterError (Interpreter.AssertLTEBoundTooLargeError bound width))
            (CompilerError (Compiler.AssertLTEBoundTooLargeError bound width) :: Error (Prime 31))

  it "assertLT on Prime 2" $ do
    forAll (choose (-2, 16)) $ \bound -> do
      let width = 4

      let program = do
            x <- inputUInt @4 Public
            assertLT x bound

      when (bound < 1) $ do
        forM_ [0 .. 15] $ \x -> do
          throwBoth
            (Prime 2)
            program
            [fromInteger x]
            []
            (InterpreterError (Interpreter.AssertLTBoundTooSmallError bound))
            (CompilerError (Compiler.AssertLTBoundTooSmallError bound) :: Error GF181)

      when (bound >= 1 && bound < 16) $ do
        forM_ [0 .. 15] $ \x -> do
          if x < bound
            then runAll (Prime 2) program [fromInteger x] [] []
            else do
              throwBoth
                (Prime 2)
                program
                [fromInteger x]
                []
                (InterpreterError (Interpreter.AssertLTError (fromInteger x) bound))
                (SolverError Solver.ConflictingValues :: Error GF181)

      when (bound >= 16) $ do
        forM_ [0 .. 15] $ \x -> do
          throwBoth
            (Prime 2)
            program
            [fromInteger x]
            []
            (InterpreterError (Interpreter.AssertLTBoundTooLargeError bound width))
            (CompilerError (Compiler.AssertLTBoundTooLargeError bound width) :: Error GF181)

  it "assertGTE on Prime 2" $ do
    forAll (choose (-2, 16)) $ \bound -> do
      let width = 4

      let program = do
            x <- inputUInt @4 Public
            assertGTE x bound

      when (bound < 1) $ do
        forM_ [0 .. 15] $ \x -> do
          throwBoth
            (Prime 2)
            program
            [fromInteger x]
            []
            (InterpreterError (Interpreter.AssertGTEBoundTooSmallError bound))
            (CompilerError (Compiler.AssertGTEBoundTooSmallError bound) :: Error (Prime 2))

      when (bound >= 1 && bound < 16) $ do
        forM_ [0 .. 15] $ \x -> do
          if x >= bound
            then runAll (Prime 2) program [fromInteger x] [] []
            else do
              throwBoth
                (Prime 2)
                program
                [fromInteger x]
                []
                (InterpreterError (Interpreter.AssertGTEError (fromInteger x) bound))
                (SolverError Solver.ConflictingValues :: Error (Prime 2))

      when (bound >= 16) $ do
        forM_ [0 .. 15] $ \x -> do
          throwBoth
            (Prime 2)
            program
            [fromInteger x]
            []
            (InterpreterError (Interpreter.AssertGTEBoundTooLargeError bound width))
            (CompilerError (Compiler.AssertGTEBoundTooLargeError bound width) :: Error (Prime 2))

  it "assertGT" $ do
    forAll (choose (-2, 16)) $ \bound -> do
      let width = 4

      let program = do
            x <- inputUInt @4 Public
            assertGT x bound

      when (bound < 0) $ do
        forM_ [0 .. 15] $ \x -> do
          throwBoth
            gf181
            program
            [fromInteger x]
            []
            (InterpreterError (Interpreter.AssertGTBoundTooSmallError bound))
            (CompilerError (Compiler.AssertGTBoundTooSmallError bound) :: Error GF181)

      when (bound >= 0 && bound < 15) $ do
        forM_ [0 .. 15] $ \x -> do
          if x > bound
            then runAll gf181 program [fromInteger x] [] []
            else do
              throwBoth
                gf181
                program
                [fromInteger x]
                []
                (InterpreterError (Interpreter.AssertGTError (fromInteger x) bound))
                (SolverError Solver.ConflictingValues :: Error GF181)

      when (bound >= 15) $ do
        forM_ [0 .. 15] $ \x -> do
          throwBoth
            gf181
            program
            [fromInteger x]
            []
            (InterpreterError (Interpreter.AssertGTBoundTooLargeError bound width))
            (CompilerError (Compiler.AssertGTBoundTooLargeError bound width) :: Error GF181)

  it "lte (variable / variable)" $ do
    let genPair = (,) <$> choose (0, 15) <*> choose (0, 15)
    let program = do
          x <- inputUInt @4 Public
          y <- inputUInt @4 Public
          return $ x `lte` y

    forAll genPair $ \(x, y) -> do
      if x <= y
        then runAll (Prime 2) program [fromInteger x, fromInteger y] [] [1]
        else runAll (Prime 2) program [fromInteger x, fromInteger y] [] [0]

  it "lte (variable / constant)" $ do
    let genPair = (,) <$> choose (0, 15) <*> choose (0, 15)
    let program y = do
          x <- inputUInt @4 Public
          return $ x `lte` y

    forAll genPair $ \(x, y) -> do
      if x <= y
        then runAll (Prime 2) (program (fromInteger y)) [fromInteger x] [] [1]
        else runAll (Prime 2) (program (fromInteger y)) [fromInteger x] [] [0]

  it "lte (constant / variable)" $ do
    let genPair = (,) <$> choose (0, 15) <*> choose (0, 15)
    let program x = do
          y <- inputUInt @4 Public
          return $ x `lte` y

    forAll genPair $ \(x, y) -> do
      if x <= y
        then runAll (Prime 2) (program (fromInteger x)) [fromInteger y] [] [1]
        else runAll (Prime 2) (program (fromInteger x)) [fromInteger y] [] [0]

  it "lte (constant / constant)" $ do
    let genPair = (,) <$> choose (0, 15) <*> choose (0, 15)
    let program x y = do
          return $ x `lte` (y :: UInt 4)

    forAll genPair $ \(x, y) -> do
      if x <= y
        then runAll (Prime 2) (program (fromInteger x) (fromInteger y)) [] [] [1]
        else runAll (Prime 2) (program (fromInteger x) (fromInteger y)) [] [] [0]

  it "lt (variable / variable)" $ do
    let genPair = (,) <$> choose (0, 15) <*> choose (0, 15)
    let program = do
          x <- inputUInt @4 Public
          y <- inputUInt @4 Public
          return $ x `lt` y

    forAll genPair $ \(x, y) -> do
      if x < y
        then runAll (Prime 2) program [fromInteger x, fromInteger y] [] [1]
        else runAll (Prime 2) program [fromInteger x, fromInteger y] [] [0]

  it "lt (variable / constant)" $ do
    let genPair = (,) <$> choose (0, 15) <*> choose (0, 15)
    let program y = do
          x <- inputUInt @4 Public
          return $ x `lt` y

    forAll genPair $ \(x, y) -> do
      if x < y
        then runAll (Prime 2) (program (fromInteger y)) [fromInteger x] [] [1]
        else runAll (Prime 2) (program (fromInteger y)) [fromInteger x] [] [0]

  it "lt (constant / variable)" $ do
    let genPair = (,) <$> choose (0, 15) <*> choose (0, 15)
    let program x = do
          y <- inputUInt @4 Public
          return $ x `lt` y

    forAll genPair $ \(x, y) -> do
      if x < y
        then runAll (Prime 2) (program (fromInteger x)) [fromInteger y] [] [1]
        else runAll (Prime 2) (program (fromInteger x)) [fromInteger y] [] [0]

  it "lt (constant / constant)" $ do
    let genPair = (,) <$> choose (0, 15) <*> choose (0, 15)
    let program x y = do
          return $ x `lt` (y :: UInt 4)

    forAll genPair $ \(x, y) -> do
      if x < y
        then runAll (Prime 2) (program (fromInteger x) (fromInteger y)) [] [] [1]
        else runAll (Prime 2) (program (fromInteger x) (fromInteger y)) [] [] [0]

  it "gte (variable / variable)" $ do
    let genPair = (,) <$> choose (0, 15) <*> choose (0, 15)
    let program = do
          x <- inputUInt @4 Public
          y <- inputUInt @4 Public
          return $ x `gte` y

    forAll genPair $ \(x, y) -> do
      if x >= y
        then runAll (Prime 2) program [fromInteger x, fromInteger y] [] [1]
        else runAll (Prime 2) program [fromInteger x, fromInteger y] [] [0]

  it "gte (variable / constant)" $ do
    let genPair = (,) <$> choose (0, 15) <*> choose (0, 15)
    let program y = do
          x <- inputUInt @4 Public
          return $ x `gte` y

    forAll genPair $ \(x, y) -> do
      if x >= y
        then runAll (Prime 2) (program (fromInteger y)) [fromInteger x] [] [1]
        else runAll (Prime 2) (program (fromInteger y)) [fromInteger x] [] [0]

  it "gte (constant / variable)" $ do
    let genPair = (,) <$> choose (0, 15) <*> choose (0, 15)
    let program x = do
          y <- inputUInt @4 Public
          return $ x `gte` y

    forAll genPair $ \(x, y) -> do
      if x >= y
        then runAll (Prime 2) (program (fromInteger x)) [fromInteger y] [] [1]
        else runAll (Prime 2) (program (fromInteger x)) [fromInteger y] [] [0]

  it "gte (constant / constant)" $ do
    let genPair = (,) <$> choose (0, 15) <*> choose (0, 15)
    let program x y = do
          return $ x `gte` (y :: UInt 4)

    forAll genPair $ \(x, y) -> do
      if x >= y
        then runAll (Prime 2) (program (fromInteger x) (fromInteger y)) [] [] [1]
        else runAll (Prime 2) (program (fromInteger x) (fromInteger y)) [] [] [0]

  it "gt (variable / variable)" $ do
    let genPair = (,) <$> choose (0, 15) <*> choose (0, 15)
    let program = do
          x <- inputUInt @4 Public
          y <- inputUInt @4 Public
          return $ x `gt` y

    forAll genPair $ \(x, y) -> do
      if x > y
        then runAll (Prime 2) program [fromInteger x, fromInteger y] [] [1]
        else runAll (Prime 2) program [fromInteger x, fromInteger y] [] [0]

  it "gt (variable / constant)" $ do
    let genPair = (,) <$> choose (0, 15) <*> choose (0, 15)
    let program y = do
          x <- inputUInt @4 Public
          return $ x `gt` y

    forAll genPair $ \(x, y) -> do
      if x > y
        then runAll (Prime 2) (program (fromInteger y)) [fromInteger x] [] [1]
        else runAll (Prime 2) (program (fromInteger y)) [fromInteger x] [] [0]

  it "gt (constant / variable)" $ do
    let genPair = (,) <$> choose (0, 15) <*> choose (0, 15)
    let program x = do
          y <- inputUInt @4 Public
          return $ x `gt` y

    forAll genPair $ \(x, y) -> do
      if x > y
        then runAll (Prime 2) (program (fromInteger x)) [fromInteger y] [] [1]
        else runAll (Prime 2) (program (fromInteger x)) [fromInteger y] [] [0]

  it "gt (constant / constant)" $ do
    let genPair = (,) <$> choose (0, 15) <*> choose (0, 15)
    let program x y = do
          return $ x `gt` (y :: UInt 4)

    forAll genPair $ \(x, y) -> do
      if x > y
        then runAll (Prime 2) (program (fromInteger x) (fromInteger y)) [] [] [1]
        else runAll (Prime 2) (program (fromInteger x) (fromInteger y)) [] [] [0]
