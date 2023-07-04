{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

module Test.Interpreter.UInt.Comparison (tests, run) where

import Control.Monad
import Keelung hiding (compile)
import Keelung.Compiler.Compile.Error qualified as Compiler
import Keelung.Compiler.Error (Error (..))
import Keelung.Interpreter.Error qualified as Interpreter
import Keelung.Interpreter.R1CS qualified as R1CS
import Keelung.Interpreter.SyntaxTree qualified as SyntaxTree
import Test.Hspec
import Test.Interpreter.Util
import Test.QuickCheck hiding ((.&.))

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests = describe "Comparisons" $ do
  it "assertLTE" $ do
    forAll (choose (-2, 16)) $ \bound -> do
      let width = 4

      let program = do
            x <- inputUInt @4 Public
            assertLTE x bound

      when (bound < 0) $ do
        forM_ [0 .. 15] $ \x -> do
          throwBoth
            (Prime 13)
            program
            [fromInteger x]
            []
            (Interpreter.SyntaxTreeError (SyntaxTree.AssertLTEBoundTooSmallError bound))
            (CompileError (Compiler.AssertLTEBoundTooSmallError bound) :: Error GF181)

      when (bound >= 0 && bound < 15) $ do
        forM_ [0 .. 15] $ \x -> do
          if x <= bound
            then runAll gf181 program [fromInteger x] [] []
            else do
              throwBoth
                (Prime 13)
                program
                [fromInteger x]
                []
                (Interpreter.SyntaxTreeError (SyntaxTree.AssertLTEError (fromInteger x) bound))
                (InterpretError (Interpreter.R1CSError R1CS.ConflictingValues) :: Error GF181)

      when (bound >= 15) $ do
        forM_ [0 .. 15] $ \x -> do
          throwBoth
            (Prime 13)
            program
            [fromInteger x]
            []
            (Interpreter.SyntaxTreeError (SyntaxTree.AssertLTEBoundTooLargeError bound width))
            (CompileError (Compiler.AssertLTEBoundTooLargeError bound width) :: Error GF181)

  it "assertLT" $ do
    -- `bound` ranges from `-50` to `50`
    forAll (choose (-50, 50)) $ \bound -> do
      let width = 4

      let program = do
            x <- inputUInt @4 Public
            assertLT x bound

      when (bound < 1) $ do
        forM_ [0 .. 15] $ \x -> do
          throwAll
            gf181Info
            program
            [fromInteger x]
            []
            (Interpreter.SyntaxTreeError (SyntaxTree.AssertLTBoundTooSmallError bound))
            (CompileError (Compiler.AssertLTBoundTooSmallError bound) :: Error GF181)

      when (bound >= 1 && bound < 16) $ do
        forM_ [0 .. 15] $ \x -> do
          if x < bound
            then runAll gf181 program [fromInteger x] [] []
            else do
              throwAll
                gf181Info
                program
                [fromInteger x]
                []
                (Interpreter.SyntaxTreeError (SyntaxTree.AssertLTError (fromInteger x) bound))
                (InterpretError (Interpreter.R1CSError R1CS.ConflictingValues) :: Error GF181)

      when (bound >= 16) $ do
        forM_ [0 .. 15] $ \x -> do
          throwAll
            gf181Info
            program
            [fromInteger x]
            []
            (Interpreter.SyntaxTreeError (SyntaxTree.AssertLTBoundTooLargeError bound width))
            (CompileError (Compiler.AssertLTBoundTooLargeError bound width) :: Error GF181)

  it "assertGTE" $ do
    -- `bound` ranges from `-50` to `50`
    forAll (choose (-50, 50)) $ \bound -> do
      let width = 4

      let program = do
            x <- inputUInt @4 Public
            assertGTE x bound

      when (bound < 1) $ do
        forM_ [0 .. 15] $ \x -> do
          throwAll
            gf181Info
            program
            [fromInteger x]
            []
            (Interpreter.SyntaxTreeError (SyntaxTree.AssertGTEBoundTooSmallError bound))
            (CompileError (Compiler.AssertGTEBoundTooSmallError bound) :: Error GF181)

      when (bound >= 1 && bound < 16) $ do
        forM_ [0 .. 15] $ \x -> do
          if x >= bound
            then runAll gf181 program [fromInteger x] [] []
            else do
              throwAll
                gf181Info
                program
                [fromInteger x]
                []
                (Interpreter.SyntaxTreeError (SyntaxTree.AssertGTEError (fromInteger x) bound))
                (InterpretError (Interpreter.R1CSError R1CS.ConflictingValues) :: Error GF181)

      when (bound >= 16) $ do
        forM_ [0 .. 15] $ \x -> do
          throwAll
            gf181Info
            program
            [fromInteger x]
            []
            (Interpreter.SyntaxTreeError (SyntaxTree.AssertGTEBoundTooLargeError bound width))
            (CompileError (Compiler.AssertGTEBoundTooLargeError bound width) :: Error GF181)

  it "assertGT" $ do
    -- `bound` ranges from `-50` to `50`
    forAll (choose (-50, 50)) $ \bound -> do
      let width = 4

      let program = do
            x <- inputUInt @4 Public
            assertGT x bound

      when (bound < 0) $ do
        forM_ [0 .. 15] $ \x -> do
          throwAll
            gf181Info
            program
            [fromInteger x]
            []
            (Interpreter.SyntaxTreeError (SyntaxTree.AssertGTBoundTooSmallError bound))
            (CompileError (Compiler.AssertGTBoundTooSmallError bound) :: Error GF181)

      when (bound >= 0 && bound < 15) $ do
        forM_ [0 .. 15] $ \x -> do
          if x > bound
            then runAll gf181 program [fromInteger x] [] []
            else do
              throwAll
                gf181Info
                program
                [fromInteger x]
                []
                (Interpreter.SyntaxTreeError (SyntaxTree.AssertGTError (fromInteger x) bound))
                (InterpretError (Interpreter.R1CSError R1CS.ConflictingValues) :: Error GF181)

      when (bound >= 15) $ do
        forM_ [0 .. 15] $ \x -> do
          throwAll
            gf181Info
            program
            [fromInteger x]
            []
            (Interpreter.SyntaxTreeError (SyntaxTree.AssertGTBoundTooLargeError bound width))
            (CompileError (Compiler.AssertGTBoundTooLargeError bound width) :: Error GF181)

  it "lte (variable / variable)" $ do
    let genPair = (,) <$> choose (0, 15) <*> choose (0, 15)
    let program = do
          x <- inputUInt @4 Public
          y <- inputUInt @4 Public
          return $ x `lte` y

    forAll genPair $ \(x, y) -> do
      if x <= y
        then runAll gf181 program [fromInteger x, fromInteger y] [] [1]
        else runAll gf181 program [fromInteger x, fromInteger y] [] [0]

  it "lte (variable / constant)" $ do
    let genPair = (,) <$> choose (0, 15) <*> choose (0, 15)
    let program y = do
          x <- inputUInt @4 Public
          return $ x `lte` y

    forAll genPair $ \(x, y) -> do
      if x <= y
        then runAll gf181 (program (fromInteger y)) [fromInteger x] [] [1]
        else runAll gf181 (program (fromInteger y)) [fromInteger x] [] [0]

  it "lte (constant / variable)" $ do
    let genPair = (,) <$> choose (0, 15) <*> choose (0, 15)
    let program x = do
          y <- inputUInt @4 Public
          return $ x `lte` y

    forAll genPair $ \(x, y) -> do
      if x <= y
        then runAll gf181 (program (fromInteger x)) [fromInteger y] [] [1]
        else runAll gf181 (program (fromInteger x)) [fromInteger y] [] [0]

  it "lte (constant / constant)" $ do
    let genPair = (,) <$> choose (0, 15) <*> choose (0, 15)
    let program x y = do
          return $ x `lte` (y :: UInt 4)

    forAll genPair $ \(x, y) -> do
      if x <= y
        then runAll gf181 (program (fromInteger x) (fromInteger y)) [] [] [1]
        else runAll gf181 (program (fromInteger x) (fromInteger y)) [] [] [0]

  it "lt (variable / variable)" $ do
    let genPair = (,) <$> choose (0, 15) <*> choose (0, 15)
    let program = do
          x <- inputUInt @4 Public
          y <- inputUInt @4 Public
          return $ x `lt` y

    forAll genPair $ \(x, y) -> do
      if x < y
        then runAll gf181 program [fromInteger x, fromInteger y] [] [1]
        else runAll gf181 program [fromInteger x, fromInteger y] [] [0]

  it "lt (variable / constant)" $ do
    let genPair = (,) <$> choose (0, 15) <*> choose (0, 15)
    let program y = do
          x <- inputUInt @4 Public
          return $ x `lt` y

    forAll genPair $ \(x, y) -> do
      if x < y
        then runAll gf181 (program (fromInteger y)) [fromInteger x] [] [1]
        else runAll gf181 (program (fromInteger y)) [fromInteger x] [] [0]

  it "lt (constant / variable)" $ do
    let genPair = (,) <$> choose (0, 15) <*> choose (0, 15)
    let program x = do
          y <- inputUInt @4 Public
          return $ x `lt` y

    forAll genPair $ \(x, y) -> do
      if x < y
        then runAll gf181 (program (fromInteger x)) [fromInteger y] [] [1]
        else runAll gf181 (program (fromInteger x)) [fromInteger y] [] [0]

  it "lt (constant / constant)" $ do
    let genPair = (,) <$> choose (0, 15) <*> choose (0, 15)
    let program x y = do
          return $ x `lt` (y :: UInt 4)

    forAll genPair $ \(x, y) -> do
      if x < y
        then runAll gf181 (program (fromInteger x) (fromInteger y)) [] [] [1]
        else runAll gf181 (program (fromInteger x) (fromInteger y)) [] [] [0]

  it "gte (variable / variable)" $ do
    let genPair = (,) <$> choose (0, 15) <*> choose (0, 15)
    let program = do
          x <- inputUInt @4 Public
          y <- inputUInt @4 Public
          return $ x `gte` y

    forAll genPair $ \(x, y) -> do
      if x >= y
        then runAll gf181 program [fromInteger x, fromInteger y] [] [1]
        else runAll gf181 program [fromInteger x, fromInteger y] [] [0]

  it "gte (variable / constant)" $ do
    let genPair = (,) <$> choose (0, 15) <*> choose (0, 15)
    let program y = do
          x <- inputUInt @4 Public
          return $ x `gte` y

    forAll genPair $ \(x, y) -> do
      if x >= y
        then runAll gf181 (program (fromInteger y)) [fromInteger x] [] [1]
        else runAll gf181 (program (fromInteger y)) [fromInteger x] [] [0]

  it "gte (constant / variable)" $ do
    let genPair = (,) <$> choose (0, 15) <*> choose (0, 15)
    let program x = do
          y <- inputUInt @4 Public
          return $ x `gte` y

    forAll genPair $ \(x, y) -> do
      if x >= y
        then runAll gf181 (program (fromInteger x)) [fromInteger y] [] [1]
        else runAll gf181 (program (fromInteger x)) [fromInteger y] [] [0]

  it "gte (constant / constant)" $ do
    let genPair = (,) <$> choose (0, 15) <*> choose (0, 15)
    let program x y = do
          return $ x `gte` (y :: UInt 4)

    forAll genPair $ \(x, y) -> do
      if x >= y
        then runAll gf181 (program (fromInteger x) (fromInteger y)) [] [] [1]
        else runAll gf181 (program (fromInteger x) (fromInteger y)) [] [] [0]

  it "gt (variable / variable)" $ do
    let genPair = (,) <$> choose (0, 15) <*> choose (0, 15)
    let program = do
          x <- inputUInt @4 Public
          y <- inputUInt @4 Public
          return $ x `gt` y

    forAll genPair $ \(x, y) -> do
      if x > y
        then runAll gf181 program [fromInteger x, fromInteger y] [] [1]
        else runAll gf181 program [fromInteger x, fromInteger y] [] [0]

  it "gt (variable / constant)" $ do
    let genPair = (,) <$> choose (0, 15) <*> choose (0, 15)
    let program y = do
          x <- inputUInt @4 Public
          return $ x `gt` y

    forAll genPair $ \(x, y) -> do
      if x > y
        then runAll gf181 (program (fromInteger y)) [fromInteger x] [] [1]
        else runAll gf181 (program (fromInteger y)) [fromInteger x] [] [0]

  it "gt (constant / variable)" $ do
    let genPair = (,) <$> choose (0, 15) <*> choose (0, 15)
    let program x = do
          y <- inputUInt @4 Public
          return $ x `gt` y

    forAll genPair $ \(x, y) -> do
      if x > y
        then runAll gf181 (program (fromInteger x)) [fromInteger y] [] [1]
        else runAll gf181 (program (fromInteger x)) [fromInteger y] [] [0]

  it "gt (constant / constant)" $ do
    let genPair = (,) <$> choose (0, 15) <*> choose (0, 15)
    let program x y = do
          return $ x `gt` (y :: UInt 4)

    forAll genPair $ \(x, y) -> do
      if x > y
        then runAll gf181 (program (fromInteger x) (fromInteger y)) [] [] [1]
        else runAll gf181 (program (fromInteger x) (fromInteger y)) [] [] [0]
