{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

module Test.Interpreter.UInt (tests, run) where

import Control.Monad (forM_, when)
import Data.Field.Galois (Prime)
import Keelung hiding (compile)
import Keelung.Compiler (Error (..))
import Keelung.Compiler.Compile.Error qualified as Compiler
import Keelung.Compiler.Compile.Error qualified as CompilerError
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
tests = do
  describe "Unsigned Integers" $ do
    describe "Big Int I/O" $ do
      it "10 bit / GF257" $ do
        let program = inputUInt @10 Public
        runAll gf181Info program [300] [] [300 :: Prime 257]

    describe "Arithmetics" $ do
      describe "Addition" $ do
        it "variable / variable" $ do
          -- let program = do
          --       x <- inputUInt @4 Public
          --       y <- inputUInt @4 Public
          --       return $ x + y
          -- debugPrime (Prime 13) program
          -- runPrime' (Prime 13) program [13, 7] [] [4]
          -- let genPair = do
          --       x <- choose (0, 16)
          --       y <- choose (0, 16)
          --       return (x, y)
          -- forAll genPair $ \(x, y) -> do
          --   let expected = [(x + y) `mod` 16]
          --   runPrime' (Prime 13) program [x, y] [] expected

          let program = do
                x <- inputUInt @4 Public
                y <- inputUInt @4 Public
                return $ x + y
          -- runPrime' gf181 program [13, 7] [] [4]
          let genPair = do
                x <- choose (0, 16)
                y <- choose (0, 16)
                return (x, y)
          forAll genPair $ \(x, y) -> do
            let expected = [(x + y) `mod` 16]
            runPrime' gf181 program [x, y] [] expected

        it "variable / constant" $ do
          let program = do
                x <- inputUInt @4 Public
                return $ x + 2
          forAll (choose (0, 100)) $ \x -> do
            let expected = [fromInteger ((x + 2) `mod` 16) :: GF181]
            runAll gf181Info program [fromInteger (x `mod` 16)] [] expected

        it "constant / constant" $ do
          let program x y = do
                return $ x + (y :: UInt 4)
          let genPair = do
                x <- choose (0, 15)
                y <- choose (0, 15)
                return (x, y)
          forAll genPair $ \(x, y) -> do
            let expected = [fromInteger ((x + y) `mod` 16) :: GF181]
            runAll gf181Info (program (fromInteger x) (fromInteger y)) [] [] expected

        it "10 bit / GF257" $ do
          let program = do
                x <- inputUInt @10 Public
                y <- inputUInt @10 Public
                return $ x + y
          -- debugPrime (Prime 257) program
          runPrime program [100, 200] [] [300 :: Prime 257]

      describe "Multiplication" $ do
        it "variable / variable" $ do
          let program = do
                x <- inputUInt @4 Public
                y <- inputUInt @4 Public
                return $ x * y
          -- runAll gf181Info program [3, 4] [] [7]
          let genPair = do
                x <- choose (0, 15)
                y <- choose (0, 15)
                return (x, y)
          forAll genPair $ \(x, y) -> do
            let expected = [fromInteger ((x * y) `mod` 16) :: GF181]
            runAll gf181Info program [fromInteger x, fromInteger y] [] expected

        it "variable / constant" $ do
          let program = do
                x <- inputUInt @4 Public
                return $ x * 2

          forAll (choose (0, 100)) $ \x -> do
            let expected = [fromInteger ((x * 2) `mod` 16) :: GF181]
            runAll gf181Info program [fromInteger (x `mod` 16)] [] expected

        it "constant / constant" $ do
          let program x y = do
                return $ x * (y :: UInt 4)
          let genPair = do
                x <- choose (0, 15)
                y <- choose (0, 15)
                return (x, y)
          forAll genPair $ \(x, y) -> do
            let expected = [fromInteger ((x * y) `mod` 16) :: GF181]
            runAll gf181Info (program (fromInteger x) (fromInteger y)) [] [] expected

      it "arithmetics 1" $ do
        let program = do
              f <- inputField Public
              u4 <- inputUInt @4 Public
              b <- inputBool Public
              return $
                cond
                  (b .&. (u4 !!! 0))
                  (f + 1)
                  (f + 2)

        runAll gf181Info program [100, 1, 1] [] [101 :: GF181]
        runAll gf181Info program [100, 0, 1] [] [102 :: GF181]

      it "add 1" $ do
        let program = do
              x <- inputUInt @4 Public
              y <- inputUInt @4 Public
              return $ x + y

        runAll gf181Info program [5, 6] [] [11 :: GF181]
        runAll gf181Info program [2, 5] [] [7 :: GF181]
        runAll gf181Info program [15, 1] [] [0 :: GF181]

      it "add 2" $ do
        let program = do
              x <- inputUInt @4 Public
              y <- inputUInt @4 Public
              z <- inputUInt @4 Public
              w <- reuse $ x + y
              return $ x + y + z + w

        runAll gf181Info program [5, 6, 7] [] [13 :: GF181]
        runAll gf181Info program [2, 5, 3] [] [1 :: GF181]
        runAll gf181Info program [0, 1, 2] [] [4 :: GF181]

      it "add + assertion" $ do
        let program = do
              x <- inputUInt @4 Public
              assert $ 2 `eq` (x + 1)
        runAll
          gf181Info
          program
          [1]
          []
          ([] :: [GF181])

      it "mul 3" $ do
        let program = do
              x <- inputUInt @4 Public
              y <- inputUInt @4 Public
              return $ x * y

        runAll gf181Info program [2, 4] [] [8 :: GF181]
        runAll gf181Info program [5, 6] [] [14 :: GF181]

      it "arithmetics 4" $ do
        let program = do
              x <- inputUInt @4 Public
              y <- inputUInt @4 Public
              return $ x * y + y

        runAll gf181Info program [5, 6] [] [4 :: GF181]
        runAll gf181Info program [2, 5] [] [15 :: GF181]
        runAll gf181Info program [15, 1] [] [0 :: GF181]

      it "arithmetics 5" $ do
        let program = do
              x <- inputUInt @4 Public
              y <- reuse x
              return (x + y)
        runAll gf181Info program [5] [] [10 :: GF181]

      it "modInv 123 2833" $ do
        let program = return $ modInv (123 :: UInt 32) 2833
        runAll gf181Info program [] [] [2119 :: GF181]

      describe "DivMod" $ do
        it "performDivMod (quotient & remainder unknown)" $ do
          let program = do
                dividend <- input Private :: Comp (UInt 6)
                divisor <- input Public
                performDivMod dividend divisor
          runAll gf181Info program [7] [20] [2, 6 :: GF181]
          runAll gf181Info program [4] [4] [1, 0 :: GF181]

        it "performDivMod (on constants) (issue #18)" $ do
          -- 7 = 3 * 2 + 1
          let program = performDivMod 7 (3 :: UInt 4)
          runAll gf181Info program [] [] [2, 1 :: GF181]

        it "assertDivMod (on constants) (issue #18)" $ do
          let program = assertDivMod 7 (3 :: UInt 4) 2 1
          runAll gf181Info program [] [] ([] :: [GF181])

        it "assertDivMod (with wrong quotient constant)" $ do
          let program = assertDivMod 7 (3 :: UInt 4) 3 1
          throwAll
            gf181Info
            program
            []
            []
            (Interpreter.SyntaxTreeError (SyntaxTree.DivModQuotientError 7 3 2 3))
            (CompileError (Compiler.ConflictingValuesB True False) :: Error GF181)

        it "assertDivMod (with wrong remainder constant)" $ do
          let program = assertDivMod 7 (3 :: UInt 4) 2 0
          throwAll
            gf181Info
            program
            []
            []
            (Interpreter.SyntaxTreeError (SyntaxTree.DivModRemainderError 7 3 1 0))
            (CompileError (Compiler.ConflictingValuesB False True) :: Error GF181)

        it "assertDivMod (multiple statements)" $ do
          let program = do
                a <- input Public :: Comp (UInt 5)
                b <- input Public
                c <- input Private
                d <- input Public
                (q0, r0) <- performDivMod a b
                (q1, r1) <- performDivMod c d
                return [q0, r0, q1, r1]
          runAll gf181Info program [20, 7, 8] [21] [2, 6, 2, 5 :: GF181]

        it "assertDivMod (multiple statements chained together)" $ do
          let program = do
                a <- input Public :: Comp (UInt 5)
                b <- input Public
                (q0, r0) <- performDivMod a b
                (q1, r1) <- performDivMod q0 b
                return [q0, r0, q1, r1]
          runAll gf181Info program [25, 3] [] [8, 1, 2, 2 :: GF181]

        it "performDivMod (before assertions)" $ do
          let program = do
                a <- input Public :: Comp (UInt 5)
                b <- input Public
                (q, r) <- performDivMod a b
                assert $ q `eq` r
          runAll gf181Info program [10, 4] [] ([] :: [GF181])

        it "performDivMod (before reuse)" $ do
          let program = do
                a <- input Public :: Comp (UInt 5)
                b <- input Public
                (q, _) <- performDivMod a b
                reuse q
          runAll gf181Info program [10, 4] [] [2 :: GF181]

        it "performDivMod (after reuse)" $ do
          let program = do
                a <- reuse =<< input Public :: Comp (UInt 5)
                b <- input Public
                (q, r) <- performDivMod a b
                assert $ q `eq` r
          runAll gf181Info program [10, 4] [] ([] :: [GF181])

        it "assertDivMod (dividend unknown)" $ do
          let program = do
                dividend <- freshVarUInt
                divisor <- input Public :: Comp (UInt 6)
                quotient <- input Public
                remainder <- input Private
                assertDivMod dividend divisor quotient remainder
                return dividend
          runAll gf181Info program [7, 2] [6] [20 :: GF181]

        it "assertDivMod (divisor & remainder unknown)" $ do
          let program = do
                dividend <- input Public :: Comp (UInt 4)
                divisor <- freshVarUInt
                quotient <- input Public
                remainder <- freshVarUInt
                assertDivMod dividend divisor quotient remainder
                return (divisor, remainder)
          runAll gf181Info program [7, 2] [] [3, 1 :: GF181]

        it "assertDivMod (quotient & remainder unknown)" $ do
          let program = do
                dividend <- input Public :: Comp (UInt 6)
                divisor <- input Public
                quotient <- freshVarUInt
                remainder <- freshVarUInt
                assertDivMod dividend divisor quotient remainder
                return (quotient, remainder)
          runAll gf181Info program [34, 6] [] [5, 4 :: GF181]

    describe "Comparisons" $ do
      it "assertLTE" $ do
        -- `bound` ranges from `-50` to `50`
        forAll (choose (-50, 50)) $ \bound -> do
          let width = 4

          let program = do
                x <- inputUInt @4 Public
                assertLTE x bound

          when (bound < 0) $ do
            forM_ [0 .. 15] $ \x -> do
              throwAll
                gf181Info
                program
                [fromInteger x]
                []
                (Interpreter.SyntaxTreeError (SyntaxTree.AssertLTEBoundTooSmallError bound))
                (CompileError (CompilerError.AssertLTEBoundTooSmallError bound) :: Error GF181)

          when (bound >= 0 && bound < 15) $ do
            forM_ [0 .. 15] $ \x -> do
              if x <= bound
                then runAll gf181Info program [fromInteger x] [] ([] :: [GF181])
                else do
                  throwAll
                    gf181Info
                    program
                    [fromInteger x]
                    []
                    (Interpreter.SyntaxTreeError (SyntaxTree.AssertLTEError (fromInteger x) bound))
                    (InterpretError (Interpreter.R1CSError R1CS.ConflictingValues) :: Error GF181)

          when (bound >= 15) $ do
            forM_ [0 .. 15] $ \x -> do
              throwAll
                gf181Info
                program
                [fromInteger x]
                []
                (Interpreter.SyntaxTreeError (SyntaxTree.AssertLTEBoundTooLargeError bound width))
                (CompileError (CompilerError.AssertLTEBoundTooLargeError bound width) :: Error GF181)

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
                (CompileError (CompilerError.AssertLTBoundTooSmallError bound) :: Error GF181)

          when (bound >= 1 && bound < 16) $ do
            forM_ [0 .. 15] $ \x -> do
              if x < bound
                then runAll gf181Info program [fromInteger x] [] ([] :: [GF181])
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
                (CompileError (CompilerError.AssertLTBoundTooLargeError bound width) :: Error GF181)

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
                (CompileError (CompilerError.AssertGTEBoundTooSmallError bound) :: Error GF181)

          when (bound >= 1 && bound < 16) $ do
            forM_ [0 .. 15] $ \x -> do
              if x >= bound
                then runAll gf181Info program [fromInteger x] [] ([] :: [GF181])
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
                (CompileError (CompilerError.AssertGTEBoundTooLargeError bound width) :: Error GF181)

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
                (CompileError (CompilerError.AssertGTBoundTooSmallError bound) :: Error GF181)

          when (bound >= 0 && bound < 15) $ do
            forM_ [0 .. 15] $ \x -> do
              if x > bound
                then runAll gf181Info program [fromInteger x] [] ([] :: [GF181])
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
                (CompileError (CompilerError.AssertGTBoundTooLargeError bound width) :: Error GF181)

      it "lte (variable / variable)" $ do
        let genPair = (,) <$> choose (0, 15) <*> choose (0, 15)
        let program = do
              x <- inputUInt @4 Public
              y <- inputUInt @4 Public
              return $ x `lte` y

        forAll genPair $ \(x, y) -> do
          if x <= y
            then runAll gf181Info program [fromInteger x, fromInteger y] [] [1 :: GF181]
            else runAll gf181Info program [fromInteger x, fromInteger y] [] [0 :: GF181]

      it "lte (variable / constant)" $ do
        let genPair = (,) <$> choose (0, 15) <*> choose (0, 15)
        let program y = do
              x <- inputUInt @4 Public
              return $ x `lte` y

        forAll genPair $ \(x, y) -> do
          if x <= y
            then runAll gf181Info (program (fromInteger y)) [fromInteger x] [] [1 :: GF181]
            else runAll gf181Info (program (fromInteger y)) [fromInteger x] [] [0 :: GF181]

      it "lte (constant / variable)" $ do
        let genPair = (,) <$> choose (0, 15) <*> choose (0, 15)
        let program x = do
              y <- inputUInt @4 Public
              return $ x `lte` y

        forAll genPair $ \(x, y) -> do
          if x <= y
            then runAll gf181Info (program (fromInteger x)) [fromInteger y] [] [1 :: GF181]
            else runAll gf181Info (program (fromInteger x)) [fromInteger y] [] [0 :: GF181]

      it "lte (constant / constant)" $ do
        let genPair = (,) <$> choose (0, 15) <*> choose (0, 15)
        let program x y = do
              return $ x `lte` (y :: UInt 4)

        forAll genPair $ \(x, y) -> do
          if x <= y
            then runAll gf181Info (program (fromInteger x) (fromInteger y)) [] [] ([1] :: [GF181])
            else runAll gf181Info (program (fromInteger x) (fromInteger y)) [] [] ([0] :: [GF181])

      it "lt (variable / variable)" $ do
        let genPair = (,) <$> choose (0, 15) <*> choose (0, 15)
        let program = do
              x <- inputUInt @4 Public
              y <- inputUInt @4 Public
              return $ x `lt` y

        forAll genPair $ \(x, y) -> do
          if x < y
            then runAll gf181Info program [fromInteger x, fromInteger y] [] [1 :: GF181]
            else runAll gf181Info program [fromInteger x, fromInteger y] [] [0 :: GF181]

      it "lt (variable / constant)" $ do
        let genPair = (,) <$> choose (0, 15) <*> choose (0, 15)
        let program y = do
              x <- inputUInt @4 Public
              return $ x `lt` y

        forAll genPair $ \(x, y) -> do
          if x < y
            then runAll gf181Info (program (fromInteger y)) [fromInteger x] [] [1 :: GF181]
            else runAll gf181Info (program (fromInteger y)) [fromInteger x] [] [0 :: GF181]

      it "lt (constant / variable)" $ do
        let genPair = (,) <$> choose (0, 15) <*> choose (0, 15)
        let program x = do
              y <- inputUInt @4 Public
              return $ x `lt` y

        forAll genPair $ \(x, y) -> do
          if x < y
            then runAll gf181Info (program (fromInteger x)) [fromInteger y] [] [1 :: GF181]
            else runAll gf181Info (program (fromInteger x)) [fromInteger y] [] [0 :: GF181]

      it "lt (constant / constant)" $ do
        let genPair = (,) <$> choose (0, 15) <*> choose (0, 15)
        let program x y = do
              return $ x `lt` (y :: UInt 4)

        forAll genPair $ \(x, y) -> do
          if x < y
            then runAll gf181Info (program (fromInteger x) (fromInteger y)) [] [] ([1] :: [GF181])
            else runAll gf181Info (program (fromInteger x) (fromInteger y)) [] [] ([0] :: [GF181])

      it "gte (variable / variable)" $ do
        let genPair = (,) <$> choose (0, 15) <*> choose (0, 15)
        let program = do
              x <- inputUInt @4 Public
              y <- inputUInt @4 Public
              return $ x `gte` y

        forAll genPair $ \(x, y) -> do
          if x >= y
            then runAll gf181Info program [fromInteger x, fromInteger y] [] [1 :: GF181]
            else runAll gf181Info program [fromInteger x, fromInteger y] [] [0 :: GF181]

      it "gte (variable / constant)" $ do
        let genPair = (,) <$> choose (0, 15) <*> choose (0, 15)
        let program y = do
              x <- inputUInt @4 Public
              return $ x `gte` y

        forAll genPair $ \(x, y) -> do
          if x >= y
            then runAll gf181Info (program (fromInteger y)) [fromInteger x] [] [1 :: GF181]
            else runAll gf181Info (program (fromInteger y)) [fromInteger x] [] [0 :: GF181]

      it "gte (constant / variable)" $ do
        let genPair = (,) <$> choose (0, 15) <*> choose (0, 15)
        let program x = do
              y <- inputUInt @4 Public
              return $ x `gte` y

        forAll genPair $ \(x, y) -> do
          if x >= y
            then runAll gf181Info (program (fromInteger x)) [fromInteger y] [] [1 :: GF181]
            else runAll gf181Info (program (fromInteger x)) [fromInteger y] [] [0 :: GF181]

      it "gte (constant / constant)" $ do
        let genPair = (,) <$> choose (0, 15) <*> choose (0, 15)
        let program x y = do
              return $ x `gte` (y :: UInt 4)

        forAll genPair $ \(x, y) -> do
          if x >= y
            then runAll gf181Info (program (fromInteger x) (fromInteger y)) [] [] ([1] :: [GF181])
            else runAll gf181Info (program (fromInteger x) (fromInteger y)) [] [] ([0] :: [GF181])

      it "gt (variable / variable)" $ do
        let genPair = (,) <$> choose (0, 15) <*> choose (0, 15)
        let program = do
              x <- inputUInt @4 Public
              y <- inputUInt @4 Public
              return $ x `gt` y

        forAll genPair $ \(x, y) -> do
          if x > y
            then runAll gf181Info program [fromInteger x, fromInteger y] [] [1 :: GF181]
            else runAll gf181Info program [fromInteger x, fromInteger y] [] [0 :: GF181]

      it "gt (variable / constant)" $ do
        let genPair = (,) <$> choose (0, 15) <*> choose (0, 15)
        let program y = do
              x <- inputUInt @4 Public
              return $ x `gt` y

        forAll genPair $ \(x, y) -> do
          if x > y
            then runAll gf181Info (program (fromInteger y)) [fromInteger x] [] [1 :: GF181]
            else runAll gf181Info (program (fromInteger y)) [fromInteger x] [] [0 :: GF181]

      it "gt (constant / variable)" $ do
        let genPair = (,) <$> choose (0, 15) <*> choose (0, 15)
        let program x = do
              y <- inputUInt @4 Public
              return $ x `gt` y

        forAll genPair $ \(x, y) -> do
          if x > y
            then runAll gf181Info (program (fromInteger x)) [fromInteger y] [] [1 :: GF181]
            else runAll gf181Info (program (fromInteger x)) [fromInteger y] [] [0 :: GF181]

      it "gt (constant / constant)" $ do
        let genPair = (,) <$> choose (0, 15) <*> choose (0, 15)
        let program x y = do
              return $ x `gt` (y :: UInt 4)

        forAll genPair $ \(x, y) -> do
          if x > y
            then runAll gf181Info (program (fromInteger x) (fromInteger y)) [] [] ([1] :: [GF181])
            else runAll gf181Info (program (fromInteger x) (fromInteger y)) [] [] ([0] :: [GF181])

    describe "Conditionals" $ do
      it "with inputs" $ do
        let program = do
              x <- input Public :: Comp (UInt 4)
              y <- input Public
              return $ cond true x y
        runAll gf181Info program [5, 6] [] [5 :: GF181]

      it "with literals" $ do
        let program = do
              return $ cond true (3 :: UInt 2) 2
        runAll gf181Info program [] [] [3 :: GF181]

    describe "Equalities" $ do
      it "eq" $ do
        let program = do
              x <- inputUInt @4 Public
              y <- inputUInt @4 Public
              return (x `eq` y)
        runAll gf181Info program [5, 6] [] [0 :: GF181]
        runAll gf181Info program [4, 4] [] [1 :: GF181]

      it "neq 1" $ do
        let program = do
              x <- inputUInt @4 Public
              y <- inputUInt @4 Public
              return (x `neq` y)
        runAll gf181Info program [5, 6] [] [1 :: GF181]
        runAll gf181Info program [4, 4] [] [0 :: GF181]

      it "neq 2" $ do
        let program = do
              x <- inputUInt @4 Public
              return (x `neq` 3)
        runAll gf181Info program [5] [] [1 :: GF181]
        runAll gf181Info program [3] [] [0 :: GF181]

      it "neq 3" $ do
        let program = do
              x <- inputUInt @4 Public
              assert $ x `neq` 3
        runAll gf181Info program [5] [] ([] :: [GF181])
        throwAll
          gf181Info
          program
          [3]
          []
          (Interpreter.SyntaxTreeError $ SyntaxTree.AssertionError "¬ ($UI₄0 = 3)")
          (InterpretError (Interpreter.R1CSError R1CS.ConflictingValues) :: Error GF181)

      it "neq 4" $ do
        let program = do
              assert $ 3 `neq` (3 :: UInt 4)
        throwAll
          gf181Info
          program
          []
          []
          (Interpreter.SyntaxTreeError $ SyntaxTree.AssertionError "¬ (3 = 3)")
          (CompileError (Compiler.ConflictingValuesB True False) :: Error GF181)

    describe "Bitwise" $ do
      it "rotate" $ do
        let program = do
              x <- inputUInt @4 Public
              return [rotate x (-4), rotate x (-3), rotate x (-2), rotate x (-1), rotate x 0, rotate x 1, rotate x 2, rotate x 3, rotate x 4]

        runAll gf181Info program [0] [] [0, 0, 0, 0, 0, 0, 0, 0, 0 :: GF181]
        runAll gf181Info program [1] [] [1, 2, 4, 8, 1, 2, 4, 8, 1 :: GF181]
        runAll gf181Info program [3] [] [3, 6, 12, 9, 3, 6, 12, 9, 3 :: GF181]
        runAll gf181Info program [5] [] [5, 10, 5, 10, 5, 10, 5, 10, 5 :: GF181]

      it "shift" $ do
        let program = do
              x <- inputUInt @4 Public
              return [x .<<. (-4), x .>>. 3, shift x (-2), shift x (-1), shift x 0, shift x 1, shift x 2, shift x 3, shift x 4]

        runAll gf181Info program [0] [] [0, 0, 0, 0, 0, 0, 0, 0, 0 :: GF181]
        runAll gf181Info program [1] [] [0, 0, 0, 0, 1, 2, 4, 8, 0 :: GF181]
        runAll gf181Info program [3] [] [0, 0, 0, 1, 3, 6, 12, 8, 0 :: GF181]
        runAll gf181Info program [5] [] [0, 0, 1, 2, 5, 10, 4, 8, 0 :: GF181]

      it "Bit test / literal" $ do
        -- 0011
        let program = do
              let c = 3 :: UInt 4
              return [c !!! (-1), c !!! 0, c !!! 1, c !!! 2, c !!! 3, c !!! 4]
        runAll gf181Info program [] [] [0, 1, 1, 0, 0, 1 :: GF181]

      it "Bit test / input var" $ do
        let program = do
              c <- input Private :: Comp (UInt 4)
              return [c !!! (-1), c !!! 0, c !!! 1, c !!! 2, c !!! 3, c !!! 4]
        runAll gf181Info program [] [3] [0, 1, 1, 0, 0, 1 :: GF181]
        runAll gf181Info program [] [5] [0, 1, 0, 1, 0, 1 :: GF181]

      it "Bit test / and 1" $ do
        let program = do
              x <- inputUInt @4 Public
              y <- inputUInt @4 Private
              return $ (x .&. y) !!! 0
        runAll gf181Info program [2] [3] [0 :: GF181]
        runAll gf181Info program [3] [5] [1 :: GF181]

      it "Bit test / and 2" $ do
        let program = do
              x <- inputUInt @4 Public
              y <- inputUInt @4 Private
              z <- inputUInt @4 Public
              return $ (x .&. y .&. z) !!! 0
        runAll gf181Info program [2, 4] [3] [0 :: GF181]
        runAll gf181Info program [3, 7] [5] [1 :: GF181]

      it "Bit test / or 1" $ do
        let program = do
              x <- inputUInt @4 Public
              y <- inputUInt @4 Private
              return $ (x .|. y) !!! 1
        runAll gf181Info program [2] [3] [1 :: GF181]
        runAll gf181Info program [3] [5] [1 :: GF181]
        runAll gf181Info program [5] [9] [0 :: GF181]

      it "Bit test / or 2" $ do
        let program = do
              x <- inputUInt @4 Public
              return $ (x .|. 3) !!! 2
        runAll gf181Info program [2] [] [0 :: GF181]
        runAll gf181Info program [3] [] [0 :: GF181]
        runAll gf181Info program [5] [] [1 :: GF181]

      it "Bit test / xor 0" $ do
        let program = do
              x <- inputUInt @4 Public
              y <- inputUInt @4 Private
              let w = x .^. y .^. 0
              return [w !!! 0]
        runAll gf181Info program [2] [3] [1 :: GF181]

      it "Bit test / xor 1" $ do
        let program = do
              x <- inputUInt @4 Public
              y <- inputUInt @4 Private
              z <- inputUInt @4 Public
              w <- reuse $ x .^. y .^. z
              return [w !!! 0, w !!! 1, w !!! 2, w !!! 3]
        runAll gf181Info program [2, 4] [3] [1, 0, 1, 0 :: GF181]
        runAll gf181Info program [3, 7] [5] [1, 0, 0, 0 :: GF181]

      it "Bit test / BtoU" $ do
        let program = do
              x <- input Public
              let u = BtoU x :: UInt 4
              return [u !!! 0, u !!! 1, u !!! 2, u !!! 3]
        runAll gf181Info program [0] [] [0, 0, 0, 0 :: GF181]
        runAll gf181Info program [1] [] [1, 0, 0, 0 :: GF181]

      it "Bit test / rotate 1" $ do
        let program = do
              x <- inputUInt @4 Public
              return $ (x `rotate` 0) !!! 0
        runAll gf181Info program [2] [] [0 :: GF181]

      it "Bit test / rotate 2" $ do
        -- 0011 0100211003
        let program = do
              x <- inputUInt @4 Public
              y <- inputUInt @4 Public
              return
                [ (x `rotate` 0) !!! 0,
                  (x `rotate` 1) !!! 1,
                  (x `rotate` (-1)) !!! 0,
                  ((x .^. y) `rotate` 1) !!! 1
                ]
        runAll gf181Info program [2, 3] [] [0, 0, 1, 1 :: GF181]