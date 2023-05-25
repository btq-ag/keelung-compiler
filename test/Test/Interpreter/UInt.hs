{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

module Test.Interpreter.UInt (tests, run) where

import Control.Monad (forM_, when)
import Keelung hiding (compile)
import Keelung.Compiler (Error (..))
import Keelung.Compiler.Compile.Error qualified as Compiler
import Keelung.Compiler.Compile.Error qualified as CompilerError
import Keelung.Constraint.R1C (R1C (R1C))
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
    describe "Arithmetics" $ do
      describe "Addition" $ do
        it "variable / variable" $ do
          let program = do
                x <- inputUInt @4 Public
                y <- inputUInt @4 Public
                return $ x + y
          -- runAll gf181Info program [3, 4] ([] :: [GF181]) [7]
          let genPair = do
                x <- choose (0, 15)
                y <- choose (0, 15)
                return (x, y)
          forAll genPair $ \(x, y) -> do
            let expected = [fromInteger ((x + y) `mod` 16)]
            runAll gf181Info program [fromInteger x, fromInteger y] ([] :: [GF181]) expected

        it "variable / constant" $ do
          let program = do
                x <- inputUInt @4 Public
                return $ x + 2
          forAll (choose (0, 100)) $ \x -> do
            let expected = [fromInteger ((x + 2) `mod` 16)]
            runAll gf181Info program [fromInteger (x `mod` 16)] ([] :: [GF181]) expected

        it "constant / constant" $ do
          let program = do
                return $ 1 + (2 :: UInt 4)
          runAll gf181Info program [] ([] :: [GF181]) [3]
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

        runAll gf181Info program [100, 1, 1 :: GF181] [] [101]
        runAll gf181Info program [100, 0, 1 :: GF181] [] [102]

      it "add 1" $ do
        let program = do
              x <- inputUInt @4 Public
              y <- inputUInt @4 Public
              return $ x + y

        runAll gf181Info program [5, 6 :: GF181] [] [11]
        runAll gf181Info program [2, 5 :: GF181] [] [7]
        runAll gf181Info program [15, 1 :: GF181] [] [0]

      it "add 2" $ do
        let program = do
              x <- inputUInt @4 Public
              y <- inputUInt @4 Public
              z <- inputUInt @4 Public
              w <- reuse $ x + y
              return $ x + y + z + w

        runAll gf181Info program [5, 6, 7 :: GF181] [] [13]
        runAll gf181Info program [2, 5, 3 :: GF181] [] [1]
        runAll gf181Info program [0, 1, 2 :: GF181] [] [4]

      it "add + assertion" $ do
        let program = do
              x <- inputUInt @4 Public
              assert $ 2 `eq` (x + 1)
        runAll
          gf181Info
          program
          [1]
          ([] :: [GF181])
          []

      it "mul 3" $ do
        let program = do
              x <- inputUInt @4 Public
              y <- inputUInt @4 Public
              return $ x * y

        runAll gf181Info program [2, 4 :: GF181] [] [8]
        runAll gf181Info program [5, 6 :: GF181] [] [14]

      it "arithmetics 4" $ do
        let program = do
              x <- inputUInt @4 Public
              y <- inputUInt @4 Public
              return $ x * y + y

        runAll gf181Info program [5, 6 :: GF181] [] [4]
        runAll gf181Info program [2, 5 :: GF181] [] [15]
        runAll gf181Info program [15, 1 :: GF181] [] [0]

      it "arithmetics 5" $ do
        let program = do
              x <- inputUInt @4 Public
              y <- reuse x
              return (x + y)
        runAll gf181Info program [5 :: GF181] [] [10]

      it "modInv 123 2833" $ do
        let program = return $ modInv (123 :: UInt 32) 2833
        runAll gf181Info program [] ([] :: [GF181]) [2119]

      describe "DivMod" $ do
        it "performDivMod (quotient & remainder unknown)" $ do
          let program = do
                dividend <- input Private :: Comp (UInt 4)
                divisor <- input Public
                performDivMod dividend divisor
          runAll gf181Info program [7 :: GF181] [20] [2, 6]
          runAll gf181Info program [4 :: GF181] [4] [1, 0]

        it "performDivMod (on constants) (issue #18)" $ do
          -- 7 = 3 * 2 + 1
          let program = performDivMod 7 (3 :: UInt 4)
          runAll gf181Info program [] [] [2, 1 :: GF181]

        it "assertDivMod (on constants) (issue #18)" $ do
          let program = assertDivMod 7 (3 :: UInt 4) 2 1
          runAll gf181Info program [] [] ([] :: [GF181])

        it "assertDivMod (with wrong quotient constant)" $ do
          let program = assertDivMod 7 (3 :: UInt 4) 3 1
          throwAll'
            gf181Info
            program
            []
            ([] :: [GF181])
            (Interpreter.SyntaxTreeError (SyntaxTree.DivModQuotientError 7 3 2 3))
            (InterpretError (Interpreter.R1CSError (R1CS.R1CInconsistentError $ R1C (Left 3) (Left 3) (Left 6))))
            (InterpretError (Interpreter.R1CSError (R1CS.DivModQuotientError 7 3 2 3)))

        it "assertDivMod (with wrong remainder constant)" $ do
          let program = assertDivMod 7 (3 :: UInt 4) 2 0
          throwAll'
            gf181Info
            program
            []
            ([] :: [GF181])
            (Interpreter.SyntaxTreeError (SyntaxTree.DivModRemainderError 7 3 1 0))
            (InterpretError (Interpreter.R1CSError (R1CS.R1CInconsistentError $ R1C (Left 3) (Left 2) (Left 7))))
            (InterpretError (Interpreter.R1CSError (R1CS.DivModRemainderError 7 3 1 0)))

        it "assertDivMod (multiple statements)" $ do
          let program = do
                a <- input Public :: Comp (UInt 5)
                b <- input Public
                c <- input Private
                d <- input Public
                (q0, r0) <- performDivMod a b
                (q1, r1) <- performDivMod c d
                return [q0, r0, q1, r1]
          runAll gf181Info program [20, 7, 8 :: GF181] [21] [2, 6, 2, 5]

        it "assertDivMod (multiple statements chained together)" $ do
          let program = do
                a <- input Public :: Comp (UInt 5)
                b <- input Public
                (q0, r0) <- performDivMod a b
                (q1, r1) <- performDivMod q0 b
                return [q0, r0, q1, r1]
          runAll gf181Info program [25, 3 :: GF181] [] [8, 1, 2, 2]

        it "performDivMod (before assertions)" $ do
          let program = do
                a <- input Public :: Comp (UInt 5)
                b <- input Public
                (q, r) <- performDivMod a b
                assert $ q `eq` r
          runAll gf181Info program [10, 4 :: GF181] [] []

        it "performDivMod (before reuse)" $ do
          let program = do
                a <- input Public :: Comp (UInt 5)
                b <- input Public
                (q, _) <- performDivMod a b
                reuse q
          runAll gf181Info program [10, 4 :: GF181] [] [2]

        it "performDivMod (after reuse)" $ do
          let program = do
                a <- reuse =<< input Public :: Comp (UInt 5)
                b <- input Public
                (q, r) <- performDivMod a b
                assert $ q `eq` r
          runAll gf181Info program [10, 4 :: GF181] [] []

        it "assertDivMod (dividend unknown)" $ do
          let program = do
                dividend <- freshVarUInt
                divisor <- input Public :: Comp (UInt 4)
                quotient <- input Public
                remainder <- input Private
                assertDivMod dividend divisor quotient remainder
                return dividend
          runAll gf181Info program [7, 2 :: GF181] [6] [20]

        it "assertDivMod (divisor & remainder unknown)" $ do
          let program = do
                dividend <- input Public :: Comp (UInt 4)
                divisor <- freshVarUInt
                quotient <- input Public
                remainder <- freshVarUInt
                assertDivMod dividend divisor quotient remainder
                return (divisor, remainder)
          runAll gf181Info program [7, 2 :: GF181] [] [3, 1]

        it "assertDivMod (quotient & remainder unknown)" $ do
          let program = do
                dividend <- input Public :: Comp (UInt 4)
                divisor <- input Public
                quotient <- freshVarUInt
                remainder <- freshVarUInt
                assertDivMod dividend divisor quotient remainder
                return (quotient, remainder)
          runAll gf181Info program [34, 6 :: GF181] [] [5, 4]

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
                [fromInteger x :: GF181]
                []
                (Interpreter.SyntaxTreeError (SyntaxTree.AssertLTEBoundTooSmallError bound))
                (CompileError (CompilerError.AssertLTEBoundTooSmallError bound))

          when (bound >= 0 && bound < 15) $ do
            forM_ [0 .. 15] $ \x -> do
              if x <= bound
                then runAll gf181Info program [fromInteger x :: GF181] [] []
                else do
                  throwAll
                    gf181Info
                    program
                    [fromInteger x :: GF181]
                    []
                    (Interpreter.SyntaxTreeError (SyntaxTree.AssertLTEError (fromInteger x) bound))
                    (InterpretError (Interpreter.R1CSError (R1CS.R1CInconsistentError $ R1C (Left (-1)) (Left 1) (Left 0))))

          when (bound >= 15) $ do
            forM_ [0 .. 15] $ \x -> do
              throwAll
                gf181Info
                program
                [fromInteger x :: GF181]
                []
                (Interpreter.SyntaxTreeError (SyntaxTree.AssertLTEBoundTooLargeError bound width))
                (CompileError (CompilerError.AssertLTEBoundTooLargeError bound width))

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
                [fromInteger x :: GF181]
                []
                (Interpreter.SyntaxTreeError (SyntaxTree.AssertLTBoundTooSmallError bound))
                (CompileError (CompilerError.AssertLTBoundTooSmallError bound))

          when (bound >= 1 && bound < 16) $ do
            forM_ [0 .. 15] $ \x -> do
              if x < bound
                then runAll gf181Info program [fromInteger x :: GF181] [] []
                else do
                  throwAll
                    gf181Info
                    program
                    [fromInteger x :: GF181]
                    []
                    (Interpreter.SyntaxTreeError (SyntaxTree.AssertLTError (fromInteger x) bound))
                    (InterpretError (Interpreter.R1CSError (R1CS.R1CInconsistentError $ R1C (Left (-1)) (Left 1) (Left 0))))

          when (bound >= 16) $ do
            forM_ [0 .. 15] $ \x -> do
              throwAll
                gf181Info
                program
                [fromInteger x :: GF181]
                []
                (Interpreter.SyntaxTreeError (SyntaxTree.AssertLTBoundTooLargeError bound width))
                (CompileError (CompilerError.AssertLTBoundTooLargeError bound width))

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
                [fromInteger x :: GF181]
                []
                (Interpreter.SyntaxTreeError (SyntaxTree.AssertGTEBoundTooSmallError bound))
                (CompileError (CompilerError.AssertGTEBoundTooSmallError bound))

          when (bound >= 1 && bound < 16) $ do
            forM_ [0 .. 15] $ \x -> do
              if x >= bound
                then runAll gf181Info program [fromInteger x :: GF181] [] []
                else do
                  throwAll
                    gf181Info
                    program
                    [fromInteger x :: GF181]
                    []
                    (Interpreter.SyntaxTreeError (SyntaxTree.AssertGTEError (fromInteger x) bound))
                    (InterpretError (Interpreter.R1CSError (R1CS.R1CInconsistentError $ R1C (Left 0) (Left 0) (Left (-1)))))

          when (bound >= 16) $ do
            forM_ [0 .. 15] $ \x -> do
              throwAll
                gf181Info
                program
                [fromInteger x :: GF181]
                []
                (Interpreter.SyntaxTreeError (SyntaxTree.AssertGTEBoundTooLargeError bound width))
                (CompileError (CompilerError.AssertGTEBoundTooLargeError bound width))

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
                [fromInteger x :: GF181]
                []
                (Interpreter.SyntaxTreeError (SyntaxTree.AssertGTBoundTooSmallError bound))
                (CompileError (CompilerError.AssertGTBoundTooSmallError bound))

          when (bound >= 0 && bound < 15) $ do
            forM_ [0 .. 15] $ \x -> do
              if x > bound
                then runAll gf181Info program [fromInteger x :: GF181] [] []
                else do
                  throwAll
                    gf181Info
                    program
                    [fromInteger x :: GF181]
                    []
                    (Interpreter.SyntaxTreeError (SyntaxTree.AssertGTError (fromInteger x) bound))
                    (InterpretError (Interpreter.R1CSError (R1CS.R1CInconsistentError $ R1C (Left 0) (Left 0) (Left (-1)))))

          when (bound >= 15) $ do
            forM_ [0 .. 15] $ \x -> do
              throwAll
                gf181Info
                program
                [fromInteger x :: GF181]
                []
                (Interpreter.SyntaxTreeError (SyntaxTree.AssertGTBoundTooLargeError bound width))
                (CompileError (CompilerError.AssertGTBoundTooLargeError bound width))

      it "lte (variable / variable)" $ do
        let genPair = (,) <$> choose (0, 15) <*> choose (0, 15)
        let program = do
              x <- inputUInt @4 Public
              y <- inputUInt @4 Public
              return $ x `lte` y

        forAll genPair $ \(x, y) -> do
          if x <= y
            then runAll gf181Info program [fromInteger x, fromInteger y :: GF181] [] [1]
            else runAll gf181Info program [fromInteger x, fromInteger y :: GF181] [] [0]

      it "lte (variable / constant)" $ do
        let genPair = (,) <$> choose (0, 15) <*> choose (0, 15)
        let program y = do
              x <- inputUInt @4 Public
              return $ x `lte` y

        forAll genPair $ \(x, y) -> do
          if x <= y
            then runAll gf181Info (program (fromInteger y)) [fromInteger x :: GF181] [] [1]
            else runAll gf181Info (program (fromInteger y)) [fromInteger x :: GF181] [] [0]

      it "lte (constant / variable)" $ do
        let genPair = (,) <$> choose (0, 15) <*> choose (0, 15)
        let program x = do
              y <- inputUInt @4 Public
              return $ x `lte` y

        forAll genPair $ \(x, y) -> do
          if x <= y
            then runAll gf181Info (program (fromInteger x)) [fromInteger y :: GF181] [] [1]
            else runAll gf181Info (program (fromInteger x)) [fromInteger y :: GF181] [] [0]

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
            then runAll gf181Info program [fromInteger x, fromInteger y :: GF181] [] [1]
            else runAll gf181Info program [fromInteger x, fromInteger y :: GF181] [] [0]

      it "lt (variable / constant)" $ do
        let genPair = (,) <$> choose (0, 15) <*> choose (0, 15)
        let program y = do
              x <- inputUInt @4 Public
              return $ x `lt` y

        forAll genPair $ \(x, y) -> do
          if x < y
            then runAll gf181Info (program (fromInteger y)) [fromInteger x :: GF181] [] [1]
            else runAll gf181Info (program (fromInteger y)) [fromInteger x :: GF181] [] [0]

      it "lt (constant / variable)" $ do
        let genPair = (,) <$> choose (0, 15) <*> choose (0, 15)
        let program x = do
              y <- inputUInt @4 Public
              return $ x `lt` y

        forAll genPair $ \(x, y) -> do
          if x < y
            then runAll gf181Info (program (fromInteger x)) [fromInteger y :: GF181] [] [1]
            else runAll gf181Info (program (fromInteger x)) [fromInteger y :: GF181] [] [0]

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
            then runAll gf181Info program [fromInteger x, fromInteger y :: GF181] [] [1]
            else runAll gf181Info program [fromInteger x, fromInteger y :: GF181] [] [0]

      it "gte (variable / constant)" $ do
        let genPair = (,) <$> choose (0, 15) <*> choose (0, 15)
        let program y = do
              x <- inputUInt @4 Public
              return $ x `gte` y

        forAll genPair $ \(x, y) -> do
          if x >= y
            then runAll gf181Info (program (fromInteger y)) [fromInteger x :: GF181] [] [1]
            else runAll gf181Info (program (fromInteger y)) [fromInteger x :: GF181] [] [0]

      it "gte (constant / variable)" $ do
        let genPair = (,) <$> choose (0, 15) <*> choose (0, 15)
        let program x = do
              y <- inputUInt @4 Public
              return $ x `gte` y

        forAll genPair $ \(x, y) -> do
          if x >= y
            then runAll gf181Info (program (fromInteger x)) [fromInteger y :: GF181] [] [1]
            else runAll gf181Info (program (fromInteger x)) [fromInteger y :: GF181] [] [0]

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
            then runAll gf181Info program [fromInteger x, fromInteger y :: GF181] [] [1]
            else runAll gf181Info program [fromInteger x, fromInteger y :: GF181] [] [0]

      it "gt (variable / constant)" $ do
        let genPair = (,) <$> choose (0, 15) <*> choose (0, 15)
        let program y = do
              x <- inputUInt @4 Public
              return $ x `gt` y

        forAll genPair $ \(x, y) -> do
          if x > y
            then runAll gf181Info (program (fromInteger y)) [fromInteger x :: GF181] [] [1]
            else runAll gf181Info (program (fromInteger y)) [fromInteger x :: GF181] [] [0]

      it "gt (constant / variable)" $ do
        let genPair = (,) <$> choose (0, 15) <*> choose (0, 15)
        let program x = do
              y <- inputUInt @4 Public
              return $ x `gt` y

        forAll genPair $ \(x, y) -> do
          if x > y
            then runAll gf181Info (program (fromInteger x)) [fromInteger y :: GF181] [] [1]
            else runAll gf181Info (program (fromInteger x)) [fromInteger y :: GF181] [] [0]

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
              x <- input Public :: Comp (UInt 2)
              y <- input Public
              return $ cond true x y
        runAll gf181Info program [5, 6 :: GF181] [] [5]

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
        runAll gf181Info program [5, 6 :: GF181] [] [0]
        runAll gf181Info program [4, 4 :: GF181] [] [1]

      it "neq 1" $ do
        let program = do
              x <- inputUInt @4 Public
              y <- inputUInt @4 Public
              return (x `neq` y)
        runAll gf181Info program [5, 6 :: GF181] [] [1]
        runAll gf181Info program [4, 4 :: GF181] [] [0]

      it "neq 2" $ do
        let program = do
              x <- inputUInt @4 Public
              return (x `neq` 3)
        runAll gf181Info program [5 :: GF181] [] [1]
        runAll gf181Info program [3 :: GF181] [] [0]

      it "neq 3" $ do
        let program = do
              x <- inputUInt @4 Public
              assert $ x `neq` 3
        runAll gf181Info program [5 :: GF181] [] []
        throwAll
          gf181Info
          program
          [3 :: GF181]
          []
          (Interpreter.SyntaxTreeError $ SyntaxTree.AssertionError "¬ ($UI₄0 = 3)")
          (InterpretError (Interpreter.R1CSError $ R1CS.R1CInconsistentError $ R1C (Left 0) (Left 0) (Left 1)))

      it "neq 4" $ do
        let program = do
              assert $ 3 `neq` (3 :: UInt 4)
        throwAll
          gf181Info
          program
          []
          ([] :: [GF181])
          (Interpreter.SyntaxTreeError $ SyntaxTree.AssertionError "¬ (3 = 3)")
          (CompileError (Compiler.ConflictingValuesB True False))

    describe "Bitwise" $ do
      it "rotate" $ do
        let program = do
              x <- inputUInt @4 Public
              return [rotate x (-4), rotate x (-3), rotate x (-2), rotate x (-1), rotate x 0, rotate x 1, rotate x 2, rotate x 3, rotate x 4]

        runAll gf181Info program [0 :: GF181] [] [0, 0, 0, 0, 0, 0, 0, 0, 0]
        runAll gf181Info program [1 :: GF181] [] [1, 2, 4, 8, 1, 2, 4, 8, 1]
        runAll gf181Info program [3 :: GF181] [] [3, 6, 12, 9, 3, 6, 12, 9, 3]
        runAll gf181Info program [5 :: GF181] [] [5, 10, 5, 10, 5, 10, 5, 10, 5]

      it "shift" $ do
        let program = do
              x <- inputUInt @4 Public
              return [x .<<. (-4), x .>>. 3, shift x (-2), shift x (-1), shift x 0, shift x 1, shift x 2, shift x 3, shift x 4]

        runAll gf181Info program [0 :: GF181] [] [0, 0, 0, 0, 0, 0, 0, 0, 0]
        runAll gf181Info program [1 :: GF181] [] [0, 0, 0, 0, 1, 2, 4, 8, 0]
        runAll gf181Info program [3 :: GF181] [] [0, 0, 0, 1, 3, 6, 12, 8, 0]
        runAll gf181Info program [5 :: GF181] [] [0, 0, 1, 2, 5, 10, 4, 8, 0]

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