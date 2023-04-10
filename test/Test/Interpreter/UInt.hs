{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

module Test.Interpreter.UInt (tests, run) where

import Control.Monad (when)
import Keelung hiding (compile, run)
import Keelung.Compiler (Error (..))
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

        runAll program [100, 1, 1 :: GF181] [] [101]
        runAll program [100, 0, 1 :: GF181] [] [102]

      it "add 1" $ do
        let program = do
              x <- inputUInt @4 Public
              y <- inputUInt @4 Public
              return $ x + y

        runAll program [5, 6 :: GF181] [] [11]
        runAll program [2, 5 :: GF181] [] [7]
        runAll program [15, 1 :: GF181] [] [0]

      it "add 2" $ do
        let program = do
              x <- inputUInt @4 Public
              y <- inputUInt @4 Public
              z <- inputUInt @4 Public
              w <- reuse $ x + y
              return $ x + y + z + w

        runAll program [5, 6, 7 :: GF181] [] [13]
        runAll program [2, 5, 3 :: GF181] [] [1]
        runAll program [0, 1, 2 :: GF181] [] [4]

      it "mul 3" $ do
        let program = do
              x <- inputUInt @4 Public
              y <- inputUInt @4 Public
              return $ x * y

        runAll program [2, 4 :: GF181] [] [8]
        runAll program [5, 6 :: GF181] [] [14]

      it "arithmetics 4" $ do
        let program = do
              x <- inputUInt @4 Public
              y <- inputUInt @4 Public
              return $ x * y + y

        runAll program [5, 6 :: GF181] [] [4]
        runAll program [2, 5 :: GF181] [] [15]
        runAll program [15, 1 :: GF181] [] [0]

      it "arithmetics 5" $ do
        let program = do
              x <- inputUInt @4 Public
              y <- reuse x
              return (x + y)
        runAllExceptForTheOldOptimizer program [5 :: GF181] [] [10]

      it "modInv 123 2833" $ do
        let program = return $ modInv (123 :: UInt 32) 2833
        runAllExceptForTheOldOptimizer program [] ([] :: [GF181]) [2119]

    describe "DivMod" $ do
      it "performDivMod (quotient & remainder unknown)" $ do
        let program = do
              dividend <- input Private :: Comp (UInt 4)
              divisor <- input Public
              performDivMod dividend divisor
        runAllExceptForTheOldOptimizer program [7 :: GF181] [20] [2, 6]
        runAllExceptForTheOldOptimizer program [4 :: GF181] [4] [1, 0]

      it "performDivMod (on constants) (issue #18)" $ do
        let program = performDivMod 7 (3 :: UInt 4)
        runAllExceptForTheOldOptimizer program [] [] [2, 1 :: GF181]

      it "assertDivMod (on constants) (issue #18)" $ do
        let program = assertDivMod 7 (3 :: UInt 4) 2 1
        runAllExceptForTheOldOptimizer program [] [] ([] :: [GF181])

      it "assertDivMod (with wrong quotient constant)" $ do
        let program = assertDivMod 7 (3 :: UInt 4) 3 1
        throwAll
          program
          []
          ([] :: [GF181])
          (Interpreter.SyntaxTreeError (SyntaxTree.DivModQuotientError 7 3 2 3))
          (InterpretError (Interpreter.R1CSError (R1CS.R1CInconsistentError 3 3 6)))
      -- (InterpretError (Interpreter.R1CSError (R1CS.DivModQuotientError 7 3 2 3)))

      it "assertDivMod (with wrong remainder constant)" $ do
        let program = assertDivMod 7 (3 :: UInt 4) 2 0
        throwAll
          program
          []
          ([] :: [GF181])
          (Interpreter.SyntaxTreeError (SyntaxTree.DivModRemainderError 7 3 1 0))
          (InterpretError (Interpreter.R1CSError (R1CS.R1CInconsistentError 3 2 7)))
      -- (InterpretError (Interpreter.R1CSError (R1CS.DivModRemainderError 7 3 1 0)))

      it "assertDivMod (multiple statements)" $ do
        let program = do
              a <- input Public :: Comp (UInt 5)
              b <- input Public
              c <- input Private
              d <- input Public
              (q0, r0) <- performDivMod a b
              (q1, r1) <- performDivMod c d
              return [q0, r0, q1, r1]
        runAllExceptForTheOldOptimizer program [20, 7, 8 :: GF181] [21] [2, 6, 2, 5]

      it "assertDivMod (multiple statements chained together)" $ do
        let program = do
              a <- input Public :: Comp (UInt 5)
              b <- input Public
              (q0, r0) <- performDivMod a b
              (q1, r1) <- performDivMod q0 b
              return [q0, r0, q1, r1]
        runAllExceptForTheOldOptimizer program [25, 3 :: GF181] [] [8, 1, 2, 2]

      it "performDivMod (before assertions)" $ do
        let program = do
              a <- input Public :: Comp (UInt 5)
              b <- input Public
              (q, r) <- performDivMod a b
              assert $ q `eq` r
        runAllExceptForTheOldOptimizer program [10, 4 :: GF181] [] []

      it "performDivMod (before reuse)" $ do
        let program = do
              a <- input Public :: Comp (UInt 5)
              b <- input Public
              (q, _) <- performDivMod a b
              reuse q
        runAllExceptForTheOldOptimizer program [10, 4 :: GF181] [] [2]

      it "performDivMod (after reuse)" $ do
        let program = do
              a <- reuse =<< input Public :: Comp (UInt 5)
              b <- input Public
              (q, r) <- performDivMod a b
              assert $ q `eq` r
        runAllExceptForTheOldOptimizer program [10, 4 :: GF181] [] []

      it "assertDivMod (dividend unknown)" $ do
        let program = do
              dividend <- freshVarUInt
              divisor <- input Public :: Comp (UInt 4)
              quotient <- input Public
              remainder <- input Private
              assertDivMod dividend divisor quotient remainder
              return dividend
        runAllExceptForTheOldOptimizer program [7, 2 :: GF181] [6] [20]

      it "assertDivMod (divisor & remainder unknown)" $ do
        let program = do
              dividend <- input Public :: Comp (UInt 4)
              divisor <- freshVarUInt
              quotient <- input Public
              remainder <- freshVarUInt
              assertDivMod dividend divisor quotient remainder
              return (divisor, remainder)
        runAllExceptForTheOldOptimizer program [7, 2 :: GF181] [] [3, 1]

      it "assertDivMod (quotient & remainder unknown)" $ do
        let program = do
              dividend <- input Public :: Comp (UInt 4)
              divisor <- input Public
              quotient <- freshVarUInt
              remainder <- freshVarUInt
              assertDivMod dividend divisor quotient remainder
              return (quotient, remainder)
        runAllExceptForTheOldOptimizer program [34, 6 :: GF181] [] [5, 4]

    describe "Range Check" $ do
      it "assertLTE (< 4)" $ do
        let program = do
              x <- inputUInt @3 Public
              assertLTE x 3
        runAllExceptForTheOldOptimizer program [0 :: GF181] [] []
        runAllExceptForTheOldOptimizer program [1 :: GF181] [] []
        runAllExceptForTheOldOptimizer program [2 :: GF181] [] []
        runAllExceptForTheOldOptimizer program [3 :: GF181] [] []
        throwAll
          program
          [4 :: GF181]
          []
          (Interpreter.SyntaxTreeError (SyntaxTree.AssertLTEError 4 3))
          (InterpretError (Interpreter.R1CSError (R1CS.R1CInconsistentError 1 (-1) 0)))
        throwAll
          program
          [5 :: GF181]
          []
          (Interpreter.SyntaxTreeError (SyntaxTree.AssertLTEError 5 3))
          (InterpretError (Interpreter.R1CSError (R1CS.R1CInconsistentError 1 (-1) 0)))
        throwAll
          program
          [6 :: GF181]
          []
          (Interpreter.SyntaxTreeError (SyntaxTree.AssertLTEError 6 3))
          (InterpretError (Interpreter.R1CSError (R1CS.R1CInconsistentError 1 (-1) 0)))
        throwAll
          program
          [7 :: GF181]
          []
          (Interpreter.SyntaxTreeError (SyntaxTree.AssertLTEError 7 3))
          (InterpretError (Interpreter.R1CSError (R1CS.R1CInconsistentError 1 (-1) 0)))

      it "assertLTE (< 5)" $ do
        let program = do
              x <- inputUInt @3 Public
              assertLTE x 4
        runAllExceptForTheOldOptimizer program [0 :: GF181] [] []
        runAllExceptForTheOldOptimizer program [1 :: GF181] [] []
        runAllExceptForTheOldOptimizer program [2 :: GF181] [] []
        runAllExceptForTheOldOptimizer program [3 :: GF181] [] []
        runAllExceptForTheOldOptimizer program [4 :: GF181] [] []
        throwAll
          program
          [5 :: GF181]
          []
          (Interpreter.SyntaxTreeError (SyntaxTree.AssertLTEError 5 4))
          (InterpretError (Interpreter.R1CSError (R1CS.R1CInconsistentError (-1) 1 0)))
        throwAll
          program
          [6 :: GF181]
          []
          (Interpreter.SyntaxTreeError (SyntaxTree.AssertLTEError 6 4))
          (InterpretError (Interpreter.R1CSError (R1CS.R1CInconsistentError (-1) 1 0)))
        throwAll
          program
          [7 :: GF181]
          []
          (Interpreter.SyntaxTreeError (SyntaxTree.AssertLTEError 7 4))
          (InterpretError (Interpreter.R1CSError (R1CS.R1CInconsistentError (-1) 1 0)))

      it "assertLTE (QuickCheck)" $ do
        let program bound = do
              x <- inputUInt @8 Public
              assertLTE x bound
        property $ \(x, b) -> do
          when (x >= 0 && x < 256 && b >= 0 && b < 256 && x <= b) $ do
            runAll (program b) [fromInteger x :: GF181] [] []
            runAll (program b) [fromInteger b :: GF181] [] []

    -- when x <= b
    -- then runAll (program b) [fromInteger x :: GF181] [] []
    -- else
    --   throwAll
    --     (program b)
    --     [fromInteger x :: GF181]
    --     []
    --     (Interpreter.SyntaxTreeError (SyntaxTree.AssertLTEError (fromInteger x) b))
    --     (InterpretError (Interpreter.R1CSError (R1CS.R1CInconsistentError (-1) 1 0)))

    it "eq" $ do
      let program = do
            x <- inputUInt @4 Public
            y <- inputUInt @4 Public
            return (x `eq` y)
      runAllExceptForTheOldOptimizer program [5, 6 :: GF181] [] [0]
      runAllExceptForTheOldOptimizer program [4, 4 :: GF181] [] [1]

    it "neq 1" $ do
      let program = do
            x <- inputUInt @4 Public
            y <- inputUInt @4 Public
            return (x `neq` y)
      runAllExceptForTheOldOptimizer program [5, 6 :: GF181] [] [1]
      runAllExceptForTheOldOptimizer program [4, 4 :: GF181] [] [0]

    it "neq 2" $ do
      let program = do
            x <- inputUInt @4 Public
            return (x `neq` 3)
      runAllExceptForTheOldOptimizer program [5 :: GF181] [] [1]
      runAllExceptForTheOldOptimizer program [3 :: GF181] [] [0]

    it "neq 3" $ do
      let program = do
            x <- inputUInt @4 Public
            assert $ x `neq` 3
      runAllExceptForTheOldOptimizer program [5 :: GF181] [] []
      throwAll
        program
        [3 :: GF181]
        []
        (Interpreter.SyntaxTreeError $ SyntaxTree.AssertionError "¬ ($UI₄0 = 3)")
        (InterpretError (Interpreter.R1CSError $ R1CS.R1CInconsistentError 0 0 1))

    it "neq 4" $ do
      let program = do
            assert $ 3 `neq` (3 :: UInt 4)
      throwAll
        program
        []
        ([] :: [GF181])
        (Interpreter.SyntaxTreeError $ SyntaxTree.AssertionError "¬ (3 = 3)")
        (InterpretError (Interpreter.R1CSError $ R1CS.R1CInconsistentError 0 0 1))

    it "rotate" $ do
      let program = do
            x <- inputUInt @4 Public
            return [rotate x (-4), rotate x (-3), rotate x (-2), rotate x (-1), rotate x 0, rotate x 1, rotate x 2, rotate x 3, rotate x 4]

      runAll program [0 :: GF181] [] [0, 0, 0, 0, 0, 0, 0, 0, 0]
      runAll program [1 :: GF181] [] [1, 2, 4, 8, 1, 2, 4, 8, 1]
      runAll program [3 :: GF181] [] [3, 6, 12, 9, 3, 6, 12, 9, 3]
      runAll program [5 :: GF181] [] [5, 10, 5, 10, 5, 10, 5, 10, 5]

    it "shift" $ do
      let program = do
            x <- inputUInt @4 Public
            return [shift x (-4), shift x (-3), shift x (-2), shift x (-1), shift x 0, shift x 1, shift x 2, shift x 3, shift x 4]

      runAll program [0 :: GF181] [] [0, 0, 0, 0, 0, 0, 0, 0, 0]
      runAll program [1 :: GF181] [] [0, 0, 0, 0, 1, 2, 4, 8, 0]
      runAll program [3 :: GF181] [] [0, 0, 0, 1, 3, 6, 12, 8, 0]
      runAll program [5 :: GF181] [] [0, 0, 1, 2, 5, 10, 4, 8, 0]

    it "Bit test / literal" $ do
      -- 0011
      let program = do
            let c = 3 :: UInt 4
            return [c !!! (-1), c !!! 0, c !!! 1, c !!! 2, c !!! 3, c !!! 4]

      runAllExceptForTheOldOptimizer program [] [] [0, 1, 1, 0, 0, 1 :: GF181]

    it "Bit test / input var" $ do
      let program = do
            c <- input Private :: Comp (UInt 4)
            return [c !!! (-1), c !!! 0, c !!! 1, c !!! 2, c !!! 3, c !!! 4]
      runAllExceptForTheOldOptimizer program [] [3] [0, 1, 1, 0, 0, 1 :: GF181]
      runAllExceptForTheOldOptimizer program [] [5] [0, 1, 0, 1, 0, 1 :: GF181]

    it "Bit test / and 1" $ do
      let program = do
            x <- inputUInt @4 Public
            y <- inputUInt @4 Private
            return $ (x .&. y) !!! 0
      runAllExceptForTheOldOptimizer program [2] [3] [0 :: GF181]
      runAllExceptForTheOldOptimizer program [3] [5] [1 :: GF181]

    it "Bit test / and 2" $ do
      let program = do
            x <- inputUInt @4 Public
            y <- inputUInt @4 Private
            z <- inputUInt @4 Public
            return $ (x .&. y .&. z) !!! 0
      runAllExceptForTheOldOptimizer program [2, 4] [3] [0 :: GF181]
      runAllExceptForTheOldOptimizer program [3, 7] [5] [1 :: GF181]

    it "Bit test / or 1" $ do
      let program = do
            x <- inputUInt @4 Public
            y <- inputUInt @4 Private
            return $ (x .|. y) !!! 1
      runAllExceptForTheOldOptimizer program [2] [3] [1 :: GF181]
      runAllExceptForTheOldOptimizer program [3] [5] [1 :: GF181]
      runAllExceptForTheOldOptimizer program [5] [9] [0 :: GF181]

    it "Bit test / or 2" $ do
      let program = do
            x <- inputUInt @4 Public
            return $ (x .|. 3) !!! 2
      runAllExceptForTheOldOptimizer program [2] [] [0 :: GF181]
      runAllExceptForTheOldOptimizer program [3] [] [0 :: GF181]
      runAllExceptForTheOldOptimizer program [5] [] [1 :: GF181]

    it "Bit test / xor 1" $ do
      let program = do
            x <- inputUInt @4 Public
            y <- inputUInt @4 Private
            z <- inputUInt @4 Public
            w <- reuse $ x .^. y .^. z
            return [w !!! 0, w !!! 1, w !!! 2, w !!! 3]
      runAllExceptForTheOldOptimizer program [2, 4] [3] [1, 0, 1, 0 :: GF181]
      runAllExceptForTheOldOptimizer program [3, 7] [5] [1, 0, 0, 0 :: GF181]

    it "Bit test / BtoU" $ do
      let program = do
            x <- input Public
            let u = BtoU x :: UInt 4
            return [u !!! 0, u !!! 1, u !!! 2, u !!! 3]
      runAllExceptForTheOldOptimizer program [0] [] [0, 0, 0, 0 :: GF181]
      runAllExceptForTheOldOptimizer program [1] [] [1, 0, 0, 0 :: GF181]

    it "Bit test / rotate 1" $ do
      let program = do
            x <- inputUInt @4 Public
            return $ (x `rotate` 0) !!! 0
      runAllExceptForTheOldOptimizer program [2] [] [0 :: GF181]

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
      runAllExceptForTheOldOptimizer program [2, 3] [] [0, 0, 1, 1 :: GF181]