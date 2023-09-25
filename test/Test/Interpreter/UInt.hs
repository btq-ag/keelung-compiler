{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

module Test.Interpreter.UInt (tests, run) where

import Data.Bits qualified
import Keelung hiding (compile)
import Keelung.Compiler (Error (..))
import Keelung.Compiler.Compile.Error qualified as Compiler
import Keelung.Interpreter qualified as Interpreter
import Keelung.Interpreter.Arithmetics qualified as Arithmetics
import Keelung.Interpreter.Arithmetics qualified as U
import Keelung.Solver qualified as Solver
import Test.Hspec
import Test.Interpreter.UInt.Addition qualified as Addition
import Test.Interpreter.UInt.CLMul qualified as CLMul
import Test.Interpreter.UInt.Comparison qualified as Comparison
import Test.Interpreter.UInt.DivMod qualified as DivMod
import Test.Interpreter.UInt.ModInv qualified as ModInv
import Test.Interpreter.UInt.Multiplication qualified as Multiplication
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
        runAll (Prime 257) program [300] [] [300]

    describe "Arithmetics" $ do
      Addition.tests

      Multiplication.tests
      CLMul.tests

      DivMod.tests
      Comparison.tests
      ModInv.tests

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

        runAll gf181 program [100, 1, 1] [] [101]
        runAll gf181 program [100, 0, 1] [] [102]

      it "add + assertion" $ do
        let program = do
              x <- inputUInt @4 Public
              assert $ 2 `eq` (x + 1)
        runAll gf181 program [1] [] []

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
        -- runAll (Prime 13) program [0] [] [0]
        -- runAll (Prime 13) program [4, 4] [] [1]
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

    describe "Logical" $ do
      describe "complement" $ do
        it "variable / byte / Prime 13" $ do
          let program = do
                x <- inputUInt @8 Public
                return $ complement x
          forAll (choose (0, 255)) $ \x -> do
            let uint = U.new 8 x
            let expected = [Arithmetics.uintValue (Data.Bits.complement uint)]
            runAll (Prime 13) program [Arithmetics.uintValue uint] [] expected

        it "constant / byte / Prime 13" $ do
          let program x = do
                return $ complement (x :: UInt 8)
          forAll (choose (0, 255)) $ \x -> do
            let uint = U.new 8 x
            let expected = [Arithmetics.uintValue (Data.Bits.complement uint)]
            runAll (Prime 13) (program (fromInteger x)) [] [] expected

      describe "conjunction" $ do
        it "2 variables / byte / Prime 13" $ do
          let program = do
                x <- inputUInt @8 Public
                y <- inputUInt @8 Public
                return $ x .&. y
          forAll
            ( do
                x <- choose (0, 255)
                y <- choose (0, 255)
                return (x, y)
            )
            $ \(x, y) -> do
              let expected = [x Data.Bits..&. y]
              runAll (Prime 13) program [x, y] [] expected

        it "3 variables / byte / Prime 13" $ do
          let program = do
                x <- inputUInt @8 Public
                y <- inputUInt @8 Public
                z <- inputUInt @8 Public
                return $ x .&. y .&. z
          forAll
            ( do
                x <- choose (0, 255)
                y <- choose (0, 255)
                z <- choose (0, 255)
                return (x, y, z)
            )
            $ \(x, y, z) -> do
              let expected = [x Data.Bits..&. y Data.Bits..&. z]
              runAll (Prime 13) program [x, y, z] [] expected

        it "variables with constants / byte / Prime 13" $ do
          let program = do
                x <- inputUInt @8 Public
                y <- inputUInt @8 Public
                z <- inputUInt @8 Public
                return $ x .&. y .&. z .&. 3
          forAll
            ( do
                x <- choose (0, 255)
                y <- choose (0, 255)
                z <- choose (0, 255)
                return (x, y, z)
            )
            $ \(x, y, z) -> do
              let expected = [x Data.Bits..&. y Data.Bits..&. z Data.Bits..&. 3]
              runAll (Prime 13) program [x, y, z] [] expected

      describe "disjunction" $ do
        it "2 variables / byte / Prime 13" $ do
          let program = do
                x <- inputUInt @8 Public
                y <- inputUInt @8 Public
                return $ x .|. y
          forAll
            ( do
                x <- choose (0, 255)
                y <- choose (0, 255)
                return (x, y)
            )
            $ \(x, y) -> do
              let expected = [x Data.Bits..|. y]
              runAll (Prime 13) program [x, y] [] expected

        it "3 variables / byte / Prime 13" $ do
          let program = do
                x <- inputUInt @8 Public
                y <- inputUInt @8 Public
                z <- inputUInt @8 Public
                return $ x .|. y .|. z
          forAll
            ( do
                x <- choose (0, 255)
                y <- choose (0, 255)
                z <- choose (0, 255)
                return (x, y, z)
            )
            $ \(x, y, z) -> do
              let expected = [x Data.Bits..|. y Data.Bits..|. z]
              runAll (Prime 13) program [x, y, z] [] expected

        it "variables with constants / byte / Prime 13" $ do
          let program = do
                x <- inputUInt @8 Public
                y <- inputUInt @8 Public
                z <- inputUInt @8 Public
                return $ x .|. y .|. z .|. 3
          forAll
            ( do
                x <- choose (0, 255)
                y <- choose (0, 255)
                z <- choose (0, 255)
                return (x, y, z)
            )
            $ \(x, y, z) -> do
              let expected = [x Data.Bits..|. y Data.Bits..|. z Data.Bits..|. 3]
              runAll (Prime 13) program [x, y, z] [] expected

      describe "exclusive disjunction" $ do
        it "2 variables / byte / Prime 13" $ do
          let program = do
                x <- inputUInt @8 Public
                y <- inputUInt @8 Public
                return $ x .^. y
          forAll
            ( do
                x <- choose (0, 255)
                y <- choose (0, 255)
                return (x, y)
            )
            $ \(x, y) -> do
              let expected = [Data.Bits.xor x y]
              runAll (Prime 13) program [x, y] [] expected

        it "3 variables / byte / Prime 13" $ do
          let program = do
                x <- inputUInt @8 Public
                y <- inputUInt @8 Public
                z <- inputUInt @8 Public
                return $ x .^. y .^. z
          forAll
            ( do
                x <- choose (0, 255)
                y <- choose (0, 255)
                z <- choose (0, 255)
                return (x, y, z)
            )
            $ \(x, y, z) -> do
              let expected = [x `Data.Bits.xor` y `Data.Bits.xor` z]
              runAll (Prime 13) program [x, y, z] [] expected

        it "variables with constants / byte / Prime 13" $ do
          let program = do
                x <- inputUInt @8 Public
                y <- inputUInt @8 Public
                z <- inputUInt @8 Public
                return $ x .^. y .^. z .^. 3
          forAll
            ( do
                x <- choose (0, 255)
                y <- choose (0, 255)
                z <- choose (0, 255)
                return (x, y, z)
            )
            $ \(x, y, z) -> do
              let expected = [x `Data.Bits.xor` y `Data.Bits.xor` z `Data.Bits.xor` 3]
              runAll (Prime 13) program [x, y, z] [] expected

    describe "Bitwise" $ do
      it "rotate" $ do
        let program = do
              x <- inputUInt @4 Public
              return [rotate x (-4), rotate x (-3), rotate x (-2), rotate x (-1), rotate x 0, rotate x 1, rotate x 2, rotate x 3, rotate x 4]

        runAll gf181 program [0] [] [0, 0, 0, 0, 0, 0, 0, 0, 0]
        runAll gf181 program [1] [] [1, 2, 4, 8, 1, 2, 4, 8, 1]
        runAll gf181 program [3] [] [3, 6, 12, 9, 3, 6, 12, 9, 3]
        runAll gf181 program [5] [] [5, 10, 5, 10, 5, 10, 5, 10, 5]

      it "shift" $ do
        let program = do
              x <- inputUInt @4 Public
              return [x .<<. (-4), x .>>. 3, shift x (-2), shift x (-1), shift x 0, shift x 1, shift x 2, shift x 3, shift x 4]

        runAll gf181 program [0] [] [0, 0, 0, 0, 0, 0, 0, 0, 0]
        runAll gf181 program [1] [] [0, 0, 0, 0, 1, 2, 4, 8, 0]
        runAll gf181 program [3] [] [0, 0, 0, 1, 3, 6, 12, 8, 0]
        runAll gf181 program [5] [] [0, 0, 1, 2, 5, 10, 4, 8, 0]

      it "Bit test / literal" $ do
        -- 0011
        let program = do
              let c = 3 :: UInt 4
              return [c !!! (-1), c !!! 0, c !!! 1, c !!! 2, c !!! 3, c !!! 4]
        runAll gf181 program [] [] [0, 1, 1, 0, 0, 1]

      it "Bit test / input var" $ do
        let program = do
              c <- input Private :: Comp (UInt 4)
              return [c !!! (-1), c !!! 0, c !!! 1, c !!! 2, c !!! 3, c !!! 4]
        runAll gf181 program [] [3] [0, 1, 1, 0, 0, 1]
        runAll gf181 program [] [5] [0, 1, 0, 1, 0, 1]

      it "Bit test / and 1" $ do
        let program = do
              x <- inputUInt @4 Public
              y <- inputUInt @4 Private
              return $ (x .&. y) !!! 0
        runAll gf181 program [2] [3] [0]
        runAll gf181 program [3] [5] [1]

      it "Bit test / and 2" $ do
        let program = do
              x <- inputUInt @4 Public
              y <- inputUInt @4 Private
              z <- inputUInt @4 Public
              return $ (x .&. y .&. z) !!! 0
        runAll gf181 program [2, 4] [3] [0]
        runAll gf181 program [3, 7] [5] [1]

      it "Bit test / or 1" $ do
        let program = do
              x <- inputUInt @4 Public
              y <- inputUInt @4 Private
              return $ (x .|. y) !!! 1
        runAll gf181 program [2] [3] [1]
        runAll gf181 program [3] [5] [1]
        runAll gf181 program [5] [9] [0]

      it "Bit test / or 2" $ do
        let program = do
              x <- inputUInt @4 Public
              return $ (x .|. 3) !!! 2
        runAll gf181 program [2] [] [0]
        runAll gf181 program [3] [] [0]
        runAll gf181 program [5] [] [1]

      it "Bit test / xor 0" $ do
        let program = do
              x <- inputUInt @4 Public
              y <- inputUInt @4 Private
              let w = x .^. y .^. 0
              return [w !!! 0]
        runAll gf181 program [2] [3] [1]

      it "Bit test / xor 1" $ do
        let program = do
              x <- inputUInt @4 Public
              y <- inputUInt @4 Private
              z <- inputUInt @4 Public
              w <- reuse $ x .^. y .^. z
              return [w !!! 0, w !!! 1, w !!! 2, w !!! 3]
        runAll gf181 program [2, 4] [3] [1, 0, 1, 0]
        runAll gf181 program [3, 7] [5] [1, 0, 0, 0]

      it "Bit test / BtoU" $ do
        let program = do
              x <- input Public
              let u = BtoU x :: UInt 4
              return [u !!! 0, u !!! 1, u !!! 2, u !!! 3]
        runAll gf181 program [0] [] [0, 0, 0, 0]
        runAll gf181 program [1] [] [1, 0, 0, 0]

      it "Bit test / rotate 1" $ do
        let program = do
              x <- inputUInt @4 Public
              return $ (x `rotate` 0) !!! 0
        runAll gf181 program [2] [] [0]

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
        runAll gf181 program [2, 3] [] [0, 0, 1, 1]