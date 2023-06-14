{-# LANGUAGE DataKinds #-}

module Test.Interpreter.UInt.Addition (tests, run) where

import Data.Field.Galois (Prime)
import Keelung hiding (compile)
import Keelung.Compiler (Error (..))
import Keelung.Compiler.Compile.Error qualified as CompilerError
import Test.Hspec
import Test.Interpreter.Util
import Test.QuickCheck hiding ((.&.))

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests =
  describe "Addition / Subtraction" $ do
    it "variable / variable" $ do
      let program = do
            x <- inputUInt @4 Public
            y <- inputUInt @4 Public
            return $ x + y
      -- debugPrime (Prime 13) program
      -- runPrime (Prime 13) program [3, 10] [] [13]
      let genPair = do
            x <- choose (0, 15)
            y <- choose (0, 15)
            return (x, y)
      forAll genPair $ \(x, y) -> do
        let expected = [(x + y) `mod` 16]
        runPrime (Prime 13) program [x, y] [] expected

    it "should throw `FieldTooSmall`" $ do
      let program = do
            x <- inputUInt @4 Public
            y <- inputUInt @4 Public
            z <- inputUInt @4 Public
            return $ x + y + z + 2 + 3
      throwPrimeR1CS (Prime 7) program [1, 2, 3] [] (CompileError (CompilerError.FieldTooSmall (Prime 7) 3) :: Error (Prime 7))

    it "variables and constants with subtraction" $ do
      let program = do
            x <- inputUInt @4 Public
            y <- inputUInt @4 Public
            z <- inputUInt @4 Public
            return $ x + y - z + 2 + 3 + 16
      -- debugPrime (Prime 31) program
      -- runPrime (Prime 31) program [5, 2, 13] [] [15]
      let genPair = do
            x <- choose (0, 15)
            y <- choose (0, 15)
            z <- choose (0, 15)
            return (x, y, z)
      forAll genPair $ \(x, y, z) -> do
        let expected = [(x + y - z + 5) `mod` 16]
        runPrime (Prime 31) program [x, y, z] [] expected

    it "variable / constant" $ do
      let program y = do
            x <- inputUInt @4 Public
            return $ x + y
      -- debugPrime (Prime 13) (program 6)
      -- runPrime (Prime 13) (program 6) [4] [] [10]
      let genPair = do
            x <- choose (0, 15)
            y <- choose (0, 15)
            return (x, y)
      forAll genPair $ \(x, y) -> do
        let expected = [(x + y) `mod` 16]
        runPrime (Prime 13) (program (fromInteger y)) [x `mod` 16] [] expected

    it "constant / constant" $ do
      let program x y = do
            return $ x + (y :: UInt 4)
      let genPair = do
            x <- choose (0, 15)
            y <- choose (0, 15)
            return (x, y)
      forAll genPair $ \(x, y) -> do
        let expected = [(x + y) `mod` 16]
        runPrime (Prime 13) (program (fromInteger x) (fromInteger y)) [] [] expected

    it "10 bit / GF257" $ do
      let program = do
            x <- inputUInt @10 Public
            y <- inputUInt @10 Public
            return $ x + y
      -- debugPrime (Prime 257) program
      runPrime (Prime 13) program [100, 200] [] [300]