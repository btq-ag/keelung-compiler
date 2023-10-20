{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Compilation.UInt.Misc (tests, run) where

import Keelung hiding (compile)
import Test.Compilation.Util
import Test.Hspec
import Test.QuickCheck

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests = describe "UInt arithmetics" $ do
  describe "Addition / Subtraction" $ do
    it "2 positive variables / UInt 2" $ do
      let program = do
            x <- inputUInt @2 Public
            y <- inputUInt @2 Public
            return $ x + y
      let genPair = do
            x <- chooseInteger (0, 3)
            y <- chooseInteger (0, 3)
            return (x, y)
      forAll genPair $ \(x, y) -> do
        let expected = [(x + y) `mod` 4]
        runAll (Binary 5) program (map toInteger [x, y]) [] expected

    it "2 positive variables / Byte" $ do
      let program = do
            x <- inputUInt @8 Public
            y <- inputUInt @8 Public
            return $ x + y
      let genPair = do
            x <- chooseInteger (0, 255)
            y <- chooseInteger (0, 255)
            return (x, y)
      forAll genPair $ \(x, y) -> do
        let expected = [(x + y) `mod` 256]
        runAll (Binary 5) program (map toInteger [x, y]) [] expected

    it "1 positive variable + 1 negative variable / Byte" $ do
      let program = do
            x <- inputUInt @8 Public
            y <- inputUInt @8 Public
            return $ x - y
      let genPair = do
            x <- chooseInteger (0, 255)
            y <- chooseInteger (0, 255)
            return (x, y)
      forAll genPair $ \(x, y) -> do
        let expected = [(x - y) `mod` 256]
        runAll (Binary 5) program (map toInteger [x, y]) [] expected

    it "1 positive variable + 1 constant / Byte" $ do
      let program y = do
            x <- inputUInt @8 Public
            return $ x + y
      let genPair = do
            x <- chooseInteger (0, 255)
            y <- chooseInteger (0, 255)
            return (x, y)
      forAll genPair $ \(x, y) -> do
        let expected = [(x + y) `mod` 256]
        runAll (Binary 5) (program (fromInteger y)) (map toInteger [x]) [] expected

    it "1 negative variable + 1 constant / Byte" $ do
      let program y = do
            x <- inputUInt @8 Public
            return $ - x + y
      let genPair = do
            x <- chooseInteger (0, 255)
            y <- chooseInteger (0, 255)
            return (x, y)
      forAll genPair $ \(x, y) -> do
        let expected = [(y - x) `mod` 256]
        runAll (Binary 5) (program (fromInteger y)) (map toInteger [x]) [] expected