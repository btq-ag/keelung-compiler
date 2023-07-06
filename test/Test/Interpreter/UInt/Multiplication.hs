{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

module Test.Interpreter.UInt.Multiplication (tests, run) where

import Keelung hiding (compile)
import Test.Hspec
import Test.Interpreter.Util
import Test.QuickCheck hiding ((.&.))

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests =
  describe "Multiplication" $ do
    it "Constants only" $ do
      let program x y = do
            return $ x * (y :: UInt 6)
      let genPair = do
            x <- choose (-63, 63)
            y <- choose (-63, 63)
            return (x, y)
      forAll genPair $ \(x, y) -> do
        let expected = [(x * y) `mod` 64]
        runAll (Prime 5) (program (fromInteger x) (fromInteger y)) [] [] expected
        runAll (Prime 257) (program (fromInteger x) (fromInteger y)) [] [] expected

    it "1-limb x 1-limb" $ do
      let program = do
            x <- inputUInt @4 Public
            y <- inputUInt @4 Public
            return $ x * y
      -- debug (Prime 1031) program
      let genPair = do
            x <- choose (-15, 15)
            y <- choose (-15, 15)
            return (x, y)

      forAll genPair $ \(x, y) -> do
        let expected = [(x * y) `mod` 16]
        runAll (Prime 1031) program [x, y] [] expected

    it "1-limb variable x 1-limb constant" $ do
      let program y = do
            x <- inputUInt @4 Public
            return $ x * fromInteger y
      let genPair = do
            x <- choose (-15, 15)
            y <- choose (-15, 15)
            return (x, y)
      forAll genPair $ \(x, y) -> do
        let expected = [(x * y) `mod` 16]
        runAll (Prime 1031) (program y) [x] [] expected
    --   runAll (Prime 17) (program y) [x] [] expected

    it "2-limb x 2-limb" $ do
      let program = do
            x <- inputUInt @4 Public
            y <- inputUInt @4 Public
            return $ x * y
      -- debug (Prime 17) program
      -- runAll (Prime 17) program [10, 2] [] [4]
      let genPair = do
            x <- choose (-15, 15)
            y <- choose (-15, 15)
            return (x, y)
      forAll genPair $ \(x, y) -> do
        let expected = [(x * y) `mod` 16]
        runAll (Prime 17) program [x, y] [] expected

    it "2-limb variable x 2-limb constant" $ do
      let program y = do
            x <- inputUInt @4 Public
            return $ x * fromInteger y
      -- runAll (Prime 17) (program 0) [10] [] [0]
      let genPair = do
            x <- choose (-15, 15)
            y <- choose (-15, 15)
            return (x, y)
      forAll genPair $ \(x, y) -> do
        let expected = [(x * y) `mod` 16]
        runAll (Prime 1031) (program y) [x] [] expected
        runAll (Prime 17) (program y) [x] [] expected

    it "3-limb x 3-limb" $ do
      let program = do
            x <- inputUInt @6 Public
            y <- inputUInt @6 Public
            return $ x * y
      -- debug (Prime 1031) program
      -- runAll (Prime 1031) program [10, 20] [] [8]
      let genPair = do
            x <- choose (-63, 63)
            y <- choose (-63, 63)
            return (x, y)
      forAll genPair $ \(x, y) -> do
        let expected = [(x * y) `mod` 64]
        runAll (Prime 17) program [x, y] [] expected

    it "3-limb variable x 3-limb constant" $ do
      let program y = do
            x <- inputUInt @6 Public
            return $ x * fromInteger y
      let genPair = do
            x <- choose (-63, 63)
            y <- choose (-63, 63)
            return (x, y)
      forAll genPair $ \(x, y) -> do
        let expected = [(x * y) `mod` 64]
        runAll (Prime 17) (program y) [x] [] expected

--     it "Byte / GF(1031)" $ do

--       let program y = do
--             x <- inputUInt @32 Public
--             return $ x * fromInteger y
--       debug (Prime 1031) (program 1)
      -- let genPair = do
      --       x <- (arbitrary :: Gen Int)
      --       y <- (arbitrary :: Gen Int)
      --       return (toInteger x, toInteger y)
      -- forAll genPair $ \(x, y) -> do
      --   let expected = [(x * y) `mod` (2 ^ 32)]
      --   runAll (Prime 17) (program y) [x] [] expected
