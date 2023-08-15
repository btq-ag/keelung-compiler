{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

module Test.Interpreter.UInt.Addition (tests, run) where

import Control.Monad (replicateM)
import Keelung hiding (compile)
import Test.Hspec
import Test.Interpreter.Util
import Test.QuickCheck

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests =
  describe "Addition / Subtraction" $ do
    it "2 positive variables" $ do
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
        -- runAll (Prime 5) program [x, y] [] expected
        -- runAll (Prime 11) program [x, y] [] expected
        runAll (Prime 17) program [x, y] [] expected

    it "3 positive variables" $ do
      let program = do
            x <- inputUInt @4 Public
            y <- inputUInt @4 Public
            z <- inputUInt @4 Public
            return $ x + y + z
      -- debug (Prime 17) program
      forAll (replicateM 3 (choose (0, 15))) $ \xs -> do
        let expected = [sum xs `mod` 16]
        -- runAll (Prime 5) program xs [] expected
        -- runAll (Prime 11) program xs [] expected
        runAll (Prime 17) program xs [] expected

    it "more than 4 positive variables" $ do
      let program n = do
            x <- inputUInt @4 Public
            return $ sum (replicate (fromInteger n) x)
      forAll (choose (4, 10)) $ \n -> do
        let expected = [n * n `mod` 16]
        -- runAll (Prime 5) (program n) [n] [] expected
        -- runAll (Prime 11) (program n) [n] [] expected
        runAll (Prime 17) (program n) [n] [] expected

    it "2 positive variables / constant" $ do
      let program = do
            x <- inputUInt @2 Public
            y <- inputUInt @2 Public
            return $ x + y + 3
      let genPair = do
            x <- choose (0, 3)
            y <- choose (0, 3)
            return (x, y)
      forAll genPair $ \(x, y) -> do
        let expected = [(x + y + 3) `mod` 4]
        -- runAll (Prime 5) program [x, y] [] expected
        -- runAll (Prime 11) program [x, y] [] expected
        runAll (Prime 17) program [x, y] [] expected

    it "3 positive variables / constant" $ do
      let program = do
            x <- inputUInt @2 Public
            y <- inputUInt @2 Public
            z <- inputUInt @2 Public
            return $ x + y + z + 3
      let genPair = do
            x <- choose (0, 3)
            y <- choose (0, 3)
            z <- choose (0, 3)
            return (x, y, z)
      forAll genPair $ \(x, y, z) -> do
        let expected = [(x + y + z + 3) `mod` 4]
        -- runAll (Prime 5) program [x, y, z] [] expected
        -- runAll (Prime 11) program [x, y, z] [] expected
        runAll (Prime 17) program [x, y, z] [] expected

    it "more than 4 positive variables / constant" $ do
      let program n = do
            x <- inputUInt @4 Public
            return $ sum (replicate (fromInteger n) x) + 3
      forAll (choose (4, 10)) $ \n -> do
        let expected = [(n * n + 3) `mod` 16]
        -- runAll (Prime 5) (program n) [n] [] expected
        -- runAll (Prime 11) (program n) [n] [] expected
        runAll (Prime 17) (program n) [n] [] expected

    it "2 mixed (positive / negative) variable" $ do
      let program = do
            x <- inputUInt @2 Public
            y <- inputUInt @2 Public
            return $ x - y
      let genPair = do
            x <- choose (0, 3)
            y <- choose (0, 3)
            return (x, y)
      forAll genPair $ \(x, y) -> do
        let expected = [(x - y) `mod` 4]
        -- runAll (Prime 5) program [x, y] [] expected
        -- runAll (Prime 11) program [x, y] [] expected
        runAll (Prime 17) program [x, y] [] expected

    it "2 mixed (positive / negative) variable" $ do
      let program = do
            x <- inputUInt @4 Public
            y <- inputUInt @4 Public
            return $ x - y
      -- debug (Prime 17) program
      -- runAll (Prime 17) program [3, 13] [] [6]
      let genPair = do
            x <- choose (0, 15)
            y <- choose (0, 15)
            return (x, y)
      forAll genPair $ \(x, y) -> do
        let expected = [(x - y) `mod` 16]
        -- runAll (Prime 5) program [x, y] [] expected
        -- runAll (Prime 11) program [x, y] [] expected
        runAll (Prime 17) program [x, y] [] expected

    it "3 positive / 1 negative variables" $ do
      let program = do
            x <- inputUInt @4 Public
            y <- inputUInt @4 Public
            z <- inputUInt @4 Public
            w <- inputUInt @4 Public
            return $ x + y + z - w
      let genPair = do
            x <- choose (0, 15)
            y <- choose (0, 15)
            z <- choose (0, 15)
            w <- choose (0, 15)
            return (x, y, w, z)
      forAll genPair $ \(x, y, z, w) -> do
        let expected = [(x + y + z - w) `mod` 16]
        -- runAll (Prime 5) program [x, y, z, w] [] expected
        -- runAll (Prime 11) program [x, y, z, w] [] expected
        runAll (Prime 17) program [x, y, z, w] [] expected

    it "2 positive / 2 negative variables" $ do
      let program = do
            x <- inputUInt @10 Public
            y <- inputUInt @10 Public
            z <- inputUInt @10 Public
            w <- inputUInt @10 Public
            return $ x + y - z - w
      let genPair = do
            x <- choose (0, 1023)
            y <- choose (0, 1023)
            z <- choose (0, 1023)
            w <- choose (0, 1023)
            return (x, y, w, z)
      forAll genPair $ \(x, y, z, w) -> do
        let expected = [(x + y - z - w) `mod` 1024]
        -- runAll (Prime 5) program [x, y, z, w] [] expected
        -- runAll (Prime 11) program [x, y, z, w] [] expected
        runAll (Prime 17) program [x, y, z, w] [] expected

    it "1 positive / 3 negative variables" $ do
      let program = do
            x <- inputUInt @4 Public
            y <- inputUInt @4 Public
            z <- inputUInt @4 Public
            w <- inputUInt @4 Public
            return $ x - y - z - w
      let genPair = do
            x <- choose (0, 15)
            y <- choose (0, 15)
            z <- choose (0, 15)
            w <- choose (0, 15)
            return (x, y, w, z)
      forAll genPair $ \(x, y, z, w) -> do
        let expected = [(x - y - z - w) `mod` 16]
        -- runAll (Prime 5) program [x, y, z, w] [] expected
        -- runAll (Prime 11) program [x, y, z, w] [] expected
        runAll (Prime 17) program [x, y, z, w] [] expected

    it "4 negative variables" $ do
      let program = do
            x <- inputUInt @10 Public
            y <- inputUInt @10 Public
            z <- inputUInt @10 Public
            w <- inputUInt @10 Public
            return $ -x - y - z - w
      let genPair = do
            x <- choose (0, 1023)
            y <- choose (0, 1023)
            z <- choose (0, 1023)
            w <- choose (0, 1023)
            return (x, y, w, z)
      forAll genPair $ \(x, y, z, w) -> do
        let expected = [(-x - y - z - w) `mod` 1024]
        -- runAll (Prime 5) program [x, y, z, w] [] expected
        -- runAll (Prime 11) program [x, y, z, w] [] expected
        runAll (Prime 17) program [x, y, z, w] [] expected

    -- it "2 negative variable" $ do
    --   let program = do
    --         x <- inputUInt @8 Public
    --         y <- inputUInt @8 Public
    --         return $ - x - y
    --   -- runAll (Prime 997) program [10, 10] [] [236]
    --   -- runAll (Prime 997) program [138, 138] [] [236]
    --   -- debug (Prime 1031) program
    --   -- debug (Prime 5) program

    --   -- runAll (Prime 5) program [10, 10] [] [236]
    --   -- runAll (Prime 5) program [10, 10] [] [12]
    --   -- runAll (Prime 7) program [11, 15] [] [6]
    --   -- runAll (Prime 7) program [10, 10] [] [12]

    --   let genPair = do
    --         x <- chooseInteger (0, 255)
    --         y <- chooseInteger (0, 255)
    --         return (x, y)
    --   forAll genPair $ \(x, y) -> do
    --     let expected = [(- x - y) `mod` 256]
    --     -- runAll (Prime 5) program [x, y] [] expected
    --     -- runAll (Prime 11) program [x, y] [] expected
    --     -- runAll (Prime 17) program [x, y] [] expected
    --     runAll (Prime 17) program [x, y] [] expected
    --     runAll (Prime 1031) program [x, y] [] expected

    it "more than 2 mixed (positive / negative) variables / constant" $ do
      let program signs = do
            inputs <- replicateM (length signs) (inputUInt @4 Public)
            return $ -4 + sum (zipWith (\sign x -> if sign then x else -x) signs inputs)
      let genPair = do
            sign <- arbitrary
            x <- chooseInteger (0, 15)
            return (sign, x)
      forAll (choose (2, 2) >>= flip replicateM genPair) $ \pairs -> do
        let (signs, values) = unzip pairs
        let expected = [(-4 + sum (zipWith (\sign x -> if sign then x else -x) signs values)) `mod` 16]
        -- runAll (Prime 5) (program signs) values [] expected
        -- runAll (Prime 11) (program signs) values [] expected
        runAll (Prime 17) (program signs) values [] expected
