{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

module Test.Compilation.UInt.Addition (tests, run) where

import Control.Monad (replicateM)
import Data.Sequence qualified as Seq
import Keelung hiding (compile)
import Keelung.Compiler.Compile.Util
import Keelung.Data.Limb qualified as Limb
import Keelung.Data.Reference (RefU (RefUX))
import Test.Compilation.Util
import Test.Hspec
import Test.QuickCheck

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests = do
  describe "Limb Bound Calculation" $ do
    it "0" $ do
      let limbs = (0, Seq.fromList [Limb.new (RefUX 2 0) 2 0 (Left True), Limb.new (RefUX 2 0) 2 0 (Left True)])
      uncurry calculateBounds limbs `shouldBe` (0, 6)
      uncurry (calculateCarrySigns 2) limbs `shouldBe` [True]

    it "1" $ do
      let limbs = (3, Seq.fromList [Limb.new (RefUX 2 0) 2 0 (Left True), Limb.new (RefUX 2 0) 2 0 (Left True)])
      uncurry calculateBounds limbs `shouldBe` (3, 9)
      uncurry (calculateCarrySigns 2) limbs `shouldBe` [True, True]

    it "2" $ do
      let limbs = (0, Seq.fromList [Limb.new (RefUX 2 0) 2 0 (Left True), Limb.new (RefUX 2 0) 2 0 (Left False)])
      uncurry calculateBounds limbs `shouldBe` (-3, 3)
      uncurry (calculateCarrySigns 2) limbs `shouldBe` [False]

    it "3" $ do
      let limbs = (1, Seq.fromList [Limb.new (RefUX 2 0) 2 0 (Left True), Limb.new (RefUX 2 0) 2 0 (Left True), Limb.new (RefUX 2 0) 2 0 (Right [False, True])])
      uncurry calculateBounds limbs `shouldBe` (0, 9)
      uncurry (calculateCarrySigns 2) limbs `shouldBe` [True, True]

    it "4" $ do
      let limbs = (3, Seq.fromList [Limb.new (RefUX 2 0) 2 0 (Left True), Limb.new (RefUX 2 0) 2 0 (Left True), Limb.new (RefUX 2 0) 2 0 (Left False), Limb.new (RefUX 2 0) 2 0 (Right [False, True])])
      uncurry calculateBounds limbs `shouldBe` (-1, 11)
      uncurry (calculateCarrySigns 2) limbs `shouldBe` [False, True]

    it "5" $ do
      let limbs = (3, Seq.fromList [Limb.new (RefUX 2 0) 2 0 (Left False), Limb.new (RefUX 2 0) 2 0 (Left True), Limb.new (RefUX 2 0) 2 0 (Left False), Limb.new (RefUX 2 0) 2 0 (Right [False, True])])
      uncurry calculateBounds limbs `shouldBe` (-4, 8)
      uncurry (calculateCarrySigns 2) limbs `shouldBe` [False, True]

    it "5" $ do
      let limbs = (3, Seq.fromList [Limb.new (RefUX 2 0) 2 0 (Left False), Limb.new (RefUX 2 0) 2 0 (Left False), Limb.new (RefUX 2 0) 2 0 (Left False), Limb.new (RefUX 2 0) 2 0 (Right [False, True])])
      uncurry calculateBounds limbs `shouldBe` (-7, 5)
      uncurry (calculateCarrySigns 2) limbs `shouldBe` [True, False]

    it "6" $ do
      let limbs = (0, Seq.fromList [Limb.new (RefUX 2 0) 2 0 (Left False), Limb.new (RefUX 2 0) 2 0 (Left False)])
      uncurry calculateBounds limbs `shouldBe` (-6, 0)
      uncurry (calculateCarrySigns 2) limbs `shouldBe` [True, False]

    it "7" $ do
      let limbs = (0, Seq.fromList [Limb.new (RefUX 2 0) 2 0 (Left True), Limb.new (RefUX 2 0) 2 0 (Left True), Limb.new (RefUX 2 0) 2 0 (Left True), Limb.new (RefUX 2 0) 2 0 (Left False)])
      uncurry calculateBounds limbs `shouldBe` (-3, 9)
      uncurry (calculateCarrySigns 2) limbs `shouldBe` [False, True]

    it "8" $ do
      let limbs = (0, Seq.fromList [Limb.new (RefUX 2 0) 2 0 (Left True), Limb.new (RefUX 2 0) 2 0 (Left True), Limb.new (RefUX 2 0) 2 0 (Left True), Limb.new (RefUX 2 0) 2 0 (Left False)])
      uncurry calculateBounds limbs `shouldBe` (-3, 9)
      uncurry (calculateCarrySigns 2) limbs `shouldBe` [False, True]

    it "9" $ do
      let limbs = (0, Seq.fromList [Limb.new (RefUX 2 0) 2 0 (Left True), Limb.new (RefUX 2 0) 2 0 (Left True), Limb.new (RefUX 2 0) 2 0 (Left True), Limb.new (RefUX 2 0) 2 0 (Right [False, True])])
      uncurry calculateBounds limbs `shouldBe` (-1, 11)
      uncurry (calculateCarrySigns 2) limbs `shouldBe` [False, True]

    it "10" $ do
      let limbs = (0, Seq.fromList [Limb.new (RefUX 2 0) 2 0 (Left True), Limb.new (RefUX 2 0) 2 0 (Left True), Limb.new (RefUX 2 0) 2 0 (Left False), Limb.new (RefUX 2 0) 2 0 (Left False)])
      uncurry calculateBounds limbs `shouldBe` (-6, 6)
      uncurry (calculateCarrySigns 2) limbs `shouldBe` [True, False]

    it "11" $ do
      let limbs = (3, Seq.fromList [Limb.new (RefUX 2 0) 1 0 (Left False), Limb.new (RefUX 2 0) 2 0 (Left False), Limb.new (RefUX 2 0) 2 0 (Left True)])
      uncurry calculateBounds limbs `shouldBe` (-1, 6)
      uncurry (calculateCarrySigns 2) limbs `shouldBe` [False, True]

    it "12" $ do
      let limbs = (0, Seq.fromList [Limb.new (RefUX 180 0) 178 0 (Left True), Limb.new (RefUX 180 0) 178 0 (Left True)])
      uncurry calculateBounds limbs `shouldBe` (0, 2 ^ (179 :: Int) - 2)
      uncurry (calculateCarrySigns 178) limbs `shouldBe` [True]

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
        runAll (Prime 17) program xs [] expected

    it "more than 4 positive variables" $ do
      let program n = do
            x <- inputUInt @4 Public
            return $ sum (replicate (fromInteger n) x)
      forAll (choose (4, 10)) $ \n -> do
        let expected = [n * n `mod` 16]
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
        runAll (Prime 17) program [x, y, z] [] expected

    it "more than 4 positive variables / constant" $ do
      let program n = do
            x <- inputUInt @4 Public
            return $ sum (replicate (fromInteger n) x) + 3
      forAll (choose (4, 10)) $ \n -> do
        let expected = [(n * n + 3) `mod` 16]
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
        runAll (Prime 17) program [x, y, z, w] [] expected

    it "3 positive / 1 negative variables (negative result)" $ do
      let program = do
            x <- inputUInt @4 Public
            y <- inputUInt @4 Public
            z <- inputUInt @4 Public
            w <- inputUInt @4 Public
            return $ x + y + z - w

      let genPair = do
            x <- choose (0, 1)
            y <- choose (0, 1)
            z <- choose (0, 12)
            w <- choose (x, 15)
            return (x, y, w, z)
      forAll genPair $ \(x, y, z, w) -> do
        let expected = [(x + y + z - w) `mod` 16]
        runAll (Prime 17) program [x, y, z, w] [] expected

    -- runAll (Prime 17) program [0, 1, 0, 3] [] expected
    -- runAll (Prime 17) program [0, 1, 0, 1] [] [0]

    -- debug  (Prime 17) program
    -- runAll (Prime 17) program [0, 1, 0, 2] [] [15]

    -- runAll gf181 program [0, 1, 0, 2] [] [15]

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
        runAll (Prime 17) program [x, y, z, w] [] expected

    it "more than 2 mixed (positive / negative / constant) / UInt 4" $ do
      let program constant signs = do
            inputs <- replicateM (length signs) (inputUInt @4 Public)
            return $ constant + sum (zipWith (\sign x -> if sign then x else -x) signs inputs)
      let genPair = do
            n <- choose (2, 10)
            signs <- replicateM n $ do
              sign <- arbitrary
              x <- chooseInteger (0, 255)
              return (sign, x)
            constant <- chooseInteger (0, 255)
            return (constant, signs)
      forAll genPair $ \(constant, pairs) -> do
        let (signs, values) = unzip pairs
        let expected = [(constant + sum (zipWith (\sign x -> if sign then x else -x) signs values)) `mod` 16]
        runAll (Prime 17) (program (fromInteger constant) signs) values [] expected