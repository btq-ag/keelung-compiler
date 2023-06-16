{-# LANGUAGE DataKinds #-}

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
    it "constant / constant" $ do
      let program x y = do
            return $ x * (y :: UInt 6)
      let genPair = do
            x <- choose (0, 63)
            y <- choose (0, 63)
            return (x, y)
      forAll genPair $ \(x, y) -> do
        let expected = [(x * y) `mod` 64]
        runAll (Prime 17) (program (fromInteger x) (fromInteger y)) [] [] expected

    -- it "variable / constant" $ do
    --   let program x = do
    --         y <- input Public
    --         return $ x * (y :: UInt 6)
    --   let genPair = do
    --         x <- choose (0, 63)
    --         y <- choose (0, 63)
    --         return (x, y)
    --   forAll genPair $ \(x, y) -> do
    --     let expected = [(x * y) `mod` 64]
    --     runAll (Prime 17) (program (fromInteger x)) [y] [] expected
