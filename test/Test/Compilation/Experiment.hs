{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Compilation.Experiment (run, tests) where

import Keelung
import Keelung.Data.U qualified as U
import Test.Arbitrary ()
import Test.Compilation.Util
import Test.Hspec
import Test.QuickCheck

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests =
  describe "Slice" $ do
    it "should throw exception when the starting index < 0" $ do
      let program = do
            x <- input Public :: Comp (UInt 8)
            return $ slice x (-1, 3) :: Comp (UInt 4)
      testCompiler (Binary 7) program [0] [] [0] `shouldThrow` anyException
      testCompiler (Prime 17) program [0] [] [0] `shouldThrow` anyException
      testCompiler gf181 program [0] [] [0] `shouldThrow` anyException

    it "should throw exception when the ending index is smaller than the starting index" $ do
      let program = do
            x <- input Public :: Comp (UInt 8)
            return $ slice x (3, 1) :: Comp (UInt 4)
      testCompiler (Binary 7) program [0] [] [0] `shouldThrow` anyException
      testCompiler (Prime 17) program [0] [] [0] `shouldThrow` anyException
      testCompiler gf181 program [0] [] [0] `shouldThrow` anyException

    it "should throw exception when the ending index is greater than the bit width" $ do
      let program = do
            x <- input Public :: Comp (UInt 8)
            return $ slice x (3, 9) :: Comp (UInt 4)
      testCompiler (Binary 7) program [0] [] [0] `shouldThrow` anyException
      testCompiler (Prime 17) program [0] [] [0] `shouldThrow` anyException
      testCompiler gf181 program [0] [] [0] `shouldThrow` anyException

    it "should throw exception when the range does not match with the type" $ do
      let program = do
            x <- input Public :: Comp (UInt 8)
            return $ slice x (3, 6) :: Comp (UInt 4)
      testCompiler (Binary 7) program [0] [] [0] `shouldThrow` anyException
      testCompiler (Prime 17) program [0] [] [0] `shouldThrow` anyException
      testCompiler gf181 program [0] [] [0] `shouldThrow` anyException

    it "constant (slice width = 4)" $ do
      let genParam = do
            i <- chooseInt (0, 4)
            val <- choose (0, 255)
            return (val, i)

      let program x (i, j) = do
            let u = fromInteger x :: UInt 8
            return $ slice u (i, j) :: Comp (UInt 4)
      forAll genParam $ \(val, i) -> do
        let expected = [toInteger (U.slice (U.new 8 val) (i, i + 4))]
        testCompiler (Binary 7) (program val (i, i + 4)) [] [] expected
        testCompiler (Prime 17) (program val (i, i + 4)) [] [] expected
        testCompiler gf181 (program val (i, i + 4)) [] [] expected

    it "variable (slice width = 4)" $ do
      let genParam = do
            i <- chooseInt (0, 4)
            val <- choose (0, 255)
            return (val, i)

      let program (i, j) = do
            x <- input Public :: Comp (UInt 8)
            return $ slice x (i, j) :: Comp (UInt 4)
      forAll genParam $ \(val, i) -> do
        let expected = [toInteger (U.slice (U.new 8 val) (i, i + 4))]
        testCompiler (Binary 7) (program (i, i + 4)) [val] [] expected
        testCompiler (Prime 17) (program (i, i + 4)) [val] [] expected
        testCompiler gf181 (program (i, i + 4)) [val] [] expected