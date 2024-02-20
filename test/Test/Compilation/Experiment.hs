{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Compilation.Experiment where

import Control.Monad (forM_)
import Keelung
import Keelung.Data.U qualified as U
import Test.Compilation.Util
import Test.Hspec
import Test.QuickCheck

-- import Test.QuickCheck

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests = describe "Experiment" $ do
  -- describe "pack" $ do
  --   it "from Field element" $ do
  --     let program = do
  --           x' <- input Public
  --           x <- toUInt 2 x' :: Comp (UInt 2)
  --           pack [x !!! 0, x !!! 1] :: Comp (UInt 3)
  --     property $ \(x :: Word) -> do
  --       testCompiler gf181 program [fromIntegral (x `mod` 4)] [] [fromIntegral (x `mod` 4)]
  --       testCompiler (Prime 7) program [fromIntegral (x `mod` 4)] [] [fromIntegral (x `mod` 4)]
  --       testCompiler (Prime 2) program [fromIntegral (x `mod` 2)] [] [fromIntegral (x `mod` 2)]
  --       testCompiler (Binary 7) program [fromIntegral (x `mod` 4)] [] [fromIntegral (x `mod` 4)]
  --       testCompiler (Binary 2) program [fromIntegral (x `mod` 2)] [] [fromIntegral (x `mod` 2)]

  describe "Carry-less Multiplication" $ do
    it "1 variable / 1 constant" $ do
      let program y = do
            x <- input Public
            return $ x .*. fromInteger y :: Comp (UInt 8)
      let genPair = do
            x <- choose (0, 255)
            return (x, 0)
      forAll genPair $ \(x, y) -> do
        let expected = [toInteger (U.clMul (U.new 8 x) (U.new 8 y))]
        forM_ [gf181, Prime 17] $ \field -> do
          debug field (program (fromIntegral y))
          testCompiler field (program (fromIntegral y)) [toInteger x] [] expected
