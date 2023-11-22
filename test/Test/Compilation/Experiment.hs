{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Compilation.Experiment where

import Data.Bits qualified
import Keelung
import Test.Compilation.Util
import Test.Hspec
import Test.QuickCheck
import Control.Monad

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests = describe "Experiment" $ do
  describe "pack" $ do
    it "from Field element" $ do
      let program = do
            x' <- input Public
            x <- toUInt 2 x' :: Comp (UInt 2)
            pack [x !!! 0, x !!! 1] :: Comp (UInt 3)
      property $ \(x :: Word) -> do
        let set (i, b) x' = if b then Data.Bits.setBit x' i else x'
            expected = foldr set (0 :: Word) $ [ (i, Data.Bits.testBit x i) | i <- [0 .. 1] ]
        forM_ [Prime 7] $ \field -> do
        -- forM_ [gf181, Prime 2, Binary 7] $ \field -> do
          runAll field program [fromIntegral (x `mod` 4)] [] [fromIntegral expected]

      -- let x = 1 :: Word
      -- let set (i, b) x' = if b then Data.Bits.setBit x' i else x'
      --     expected = foldr set (0 :: Word) $ [ (i, Data.Bits.testBit x i) | i <- [0 .. 1] ]
      -- debug (Prime 2) program
      -- debugUnoptimized (Prime 17) program
      -- runAll (Prime 2) program [fromIntegral x] [] [fromIntegral expected]