{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Compilation.Experiment where

import Keelung
import Test.Compilation.Util
import Test.Hspec
import Test.QuickCheck

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
        runAll gf181 program [fromIntegral (x `mod` 4)] [] [fromIntegral (x `mod` 4)]
        runAll (Prime 7) program [fromIntegral (x `mod` 4)] [] [fromIntegral (x `mod` 4)]
        runAll (Prime 2) program [fromIntegral (x `mod` 2)] [] [fromIntegral (x `mod` 2)]
        runAll (Binary 7) program [fromIntegral (x `mod` 4)] [] [fromIntegral (x `mod` 4)]
        runAll (Binary 2) program [fromIntegral (x `mod` 2)] [] [fromIntegral (x `mod` 2)]

    it "from Field element" $ do
      let program = do
            x' <- input Public
            x <- toUInt 8 x' :: Comp (UInt 8)
            pack [x !!! 0, x !!! 1] :: Comp (UInt 3)
      -- property $ \(x :: Word) -> do
      --   runAll gf181 program [fromIntegral x] [] [fromIntegral x]
      debug gf181 program

-- runAll (Prime 7) program [fromIntegral (x `mod` 4)] [] [fromIntegral (x `mod` 4)]
-- runAll (Prime 2) program [fromIntegral (x `mod` 2)] [] [fromIntegral (x `mod` 2)]
-- runAll (Binary 7) program [fromIntegral (x `mod` 4)] [] [fromIntegral (x `mod` 4)]
-- runAll (Binary 2) program [fromIntegral (x `mod` 2)] [] [fromIntegral (x `mod` 2)]