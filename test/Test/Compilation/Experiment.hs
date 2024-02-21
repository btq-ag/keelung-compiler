{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Compilation.Experiment where

import Keelung
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

  describe "toField" $ do
    describe "from variable" $ do
      let program = do
            x <- input Public :: Comp (UInt 8)
            toField x
      it "GF181" $ do
        debug gf181 program
        -- forAll (chooseInteger (-100, 511)) $ \n -> do
        --   testCompiler gf181 program [n] [] [n `mod` 256]
      it "Prime 2" $ do
        forAll (chooseInteger (-10, 4)) $ \n -> do
          testCompiler (Prime 2) program [n] [] [n `mod` 2]
      it "Binary 7" $ do
        forAll (chooseInteger (-10, 8)) $ \n -> do
          testCompiler (Binary 7) program [n] [] [n `mod` 4]
    describe "from constant" $ do
      let program n = toField (n :: UInt 8)
      it "GF181" $ do
        forAll (chooseInteger (-100, 511)) $ \n -> do
          testCompiler gf181 (program (fromInteger n)) [] [] [n `mod` 256]
      it "Prime 2" $ do
        forAll (chooseInteger (-10, 4)) $ \n -> do
          testCompiler (Prime 2) (program (fromInteger n)) [] [] [n `mod` 2]
      it "Binary 7" $ do
        forAll (chooseInteger (-10, 8)) $ \n -> do
          testCompiler (Binary 7) (program (fromInteger n)) [] [] [n `mod` 4]
