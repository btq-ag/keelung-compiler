{-# LANGUAGE DataKinds #-}

module Test.Compilation.Statement where

import Keelung
import Test.Compilation.Util
import Test.Hspec
import Test.QuickCheck

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests = describe "Statement" $ do
  describe "toField" $ do
    describe "from variable" $ do
      let program = do
            x <- input Public :: Comp (UInt 8)
            toField x
      it "GF181" $ do
        forAll (chooseInteger (-100, 511)) $ \n -> do
          runAll gf181 program [n] [] [n `mod` 256]
      it "Prime 2" $ do
        forAll (chooseInteger (-10, 4)) $ \n -> do
          runAll (Prime 2) program [n] [] [n `mod` 2]
      it "Binary 7" $ do
        forAll (chooseInteger (-10, 8)) $ \n -> do
          runAll (Binary 7) program [n] [] [n `mod` 4]
    describe "from constant" $ do
      let program n = toField (n :: UInt 8)
      it "GF181" $ do
        forAll (chooseInteger (-100, 511)) $ \n -> do
          runAll gf181 (program (fromInteger n)) [] [] [n `mod` 256]
      it "Prime 2" $ do
        forAll (chooseInteger (-10, 4)) $ \n -> do
          runAll (Prime 2) (program (fromInteger n)) [] [] [n `mod` 2]
      -- it "Binary 7" $ do
      --   -- forAll (chooseInteger (-10, 8)) $ \n -> do
      --   --   runAll (Binary 7) (program (fromInteger n)) [] [] [n `mod` 4]
      --   runAll (Binary 7) (program 7) [] [] [3]

  -- describe "toUInt" $ do
  --   it "from variable" $ do
  --     let program = input Public >>= toUInt 8 :: Comp (UInt 8)
  --     runAll gf181 program [100] [] [100]
  --     runAll (Prime 2) program [100] [] [0]
    --   runAll (Prime 2) program [101] [] [1]
    --   -- runAll (Binary 7) program [1] [] [1]
    --   -- runAll (Binary 7) program [2] [] [2]
    --   -- runAll (Binary 7) program [3] [] [3]
    --   -- runAll (Binary 7) program [4] [] [3]
    --   -- runAll (Binary 7) program [5] [] [2]
    -- it "from constant" $ do
    --   let program = toUInt @8 8
    --   runAll gf181 (program 3) [] [] [3]
    --   runAll (Prime 2) (program 100) [] [] [0]
    --   runAll (Prime 2) (program 101) [] [] [1]
    --   runAll (Binary 7) (program 1) [] [] [1]