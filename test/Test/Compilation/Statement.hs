{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Compilation.Statement where

import Control.Monad
import Data.Bits qualified
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
          testCompiler gf181 program [n] [] [n `mod` 256]
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

  describe "fromField" $ do
    describe "from variable" $ do
      let program = input Public >>= fromField 8 :: Comp (UInt 8)
      it "GF181" $ do
        forAll (chooseInteger (0, 255)) $ \n -> do
          testCompiler gf181 program [n] [] [n `mod` 256]
      it "Prime 2" $ do
        forAll (chooseInteger (0, 1)) $ \n -> do
          testCompiler (Prime 2) program [n] [] [n `mod` 2]
      it "Binary 7" $ do
        forAll (chooseInteger (0, 3)) $ \n -> do
          testCompiler (Binary 7) program [n] [] [n `mod` 4]
    describe "from constant" $ do
      let program n = fromField 8 (n :: Field) :: Comp (UInt 8)
      it "GF181" $ do
        forAll (chooseInteger (0, 255)) $ \n -> do
          testCompiler gf181 (program (fromInteger n)) [] [] [n `mod` 256]
      it "Prime 2" $ do
        forAll (chooseInteger (0, 1)) $ \n -> do
          testCompiler (Prime 2) (program (fromInteger n)) [] [] [n `mod` 2]
      it "Binary 7" $ do
        forAll (chooseInteger (0, 3)) $ \n -> do
          testCompiler (Binary 7) (program (fromInteger n)) [] [] [n `mod` 4]

  describe "fromBools" $ do
    it "from variables" $ do
      let program = do
            xs <- inputList Public 8
            fromBools xs :: Comp (UInt 8)
      property $ \(x :: Word) -> do
        let bits = map (\b -> if b then 1 else 0) $ Data.Bits.testBit x <$> [0 .. 7]
        forM_ [gf181, Prime 2, Binary 7] $ \field -> do
          testCompiler field program bits [] [fromIntegral x]
    it "from constants" $ do
      let program xs = do
            fromBools xs :: Comp (UInt 8)
      property $ \(x :: Word) -> do
        let bits = map (\b -> if b then true else false) $ Data.Bits.testBit x <$> [0 .. 7]
        forM_ [gf181, Prime 2, Binary 7] $ \field -> do
          testCompiler field (program bits) [] [] [fromIntegral x]

    it "from Field element" $ do
      let program = do
            x' <- input Public
            x <- fromField 2 x' :: Comp (UInt 2)
            fromBools [x !!! 0, x !!! 1] :: Comp (UInt 2)
      property $ \(x :: Word) -> do
        let set (i, b) x' = if b then Data.Bits.setBit x' i else x'
            expected = foldr set (0 :: Word) $ [(i, Data.Bits.testBit x i) | i <- [0 .. 1]]
        forM_ [gf181, Prime 5, Binary 7] $ \field -> do
          testCompiler field program [fromIntegral (x `mod` 4)] [] [fromIntegral expected]