{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Compilation.Experiment where

import Data.Bits qualified
import Keelung
import Test.Compilation.Util
import Test.Hspec

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

  describe "fromBools" $ do
    -- it "from variables" $ do
    --   let program = do
    --         xs <- inputList Public 8
    --         pack xs :: Comp (UInt 8)
    --   property $ \(x :: Word) -> do
    --     let bits = map (\b -> if b then 1 else 0) $ Data.Bits.testBit x <$> [0 .. 7]
    --     testCompiler gf181 program bits [] [fromIntegral x]
    --     testCompiler (Prime 2) program bits [] [fromIntegral x]
    --     testCompiler (Binary 7) program bits [] [fromIntegral x]
    -- it "from constants" $ do
    --   let program xs = do
    --         pack xs :: Comp (UInt 8)
    --   property $ \(x :: Word) -> do
    --     let bits = map (\b -> if b then true else false) $ Data.Bits.testBit x <$> [0 .. 7]
    --     testCompiler gf181 (program bits) [] [] [fromIntegral x]
    --     testCompiler (Prime 2) (program bits) [] [] [fromIntegral x]
    --     testCompiler (Binary 7) (program bits) [] [] [fromIntegral x]

    it "from Field element" $ do
      let program = do
            x' <- input Public
            x <- toUInt 2 x' :: Comp (UInt 2)
            pack [x !!! 0, x !!! 1] :: Comp (UInt 2)
      let x = 2 :: Word
      -- property $ \(x :: Word) -> do
      let set (i, b) x' = if b then Data.Bits.setBit x' i else x'
          expected = foldr set (0 :: Word) $ [(i, Data.Bits.testBit x i) | i <- [0 .. 0]]
      testCompiler (Prime 2) program [fromIntegral (x `mod` 2)] [] [fromIntegral expected]
