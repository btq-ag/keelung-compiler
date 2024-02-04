{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Compilation.UInt.Bitwise (tests, run) where

import Control.Monad
import Data.Bits qualified
import Data.Word (Word64, Word8)
import Keelung hiding (compile)
import Test.Compilation.Util
import Test.Hspec
import Test.QuickCheck hiding ((.&.))

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests = describe "Bitwise" $ do
  describe "rotate" $ do
    describe "constant / byte" $ do
      let program constant i = return $ rotate (constant :: UInt 8) i

      it "GF181" $ property $ \(i :: Int, x :: Word8) -> do
        let expected = [toInteger (Data.Bits.rotate x i)]
        testCompiler gf181 (program (fromIntegral x) i) [] [] expected

      it "Prime 2" $ property $ \(i :: Int, x :: Word8) -> do
        let expected = [toInteger (Data.Bits.rotate x i)]
        testCompiler (Prime 2) (program (fromIntegral x) i) [] [] expected

      it "Binary 7" $ property $ \(i :: Int, x :: Word8) -> do
        let expected = [toInteger (Data.Bits.rotate x i)]
        testCompiler (Binary 7) (program (fromIntegral x) i) [] [] expected

    describe "variable / byte" $ do
      let program i = do
            x <- input Public :: Comp (UInt 8)
            return $ rotate x i

      it "GF181" $ property $ \(i :: Int, x :: Word8) -> do
        let expected = [toInteger (Data.Bits.rotate x i)]
        testCompiler gf181 (program i) [toInteger x] [] expected

      it "Prime 2" $ property $ \(i :: Int, x :: Word8) -> do
        let expected = [toInteger (Data.Bits.rotate x i)]
        testCompiler (Prime 2) (program i) [toInteger x] [] expected

      it "Binary 7" $ property $ \(i :: Int, x :: Word8) -> do
        let expected = [toInteger (Data.Bits.rotate x i)]
        testCompiler (Binary 7) (program i) [toInteger x] [] expected

    it "misc" $ do
      let program = do
            x <- input Public :: Comp (UInt 4)
            return [rotate x (-4), rotate x (-3), rotate x (-2), rotate x (-1), rotate x 0, rotate x 1, rotate x 2, rotate x 3, rotate x 4]

      forM_ [gf181, Prime 257, Prime 2, Binary 7] $ \field -> do
        testCompiler field program [0] [] [0, 0, 0, 0, 0, 0, 0, 0, 0]
        testCompiler field program [1] [] [1, 2, 4, 8, 1, 2, 4, 8, 1]
        testCompiler field program [3] [] [3, 6, 12, 9, 3, 6, 12, 9, 3]
        testCompiler field program [5] [] [5, 10, 5, 10, 5, 10, 5, 10, 5]

  describe "shift" $ do
    describe "constant / byte" $ do
      let program constant i = return $ shift (constant :: UInt 8) i

      it "GF181" $ property $ \(i :: Int, x :: Word8) -> do
        let expected = [toInteger (Data.Bits.shift x i)]
        testCompiler gf181 (program (fromIntegral x) i) [] [] expected

      it "Prime 2" $ property $ \(i :: Int, x :: Word8) -> do
        let expected = [toInteger (Data.Bits.shift x i)]
        testCompiler (Prime 2) (program (fromIntegral x) i) [] [] expected

      it "Binary 7" $ property $ \(i :: Int, x :: Word8) -> do
        let expected = [toInteger (Data.Bits.shift x i)]
        testCompiler (Binary 7) (program (fromIntegral x) i) [] [] expected

    describe "variable / byte" $ do
      let program i = do
            x <- input Public :: Comp (UInt 8)
            return $ shift x i

      it "GF181" $ property $ \(i :: Int, x :: Word8) -> do
        let expected = [toInteger (Data.Bits.shift x i)]
        testCompiler gf181 (program i) [toInteger x] [] expected

      it "Prime 2" $ property $ \(i :: Int, x :: Word8) -> do
        let expected = [toInteger (Data.Bits.shift x i)]
        testCompiler (Prime 2) (program i) [toInteger x] [] expected

      it "Binary 7" $ property $ \(i :: Int, x :: Word8) -> do
        let expected = [toInteger (Data.Bits.shift x i)]
        testCompiler (Binary 7) (program i) [toInteger x] [] expected

    it "misc" $ do
      let program = do
            x <- input Public :: Comp (UInt 4)
            return [x .<<. (-4), x .>>. 3, shift x (-2), shift x (-1), shift x 0, shift x 1, shift x 2, shift x 3, shift x 4]

      testCompiler gf181 program [0] [] [0, 0, 0, 0, 0, 0, 0, 0, 0]
      testCompiler gf181 program [1] [] [0, 0, 0, 0, 1, 2, 4, 8, 0]
      testCompiler gf181 program [3] [] [0, 0, 0, 1, 3, 6, 12, 8, 0]
      testCompiler gf181 program [5] [] [0, 0, 1, 2, 5, 10, 4, 8, 0]

    it "shift left" $ do
      let program n = do
            x <- input Public :: Comp (UInt 64)
            return $ x `shiftL` n

      property $ \(x :: Word64, n :: Int) -> do
        let amount = abs n
        let expected = [toInteger (x `Data.Bits.shiftL` amount)]
        testCompiler (Prime 2) (program amount) [toInteger x] [] expected
        testCompiler gf181 (program amount) [toInteger x] [] expected

    it "shift right" $ do
      let program n = do
            x <- input Public :: Comp (UInt 64)
            return $ x `shiftR` n

      property $ \(x :: Word64, n :: Int) -> do
        let amount = abs n
        let expected = [toInteger (x `Data.Bits.shiftR` amount)]
        testCompiler (Prime 2) (program amount) [toInteger x] [] expected
        testCompiler gf181 (program amount) [toInteger x] [] expected

  describe "bit tests" $ do
    it "literal" $ do
      -- 0011
      let program = do
            let c = 3 :: UInt 4
            return [c !!! (-1), c !!! 0, c !!! 1, c !!! 2, c !!! 3, c !!! 4]
      testCompiler gf181 program [] [] [0, 1, 1, 0, 0, 1]

    it "input var" $ do
      let program = do
            c <- input Private :: Comp (UInt 4)
            return [c !!! (-1), c !!! 0, c !!! 1, c !!! 2, c !!! 3, c !!! 4]
      testCompiler gf181 program [] [3] [0, 1, 1, 0, 0, 1]
      testCompiler gf181 program [] [5] [0, 1, 0, 1, 0, 1]

    it "and 1" $ do
      let program = do
            x <- input Public :: Comp (UInt 4)
            y <- input Private
            return $ (x .&. y) !!! 0
      testCompiler gf181 program [2] [3] [0]
      testCompiler gf181 program [3] [5] [1]

    it "and 2" $ do
      let program = do
            x <- input Public :: Comp (UInt 4)
            y <- input Private
            z <- input Public
            return $ (x .&. y .&. z) !!! 0
      testCompiler gf181 program [2, 4] [3] [0]
      testCompiler gf181 program [3, 7] [5] [1]

    it "or 1" $ do
      let program = do
            x <- input Public :: Comp (UInt 4)
            y <- input Private
            return $ (x .|. y) !!! 1
      testCompiler gf181 program [2] [3] [1]
      testCompiler gf181 program [3] [5] [1]
      testCompiler gf181 program [5] [9] [0]

    it "or 2" $ do
      let program = do
            x <- input Public :: Comp (UInt 4)
            return $ (x .|. 3) !!! 2
      testCompiler gf181 program [2] [] [0]
      testCompiler gf181 program [3] [] [0]
      testCompiler gf181 program [5] [] [1]

    it "xor 0" $ do
      let program = do
            x <- input Public :: Comp (UInt 4)
            y <- input Private
            let w = x .^. y .^. 0
            return [w !!! 0]
      testCompiler gf181 program [2] [3] [1]

    it "xor 1" $ do
      let program = do
            x <- input Public :: Comp (UInt 4)
            y <- input Private
            z <- input Public
            w <- reuse $ x .^. y .^. z
            return [w !!! 0, w !!! 1, w !!! 2, w !!! 3]
      testCompiler gf181 program [2, 4] [3] [1, 0, 1, 0]
      testCompiler gf181 program [3, 7] [5] [1, 0, 0, 0]

    it "BtoU" $ do
      let program = do
            x <- input Public
            let u = BtoU x :: UInt 4
            return [u !!! 0, u !!! 1, u !!! 2, u !!! 3]
      testCompiler gf181 program [0] [] [0, 0, 0, 0]
      testCompiler gf181 program [1] [] [1, 0, 0, 0]

    it "rotate 1" $ do
      let program = do
            x <- input Public :: Comp (UInt 4)
            return $ (x `rotate` 0) !!! 0
      testCompiler gf181 program [2] [] [0]

    it "rotate 2" $ do
      -- 0011 0100211003
      let program = do
            x <- input Public :: Comp (UInt 4)
            y <- input Public
            return
              [ (x `rotate` 0) !!! 0,
                (x `rotate` 1) !!! 1,
                (x `rotate` (-1)) !!! 0,
                ((x .^. y) `rotate` 1) !!! 1
              ]
      testCompiler gf181 program [2, 3] [] [0, 0, 1, 1]