{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Test.Compilation.UInt.Bitwise (tests, run) where

import Data.Bits qualified
import Data.Word (Word64)
import Keelung hiding (compile)
import Test.Hspec
import Test.Compilation.Util
import Test.QuickCheck hiding ((.&.))

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests = describe "Bitwise" $ do
  it "rotate" $ do
    let program = do
          x <- inputUInt @4 Public
          return [rotate x (-4), rotate x (-3), rotate x (-2), rotate x (-1), rotate x 0, rotate x 1, rotate x 2, rotate x 3, rotate x 4]

    runAll gf181 program [0] [] [0, 0, 0, 0, 0, 0, 0, 0, 0]
    runAll gf181 program [1] [] [1, 2, 4, 8, 1, 2, 4, 8, 1]
    runAll gf181 program [3] [] [3, 6, 12, 9, 3, 6, 12, 9, 3]
    runAll gf181 program [5] [] [5, 10, 5, 10, 5, 10, 5, 10, 5]

  it "rotate left" $ do
    let program n = do
          x <- inputUInt @64 Public
          return $ x `rotate` n

    forAll arbitrary $ \(x :: Word64, n :: Int) -> do
      let expected = [toInteger (x `Data.Bits.rotateL` n)]
      runAll (Prime 2) (program n) [toInteger x] [] expected
      runAll gf181 (program n) [toInteger x] [] expected

  it "rotate right" $ do
    let program n = do
          x <- inputUInt @64 Public
          return $ x `rotate` (-n)

    forAll arbitrary $ \(x :: Word64, n :: Int) -> do
      let expected = [toInteger (x `Data.Bits.rotateR` n)]
      runAll (Prime 2) (program n) [toInteger x] [] expected
      runAll gf181 (program n) [toInteger x] [] expected

  it "shift" $ do
    let program = do
          x <- inputUInt @4 Public
          return [x .<<. (-4), x .>>. 3, shift x (-2), shift x (-1), shift x 0, shift x 1, shift x 2, shift x 3, shift x 4]

    runAll gf181 program [0] [] [0, 0, 0, 0, 0, 0, 0, 0, 0]
    runAll gf181 program [1] [] [0, 0, 0, 0, 1, 2, 4, 8, 0]
    runAll gf181 program [3] [] [0, 0, 0, 1, 3, 6, 12, 8, 0]
    runAll gf181 program [5] [] [0, 0, 1, 2, 5, 10, 4, 8, 0]

  it "shift left" $ do
    let program n = do
          x <- inputUInt @64 Public
          return $ x `shiftL` n

    forAll arbitrary $ \(x :: Word64, n :: Int) -> do
      let amount = abs n
      let expected = [toInteger (x `Data.Bits.shiftL` amount)]
      runAll (Prime 2) (program amount) [toInteger x] [] expected
      runAll gf181 (program amount) [toInteger x] [] expected

  it "shift right" $ do
    let program n = do
          x <- inputUInt @64 Public
          return $ x `shiftR` n

    forAll arbitrary $ \(x :: Word64, n :: Int) -> do
      let amount = abs n
      let expected = [toInteger (x `Data.Bits.shiftR` amount)]
      runAll (Prime 2) (program amount) [toInteger x] [] expected
      runAll gf181 (program amount) [toInteger x] [] expected

  it "Bit test / literal" $ do
    -- 0011
    let program = do
          let c = 3 :: UInt 4
          return [c !!! (-1), c !!! 0, c !!! 1, c !!! 2, c !!! 3, c !!! 4]
    runAll gf181 program [] [] [0, 1, 1, 0, 0, 1]

  it "Bit test / input var" $ do
    let program = do
          c <- input Private :: Comp (UInt 4)
          return [c !!! (-1), c !!! 0, c !!! 1, c !!! 2, c !!! 3, c !!! 4]
    runAll gf181 program [] [3] [0, 1, 1, 0, 0, 1]
    runAll gf181 program [] [5] [0, 1, 0, 1, 0, 1]

  it "Bit test / and 1" $ do
    let program = do
          x <- inputUInt @4 Public
          y <- inputUInt @4 Private
          return $ (x .&. y) !!! 0
    runAll gf181 program [2] [3] [0]
    runAll gf181 program [3] [5] [1]

  it "Bit test / and 2" $ do
    let program = do
          x <- inputUInt @4 Public
          y <- inputUInt @4 Private
          z <- inputUInt @4 Public
          return $ (x .&. y .&. z) !!! 0
    runAll gf181 program [2, 4] [3] [0]
    runAll gf181 program [3, 7] [5] [1]

  it "Bit test / or 1" $ do
    let program = do
          x <- inputUInt @4 Public
          y <- inputUInt @4 Private
          return $ (x .|. y) !!! 1
    runAll gf181 program [2] [3] [1]
    runAll gf181 program [3] [5] [1]
    runAll gf181 program [5] [9] [0]

  it "Bit test / or 2" $ do
    let program = do
          x <- inputUInt @4 Public
          return $ (x .|. 3) !!! 2
    runAll gf181 program [2] [] [0]
    runAll gf181 program [3] [] [0]
    runAll gf181 program [5] [] [1]

  it "Bit test / xor 0" $ do
    let program = do
          x <- inputUInt @4 Public
          y <- inputUInt @4 Private
          let w = x .^. y .^. 0
          return [w !!! 0]
    runAll gf181 program [2] [3] [1]

  it "Bit test / xor 1" $ do
    let program = do
          x <- inputUInt @4 Public
          y <- inputUInt @4 Private
          z <- inputUInt @4 Public
          w <- reuse $ x .^. y .^. z
          return [w !!! 0, w !!! 1, w !!! 2, w !!! 3]
    runAll gf181 program [2, 4] [3] [1, 0, 1, 0]
    runAll gf181 program [3, 7] [5] [1, 0, 0, 0]

  it "Bit test / BtoU" $ do
    let program = do
          x <- input Public
          let u = BtoU x :: UInt 4
          return [u !!! 0, u !!! 1, u !!! 2, u !!! 3]
    runAll gf181 program [0] [] [0, 0, 0, 0]
    runAll gf181 program [1] [] [1, 0, 0, 0]

  it "Bit test / rotate 1" $ do
    let program = do
          x <- inputUInt @4 Public
          return $ (x `rotate` 0) !!! 0
    runAll gf181 program [2] [] [0]

  it "Bit test / rotate 2" $ do
    -- 0011 0100211003
    let program = do
          x <- inputUInt @4 Public
          y <- inputUInt @4 Public
          return
            [ (x `rotate` 0) !!! 0,
              (x `rotate` 1) !!! 1,
              (x `rotate` (-1)) !!! 0,
              ((x .^. y) `rotate` 1) !!! 1
            ]
    runAll gf181 program [2, 3] [] [0, 0, 1, 1]