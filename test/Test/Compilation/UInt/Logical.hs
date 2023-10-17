{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Test.Compilation.UInt.Logical (tests, run) where

import Control.Monad
import Data.Bits qualified
import Data.Word
import Keelung hiding (compile)
import Keelung.Data.U qualified as U
import Test.Compilation.Util
import Test.Hspec
import Test.QuickCheck hiding ((.&.))

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests = describe "Logical" $ do
  describe "complement" $ do
    it "variable / byte / Prime 13" $ do
      let program = do
            x <- inputUInt @8 Public
            return $ complement x
      forAll (choose (0, 255)) $ \x -> do
        let uint = U.new 8 x
        let expected = [U.uValue (Data.Bits.complement uint)]
        runAll (Prime 13) program [U.uValue uint] [] expected

    it "constant / byte / Prime 13" $ do
      let program x = do
            return $ complement (x :: UInt 8)
      forAll (choose (0, 255)) $ \x -> do
        let uint = U.new 8 x
        let expected = [U.uValue (Data.Bits.complement uint)]
        runAll (Prime 13) (program (fromInteger x)) [] [] expected

  describe "conjunction" $ do
    it "2 variables / byte / Prime 13" $ do
      let program = do
            x <- inputUInt @8 Public
            y <- inputUInt @8 Public
            return $ x .&. y
      forAll
        ( do
            x <- choose (0, 255)
            y <- choose (0, 255)
            return (x, y)
        )
        $ \(x, y) -> do
          let expected = [x Data.Bits..&. y]
          runAll (Prime 13) program [x, y] [] expected

    it "3 variables / byte / Prime 13" $ do
      let program = do
            x <- inputUInt @8 Public
            y <- inputUInt @8 Public
            z <- inputUInt @8 Public
            return $ x .&. y .&. z
      forAll
        ( do
            x <- choose (0, 255)
            y <- choose (0, 255)
            z <- choose (0, 255)
            return (x, y, z)
        )
        $ \(x, y, z) -> do
          let expected = [x Data.Bits..&. y Data.Bits..&. z]
          runAll (Prime 13) program [x, y, z] [] expected

    it "variables with constants / byte / Prime 13" $ do
      let program = do
            x <- inputUInt @8 Public
            y <- inputUInt @8 Public
            z <- inputUInt @8 Public
            return $ x .&. y .&. z .&. 3
      forAll
        ( do
            x <- choose (0, 255)
            y <- choose (0, 255)
            z <- choose (0, 255)
            return (x, y, z)
        )
        $ \(x, y, z) -> do
          let expected = [x Data.Bits..&. y Data.Bits..&. z Data.Bits..&. 3]
          runAll (Prime 13) program [x, y, z] [] expected

  describe "disjunction" $ do
    it "2 variables / byte / Prime 13" $ do
      let program = do
            x <- inputUInt @8 Public
            y <- inputUInt @8 Public
            return $ x .|. y
      forAll
        ( do
            x <- choose (0, 255)
            y <- choose (0, 255)
            return (x, y)
        )
        $ \(x, y) -> do
          let expected = [x Data.Bits..|. y]
          runAll (Prime 13) program [x, y] [] expected

    it "3 variables / byte / Prime 13" $ do
      let program = do
            x <- inputUInt @8 Public
            y <- inputUInt @8 Public
            z <- inputUInt @8 Public
            return $ x .|. y .|. z
      forAll
        ( do
            x <- choose (0, 255)
            y <- choose (0, 255)
            z <- choose (0, 255)
            return (x, y, z)
        )
        $ \(x, y, z) -> do
          let expected = [x Data.Bits..|. y Data.Bits..|. z]
          runAll (Prime 13) program [x, y, z] [] expected

    it "variables with constants / byte / Prime 13" $ do
      let program = do
            x <- inputUInt @8 Public
            y <- inputUInt @8 Public
            z <- inputUInt @8 Public
            return $ x .|. y .|. z .|. 3
      forAll
        ( do
            x <- choose (0, 255)
            y <- choose (0, 255)
            z <- choose (0, 255)
            return (x, y, z)
        )
        $ \(x, y, z) -> do
          let expected = [x Data.Bits..|. y Data.Bits..|. z Data.Bits..|. 3]
          runAll (Prime 13) program [x, y, z] [] expected

  describe "exclusive disjunction" $ do
    it "2 variables / byte" $ do
      let program = do
            x <- inputUInt @8 Public
            y <- inputUInt @8 Public
            return $ x .^. y
      forAll arbitrary $ \(x' :: Word8, y' :: Word8) -> do
        let x = toInteger x'
        let y = toInteger y'
        let expected = [Data.Bits.xor x y]
        runAll (Prime 13) program [x, y] [] expected
        runAll (Prime 257) program [x, y] [] expected
        runAll gf181 program [x, y] [] expected

    it "more than 2 variables / byte" $ do
      let program n = do
            xs <- replicateM n (inputUInt @8 Public)
            return $ foldl (.^.) 0 xs
      forAll
        ( do
            n <- choose (8, 8)
            xs <- replicateM n (choose (0, 255))
            return (n, xs)
        )
        $ \(n, xs) -> do
          let expected = [foldl Data.Bits.xor 0 xs]
          runAll (Prime 13) (program n) xs [] expected
          runAll (Prime 257) (program n) xs [] expected
          runAll gf181 (program n) xs [] expected

    it "variables with constants / byte / Prime 13" $ do
      let program = do
            x <- inputUInt @8 Public
            y <- inputUInt @8 Public
            z <- inputUInt @8 Public
            return $ x .^. y .^. z .^. 3
      forAll
        ( do
            x <- choose (0, 255)
            y <- choose (0, 255)
            z <- choose (0, 255)
            return (x, y, z)
        )
        $ \(x, y, z) -> do
          let expected = [x `Data.Bits.xor` y `Data.Bits.xor` z `Data.Bits.xor` 3]
          runAll (Prime 13) program [x, y, z] [] expected
