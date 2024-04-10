{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Compilation.UInt.Equality (tests, run) where

import Control.Monad
import Data.Word (Word8)
import Keelung hiding (compile)
import Test.Util
import Test.Hspec
import Test.QuickCheck

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests = describe "equality" $ do
  let genCase = do
        isEq <- arbitrary
        if isEq
          then do
            x <- arbitrary
            return (x, x)
          else do
            x <- arbitrary
            y <- arbitrary
            return (x, y)

  it "2 constants" $ do
    let program x y = do
          return $ x `eq` (y :: UInt 8)

    forAll genCase $ \(x, y :: Word8) -> do
      let expected = [if x == y then 1 else 0]
      forM_ [gf181, Prime 2, Binary 7] $ \field -> do
        check field (program (fromIntegral x) (fromIntegral y)) [] [] expected

  it "variable + constant" $ do
    let program constant = do
          x <- input Public :: Comp (UInt 8)
          return $ x `eq` constant

    forAll genCase $ \(x, y :: Word8) -> do
      let expected = [if x == y then 1 else 0]
      forM_ [gf181, Prime 2, Binary 7] $ \field -> do
        check field (program (fromIntegral x)) [fromIntegral y] [] expected

  it "2 variables" $ do
    let program = do
          x <- input Public :: Comp (UInt 8)
          y <- input Public :: Comp (UInt 8)
          return $ x `eq` y

    forAll genCase $ \(x, y :: Word8) -> do
      let expected = [if x == y then 1 else 0]
      forM_ [gf181, Prime 2, Binary 7] $ \field -> do
        check field program [fromIntegral x, fromIntegral y] [] expected
