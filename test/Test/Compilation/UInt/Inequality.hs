{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Compilation.UInt.Inequality (tests, run) where

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
tests = describe "inequality" $ do
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
          return $ x `neq` (y :: UInt 8)

    forAll genCase $ \(x, y :: Word8) -> do
      let expected = [if x == y then 0 else 1]
      forM_ [gf181, Prime 2, Binary 7] $ \field -> do
        check field (program (fromIntegral x) (fromIntegral y)) [] [] expected

  it "variable + constant" $ do
    let program constant = do
          x <- input Public :: Comp (UInt 8)
          return $ x `neq` constant

    forAll genCase $ \(x, y :: Word8) -> do
      let expected = [if x == y then 0 else 1]
      forM_ [gf181, Prime 2, Binary 7] $ \field -> do
        check field (program (fromIntegral x)) [fromIntegral y] [] expected

  it "2 variables" $ do
    let program = do
          x <- input Public :: Comp (UInt 8)
          y <- input Public :: Comp (UInt 8)
          return $ x `neq` y

    forAll genCase $ \(x, y :: Word8) -> do
      let expected = [if x == y then 0 else 1]
      forM_ [gf181, Prime 2, Binary 7] $ \field -> do
        check field program [fromIntegral x, fromIntegral y] [] expected
