{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Compilation.Field.Arithmetics (tests, run) where

import Data.Field.Galois qualified as Data.Galois.Field
import Keelung hiding (compile)
import Test.Compilation.Util
import Test.Hspec
import Test.QuickCheck

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests = describe "Field arithmetics" $ do
  it "Addition / Prime 257" $ do
    let program = do
          x <- input Public :: Comp Field
          y <- input Public
          return (x + y)
    forAll arbitrary $ \(x, y :: Data.Galois.Field.Prime 257) -> do
      let expected = [toInteger (x + y)]
      runAll (Prime 257) program [toInteger x, toInteger y] [] expected

  it "Addition / Binary 256" $ do
    let program = do
          x <- input Public :: Comp Field
          y <- input Public
          return (x + y)
    forAll arbitrary $ \(x, y :: Data.Galois.Field.Binary 256) -> do
      let expected = [toInteger (x + y)]
      runAll (Binary 0x100) program [toInteger x, toInteger y] [] expected

  it "Mixed 1 / GF181" $ do
    let program = do
          x <- inputField Public
          y <- inputField Public
          return $ x * y + y * 2
    property $ \(x, y :: GF181) -> do
      let expected = [toInteger $ x * y + y * 2]
      runAll gf181 program [toInteger x, toInteger y] [] expected

  it "Mixed 1 / Binary 256" $ do
    let program = do
          x <- inputField Public
          y <- inputField Public
          return $ x * y + y * 2
    property $ \(x, y :: Data.Galois.Field.Binary 256) -> do
      let expected = [toInteger $ x * y + y * 2]
      runAll (Binary 256) program [toInteger x, toInteger y] [] expected

  it "Mixed 2 / GF181" $ do
    let program = do
          x <- inputField Public
          y <- inputField Private
          z <- reuse $ x * y + y * 2
          return $ x * y - z
    property $ \(x :: GF181, y :: GF181) -> do
      let expected = [toInteger $ -y * 2]
      runAll gf181 program [toInteger x] [toInteger y] expected

  it "Mixed 2 / Binary 256" $ do
    let program = do
          x <- inputField Public
          y <- inputField Private
          z <- reuse $ x * y + y * 2
          return $ x * y - z
    property $ \(x :: Data.Galois.Field.Binary 256, y :: Data.Galois.Field.Binary 256) -> do
      let expected = [toInteger $ -y * 2]
      runAll (Binary 256) program [toInteger x] [toInteger y] expected
