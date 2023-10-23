{-# LANGUAGE ScopedTypeVariables #-}

module Test.Compilation.Field (tests, run) where

import Control.Monad
import Keelung hiding (compile)
import Test.Compilation.Field.Arithmetics qualified
import Test.Compilation.Field.Equality qualified
import Test.Compilation.Field.Inequality qualified
import Test.Compilation.Util
import Test.Hspec
import Test.QuickCheck hiding ((.&.))

run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = describe "Field" $ do
  Test.Compilation.Field.Arithmetics.tests
  Test.Compilation.Field.Equality.tests
  Test.Compilation.Field.Inequality.tests

  it "conditional (variable)" $ do
    let program = do
          x <- inputBool Public
          y <- inputField Public
          return $ cond x y (5 :: Field)

    property $ \(x' :: GF181, y' :: GF181) -> do
      let x = x' `mod` 4
          y = y' `mod` 4
      let expectedOutput = if (x `mod` 2) == 1 then [toInteger y] else [5]
      runAll gf181 program [toInteger x `mod` 2, toInteger y] [] expectedOutput

  it "exponentiation (variable base)" $ do
    let program i = do
          x <- inputField Public
          return (x `pow` i)
    property $ \(x :: GF181, i) -> do
      when (i >= 0) $ do
        let expectedOutput = [toInteger (x ^ (i :: Integer) :: GF181)]
        runAll gf181 (program i) [toInteger x] [] expectedOutput

  it "exponentiation (constant base)" $ do
    let program x i = do
          return (fromIntegral x `pow` i)
    property $ \(x :: GF181, i) -> do
      when (i >= 0) $ do
        let expectedOutput = [toInteger (x ^ (i :: Integer) :: GF181)]
        runAll gf181 (program x i) [] [] expectedOutput

  it "issue #25" $ do
    let program = do
          x <- input Public
          y <- input Public
          z <- inputField Public
          assert $ (x * y) `eq` z
    property $ \(x, y) -> do
      runAll gf181 program [toInteger (x :: GF181), toInteger y, toInteger (x * y)] [] []
