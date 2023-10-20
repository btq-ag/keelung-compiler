{-# LANGUAGE ScopedTypeVariables #-}

module Test.Compilation.Field (tests, run) where

import Control.Monad
import Keelung hiding (compile)
import Test.Hspec
import Test.Compilation.Util
import Test.QuickCheck hiding ((.&.))
import qualified Test.Compilation.Field.Arithmetics

run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = describe "Field" $ do

  Test.Compilation.Field.Arithmetics.tests

  it "eq (variable / variable)" $ do
    let program = do
          x <- inputField Public
          y <- inputField Public
          return $ x `eq` y
    property $ \(x' :: GF181, y' :: GF181) -> do
      let x = x' `mod` 4
          y = y' `mod` 4
      let expectedOutput = if x == y then [1] else [0]
      runAll gf181 program [toInteger x, toInteger y] [] expectedOutput

  it "eq (variable / constant)" $ do
    let program y = do
          x <- inputField Public
          return $ x `eq` fromInteger y
    property $ \(x' :: GF181, y' :: GF181) -> do
      let x = x' `mod` 4
          y = y' `mod` 4
      let expectedOutput = if x == y then [1] else [0]
      runAll gf181 (program (toInteger y)) [toInteger x] [] expectedOutput

  it "eq (constant / constant)" $ do
    let program x y = do
          return $ fromInteger x `eq` (fromInteger y :: Field)

    property $ \(x' :: GF181, y' :: GF181) -> do
      let x = x' `mod` 4
          y = y' `mod` 4
      let expectedOutput = if x == y then [1] else [0]
      runAll gf181 (program (toInteger x) (toInteger y)) [] [] expectedOutput

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
