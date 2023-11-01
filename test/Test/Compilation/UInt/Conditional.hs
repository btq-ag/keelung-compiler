{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Compilation.UInt.Conditional (tests, run) where

import Control.Monad
import Data.Word (Word8)
import Keelung hiding (compile)
import Test.Compilation.Util
import Test.Hspec
import Test.QuickCheck

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests = describe "conditional" $ do
  it "constant predicate / constant branches" $ do
    let program p x y = do
          return $ cond p x (y :: UInt 8)

    property $ \(p :: Bool, x, y :: Word8) -> do
      let expected = map toInteger [if p then x else y]
      forM_ [gf181, Prime 2, Binary 7] $ \field -> do
        runAll field (program (if p then true else false) (fromIntegral x) (fromIntegral y)) [] [] expected

  it "variable predicate / constant branches" $ do
    let program x y = do
          p <- input Public
          return $ cond p x (y :: UInt 8)

    property $ \(p :: Bool, x, y :: Word8) -> do
      let expected = map toInteger [if p then x else y]
      forM_ [gf181, Prime 2, Binary 7] $ \field -> do
        runAll field (program (fromIntegral x) (fromIntegral y)) [if p then 1 else 0] [] expected

  it "variable predicate / constant branch + variable branch" $ do
    let program constant = do
          p <- input Public
          x <- input Public
          return $ cond p constant (x :: UInt 8)
    property $ \(p :: Bool, constant, x :: Word8) -> do
      let expected = map toInteger [if p then constant else x]
      forM_ [gf181, Prime 2, Binary 7] $ \field -> do
        runAll field (program (fromIntegral constant)) [if p then 1 else 0, fromIntegral x] [] expected

  it "variable predicate / variable branch + constant branch" $ do
    let program constant = do
          p <- input Public
          x <- input Public
          return $ cond p (x :: UInt 8) constant
    property $ \(p :: Bool, x :: Word8, constant) -> do
      let expected = map toInteger [if p then x else constant]
      forM_ [gf181, Prime 2, Binary 7] $ \field -> do
        runAll field (program (fromIntegral constant)) [if p then 1 else 0, fromIntegral x] [] expected

  it "variable predicate / variable branches" $ do
    let program = do
          p <- input Public
          x <- input Public
          y <- input Public
          return $ cond p x (y :: UInt 8)
    property $ \(p :: Bool, x, y :: Word8) -> do
      let expected = map toInteger [if p then x else y]
      forM_ [gf181, Prime 2, Binary 7] $ \field -> do
        runAll field program [if p then 1 else 0, fromIntegral x, fromIntegral y] [] expected