{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Compilation.Field.Conditional (tests, run) where

import Data.Field.Galois qualified as Galois
import Keelung hiding (compile)
import Test.Compilation.Util
import Test.Hspec
import Test.QuickCheck

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests = describe "conditional" $ do
  describe "constant predicate / constant branches" $ do
    let program p x y = do
          return $ cond p x (y :: Field)

    it "GF181" $ do
      property $ \(p :: Bool, x, y :: GF181) -> do
        let expected = map toInteger [if p then x else y]
        testCompiler gf181 (program (if p then true else false) (fromIntegral x) (fromIntegral y)) [] [] expected

    it "Prime 2" $ do
      property $ \(p :: Bool, x, y :: Galois.Prime 2) -> do
        let expected = map toInteger [if p then x else y]
        testCompiler (Prime 2) (program (if p then true else false) (fromIntegral x) (fromIntegral y)) [] [] expected

    it "Binary 7" $ do
      property $ \(p :: Bool, x, y :: Galois.Binary 7) -> do
        let expected = map toInteger [if p then x else y]
        testCompiler (Binary 7) (program (if p then true else false) (fromIntegral x) (fromIntegral y)) [] [] expected

  describe "variable predicate / variable branches" $ do
    let program = do
          p <- inputBool Public
          x <- inputField Public
          y <- inputField Public
          return $ cond p x y

    it "GF181" $ do
      property $ \(p :: Bool, x, y :: GF181) -> do
        let expected = map toInteger [if p then x else y]
        testCompiler gf181 program [if p then 1 else 0, fromIntegral x, fromIntegral y] [] expected

    it "Prime 2" $ do
      property $ \(p :: Bool, x, y :: Galois.Prime 2) -> do
        let expected = map toInteger [if p then x else y]
        testCompiler (Prime 2) program [if p then 1 else 0, fromIntegral x, fromIntegral y] [] expected

    it "Binary 7" $ do
      property $ \(p :: Bool, x, y :: Galois.Binary 7) -> do
        let expected = map toInteger [if p then x else y]
        testCompiler (Binary 7) program [if p then 1 else 0, fromIntegral x, fromIntegral y] [] expected