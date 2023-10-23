{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Compilation.Boolean.Inequality (tests, run) where

import Control.Monad
import Keelung hiding (compile)
import Test.Compilation.Util
import Test.Hspec

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests = describe "inequality" $ do
  it "variable + constant false" $ do
    let program = do
          x <- input Public
          return $ x `neq` false
    forM_ [gf181, Prime 2, Binary 7] $ \field -> do
      runAll field program [0] [] [0]
      runAll field program [1] [] [1]

  it "variable + constant true" $ do
    let program = do
          x <- input Public
          return $ x `neq` true
    forM_ [gf181, Prime 2, Binary 7] $ \field -> do
      runAll field program [0] [] [1]
      runAll field program [1] [] [0]

  it "2 variables" $ do
    let program = do
          x <- inputBool Public
          y <- inputBool Public
          return $ x `neq` y
    forM_ [gf181, Prime 2, Binary 7] $ \field -> do
      runAll field program [0, 0] [] [0]
      runAll field program [0, 1] [] [1]
      runAll field program [1, 0] [] [1]
      runAll field program [1, 1] [] [0]
