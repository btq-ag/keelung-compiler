{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Compilation.Boolean.Equality (tests, run) where

import Control.Monad
import Keelung hiding (compile)
import Test.Util
import Test.Hspec

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests = describe "equality" $ do
  it "variable + constant false" $ do
    let program = do
          x <- input Public
          return $ x `eq` false
    forM_ [gf181, Prime 2, Binary 7] $ \field -> do
      check field program [0] [] [1]
      check field program [1] [] [0]

  it "variable + constant true" $ do
    let program = do
          x <- input Public
          return $ x `eq` true
    forM_ [gf181, Prime 2, Binary 7] $ \field -> do
      check field program [0] [] [0]
      check field program [1] [] [1]

  it "2 variables" $ do
    let program = do
          x <- inputBool Public
          y <- inputBool Public
          return $ x `eq` y
    forM_ [gf181, Prime 2, Binary 7] $ \field -> do
      check field program [0, 0] [] [1]
      check field program [0, 1] [] [0]
      check field program [1, 0] [] [0]
      check field program [1, 1] [] [1]