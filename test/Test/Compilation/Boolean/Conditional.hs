{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Compilation.Boolean.Conditional (tests, run) where

import Control.Monad
import Keelung hiding (compile)
import Test.Compilation.Util
import Test.Hspec

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests = describe "conditional" $ do
  it "constant predicate / constant branches" $ do
    let program p x y = do
          return $ cond p x (y :: Boolean)
    forM_ [gf181, Prime 2, Binary 7] $ \field -> do
      testCompiler field (program false false false) [] [] [0]
      testCompiler field (program false false true) [] [] [1]
      testCompiler field (program false true false) [] [] [0]
      testCompiler field (program false true true) [] [] [1]
      testCompiler field (program true false false) [] [] [0]
      testCompiler field (program true false true) [] [] [0]
      testCompiler field (program true true false) [] [] [1]
      testCompiler field (program true true true) [] [] [1]

  it "variable predicate / variable branches" $ do
    let program = do
          p <- inputBool Public
          x <- inputBool Public
          y <- inputBool Public
          return $ cond p x y
    forM_ [gf181, Prime 2, Binary 7] $ \field -> do
      testCompiler field program [0, 0, 0] [] [0]
      testCompiler field program [0, 0, 1] [] [1]
      testCompiler field program [0, 1, 0] [] [0]
      testCompiler field program [0, 1, 1] [] [1]
      testCompiler field program [1, 0, 0] [] [0]
      testCompiler field program [1, 0, 1] [] [0]
      testCompiler field program [1, 1, 0] [] [1]
      testCompiler field program [1, 1, 1] [] [1]
