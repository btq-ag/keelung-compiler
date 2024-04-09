{-# LANGUAGE ScopedTypeVariables #-}

module Test.Compilation.Field (tests, run) where

import Keelung hiding (compile)
import Test.Compilation.Field.Arithmetics qualified
import Test.Compilation.Field.Conditional qualified
import Test.Compilation.Field.Equality qualified
import Test.Compilation.Field.Exponentiation qualified
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
  Test.Compilation.Field.Conditional.tests
  Test.Compilation.Field.Exponentiation.tests

  it "issue #25" $ do
    let program = do
          x <- input Public
          y <- input Public
          z <- inputField Public
          assert $ (x * y) `eq` z
    property $ \(x, y) -> do
      validate gf181 program [toInteger (x :: GF181), toInteger y, toInteger (x * y)] [] []