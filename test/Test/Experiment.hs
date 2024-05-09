{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}

module Test.Experiment (run, tests) where

import Keelung hiding (MulU, VarUI)
import Keelung.Compiler.ConstraintModule (ConstraintModule (..))
import Keelung.Compiler.Relations qualified as Relations
import Keelung.Data.Reference
import Test.Hspec
import Test.QuickCheck
import Test.Util

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests = describe "Experiment" $ do
  it "Field 4" $ do
    let program = do
          let x = 4
          y <- reuse x
          return (x + y :: Field)

    assertCountO0 gf181 program 1
    assertCount gf181 program 1
    cm <- compileAsConstraintModule gf181 program :: IO (ConstraintModule GF181)
    Relations.lookup (F $ RefFO 0) (cmRelations cm) `shouldBe` Relations.Constant 8
