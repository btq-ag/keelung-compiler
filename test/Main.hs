{-# LANGUAGE DataKinds #-}

module Main where

import Test.Compilation qualified as Compilation
import Test.Data.IntervalTree qualified as Data.IntervalTree
import Test.Data.LC qualified as Data.LC
import Test.Hspec (hspec)
import Test.IndexTable qualified as IndexTable
import Test.Intergration qualified as Intergration
import Test.Optimization qualified as Optimization
import Test.Relations qualified as Relations
import Test.Solver qualified as Solver

main :: IO ()
main = hspec $ do
  Solver.tests
  Compilation.tests
  Optimization.tests
  IndexTable.tests
  Relations.tests
  Intergration.tests
  Data.LC.tests
  Data.IntervalTree.tests
