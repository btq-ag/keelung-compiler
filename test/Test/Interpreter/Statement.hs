module Test.Interpreter.Statement (tests, run) where

import Basic qualified
import Keelung hiding (compile)
import Test.Hspec
import Test.Interpreter.Util
import Test.QuickCheck hiding ((.&.))

run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = describe "Statements" $ do
  it "assert 1" $ do
    let program = do
          x <- inputField Public
          assert (x `eq` 3)
    runAll gf181 program [3] [] []

  it "assertions intertwined with assignments" $ do
    let program = do
          xs <- thaw [0 :: Field]
          x0 <- accessM xs 0
          assert (x0 `eq` 0)
          updateM xs 0 1
          x1 <- accessM xs 0
          assert (x1 `eq` 1)
    runAll gf181 program [] [] []

  it "Basic.summation2" $
    forAll (vector 4) $ \inputs -> do
      runAll gf181 Basic.summation2 inputs [] []

  it "Basic.assertArraysEqual" $
    runAll gf181 Basic.assertArraysEqual [0, 2, 4, 8, 0, 2, 4, 8] [] []

  it "Basic.assertArraysEqual2" $
    runAll gf181 Basic.assertArraysEqual2 [0, 2, 4, 8, 0, 2, 4, 8] [] []

  it "Basic.array1D" $
    runAll gf181 (Basic.array1D 1) [2, 4] [] []

  it "Basic.array2D 1" $
    runAll gf181 (Basic.array2D 1 1) [2, 4] [] []

  it "Basic.array2D 2" $
    runAll gf181 (Basic.array2D 2 2) [0, 1, 2, 3, 0, 1, 4, 9] [] []

  it "Basic.toArray1" $
    runAll gf181 Basic.toArray1 [0 .. 7] [] []
