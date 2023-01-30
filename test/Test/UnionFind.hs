module Test.UnionFind (tests, run) where

import Control.Monad.State
import qualified Data.Map.Strict as Map
import Keelung hiding (run)
import Keelung.Compiler.Optimize.MinimizeConstraints.UnionFind (UnionFind)
import qualified Keelung.Compiler.Optimize.MinimizeConstraints.UnionFind as UnionFind
import Test.Hspec (SpecWith, describe, hspec, it)
import Test.Hspec.Expectations.Lifted

run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = do
  describe "UnionFind" $ do
    it "Find root 1" $
      runM $ do
        findAndAssert "x" (1, "x")

    it "Union 1" $
      runM $ do
        "x" `union` (1, "a")
        xs <- list
        xs `shouldBe` [("x", (1, "a"))]
        findAndAssert "x" (1, "a")

    it "Union 2" $
      runM $ do
        "z" `union` (2, "y") -- z = 2y
        "y" `union` (3, "x") -- y = 3x
        "x" `union` (5, "w") -- x = 5w = 1/3y
        "a" `union` (7, "z") -- a = 7z = 14y
        xs <- list
        xs `shouldContain` [("x", (1 / 3, "y"))]
        xs `shouldContain` [("z", (2, "y"))]
        xs `shouldContain` [("w", (1 / 15, "y"))]
        xs `shouldContain` [("a", (14, "y"))]

        findAndAssert "x" (1 / 3, "y")
        findAndAssert "z" (2, "y")
        findAndAssert "w" (1 / 15, "y")
        findAndAssert "a" (14, "y")

type M = StateT (UnionFind String GF181) IO

runM :: M a -> IO a
runM p = evalStateT p UnionFind.new

find :: String -> M (GF181, String)
find var = do
  unionFind <- get
  let (result, unionFind') = UnionFind.find var unionFind
  put unionFind'
  return result

union :: String -> (GF181, String) -> M ()
union var = modify' . UnionFind.union var

list :: M [(String, (GF181, String))]
list = gets (Map.toList . UnionFind.toMap)

findAndAssert :: String -> (GF181, String) -> M ()
findAndAssert var expected = do
  actual <- find var
  actual `shouldBe` expected