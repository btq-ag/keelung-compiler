module Test.UnionFind (tests, run) where

import Control.Monad.State
import Data.Map.Strict qualified as Map
import Data.Maybe qualified as Maybe
import Keelung hiding (run)
import Keelung.Compiler.Optimize.MinimizeConstraints.UnionFind (UnionFind)
import Keelung.Compiler.Optimize.MinimizeConstraints.UnionFind qualified as UnionFind
import Test.Hspec (SpecWith, describe, hspec, it)
import Test.Hspec.Expectations.Lifted
import Test.QuickCheck (Arbitrary (arbitrary))
import Test.QuickCheck.Arbitrary (Arbitrary)
import Test.QuickCheck.Arbitrary qualified as Arbitrary

run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = do
  describe "UnionFind" $ do
    it "Find root 1" $
      runM $ do
        findAndAssert "x" (1, "x", 0)

    it "Find root 1" $
      runM $ do
        lookupAndAssert "x" (1, "x", 0)

    it "Union 1" $
      runM $ do
        "x" `union` (1, "a", 0)
        xs <- list
        xs `shouldBe` [("x", (1, "a", 0))]
        findAndAssert "x" (1, "a", 0)

    it "Union 1" $
      runM $ do
        "x" `relate` (1, "a", 0)
        xs <- list
        xs `shouldBe` [("x", (1, "a", 0))]
        lookupAndAssert "x" (1, "a", 0)

    it "Union 2" $
      runM $ do
        "z" `union` (2, "y", 0) -- z = 2y
        "y" `union` (3, "x", 0) -- y = 3x
        "x" `union` (5, "w", 0) -- x = 5w = 1/3y
        "a" `union` (7, "z", 0) -- a = 7z = 14y
        xs <- list
        xs `shouldContain` [("x", (1 / 3, "y", 0))]
        xs `shouldContain` [("z", (2, "y", 0))]
        xs `shouldContain` [("w", (1 / 15, "y", 0))]
        xs `shouldContain` [("a", (14, "y", 0))]

        findAndAssert "x" (1 / 3, "y", 0)
        findAndAssert "z" (2, "y", 0)
        findAndAssert "w" (1 / 15, "y", 0)
        findAndAssert "a" (14, "y", 0)

    it "Union 2" $
      runM $ do
        "z" `relate` (2, "y", 0) -- z = 2y
        "y" `relate` (3, "x", 0) -- y = 3x
        "x" `relate` (5, "w", 0) -- x = 5w = 1/3y
        "a" `relate` (7, "z", 0) -- a = 7z = 14y
        xs <- list
        xs `shouldContain` [("x", (1 / 3, "y", 0))]
        xs `shouldContain` [("z", (2, "y", 0))]
        xs `shouldContain` [("w", (1 / 15, "y", 0))]
        xs `shouldContain` [("a", (14, "y", 0))]

        lookupAndAssert "x" (1 / 3, "y", 0)
        lookupAndAssert "z" (2, "y", 0)
        lookupAndAssert "w" (1 / 15, "y", 0)
        lookupAndAssert "a" (14, "y", 0)

    it "Union 3" $
      runM $ do
        "z" `relate` (2, "y", 4) -- z = 2y + 4
        "y" `relate` (3, "x", 1) -- y = 3x + 1
        xs <- list
        xs `shouldContain` [("x", (1 / 3, "y", -1 / 3))] -- x = (y - 1)/3
        xs `shouldContain` [("z", (2, "y", 4))] -- z = 2y + 4
        lookupAndAssert "x" (1 / 3, "y", -1 / 3)
        lookupAndAssert "z" (2, "y", 4)

type M = StateT (UnionFind String GF181) IO

runM :: M a -> IO a
runM p = evalStateT p UnionFind.new

find :: String -> M (GF181, String, GF181)
find var = do
  unionFind <- get
  let (result, unionFind') = UnionFind.find var unionFind
  put unionFind'
  return result

union :: String -> (GF181, String, GF181) -> M ()
union var = modify' . UnionFind.union var

list :: M [(String, (GF181, String, GF181))]
list = gets (Map.toList . UnionFind.toMap)

findAndAssert :: String -> (GF181, String, GF181) -> M ()
findAndAssert var expected = do
  actual <- find var
  actual `shouldBe` expected

relate :: String -> (GF181, String, GF181) -> M ()
relate var val = do
  xs <- get
  forM_ (UnionFind.relate var val xs) put

lookupAndAssert :: String -> (GF181, String, GF181) -> M ()
lookupAndAssert var expected = do
  xs <- get
  let (_varIsRoot, slope, root, intercept) = UnionFind.lookup var xs
  (slope, root, intercept) `shouldBe` expected

------------------------------------------------------------------------

instance (Arbitrary ref, Arbitrary n, GaloisField n, Ord ref) => Arbitrary (UnionFind ref n) where
  arbitrary = do
    relations <- Arbitrary.vector 100

    return $ foldl go UnionFind.new relations
    where
      go xs (var, slope, ref, intercept) = Maybe.fromMaybe xs (UnionFind.relate var (slope, ref, intercept) xs)