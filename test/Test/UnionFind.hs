module Test.UnionFind (tests, run) where

import Control.Monad.State
import Data.Maybe qualified as Maybe
import Keelung hiding (run)
import Keelung.Compiler.Optimize.MinimizeConstraints.UnionFind (UnionFind)
import Keelung.Compiler.Optimize.MinimizeConstraints.UnionFind qualified as UnionFind
import Test.Hspec (SpecWith, describe, hspec, it)
import Test.Hspec.Expectations.Lifted
import Test.QuickCheck (Arbitrary (arbitrary))
import Test.QuickCheck.Arbitrary qualified as Arbitrary

run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = do
  describe "UnionFind" $ do
    it "Relate (x = y)" $
      runM $ do
        "x" `relate` (1, "y", 0)

        assertRelation "x" 1 "y" 0
        assertRelation "y" 1 "x" 0

    it "Relate (x = 2y)" $
      runM $ do
        "x" `relate` (2, "y", 0) -- x = 2y
        assertRelation "x" 2 "y" 0
        assertRelation "x" 1 "x" 0
        assertRelation "y" (1 / 2) "x" 0
        assertRelation "y" 1 "y" 0

    it "Relate (x = 2y + 1)" $
      runM $ do
        "x" `relate` (2, "y", 1) -- x = 2y + 1
        assertRelation "x" 2 "y" 1
        assertRelation "y" (1 / 2) "x" (-1 / 2) -- y = 1/2x - 1/2
    it "Relate (x = 2y + 1 & y = 3z + 2)" $
      runM $ do
        "x" `relate` (2, "y", 1) -- x = 2y + 1
        "y" `relate` (3, "z", 2) -- y = 3z + 2

        -- x = 2y + 1
        assertRelation "x" 2 "y" 1
        -- y = 1/2x - 1/2
        assertRelation "y" (1 / 2) "x" (-1 / 2)
        -- x = 6z + 5
        assertRelation "x" 6 "z" 5
        -- z = 1/6x - 5/6
        assertRelation "z" (1 / 6) "x" (-5 / 6)
        -- y = 3z + 2
        assertRelation "y" 3 "z" 2
        -- z = 1/3y - 2/3
        assertRelation "z" (1 / 3) "y" (-2 / 3)

type M = StateT (UnionFind String GF181) IO

runM :: M a -> IO a
runM p = evalStateT p UnionFind.new

relate :: String -> (GF181, String, GF181) -> M ()
relate var val = do
  xs <- get
  forM_ (UnionFind.relate var val xs) put

-- | Assert that `var1 = slope * var2 + intercept`
assertRelation :: String -> GF181 -> String -> GF181 -> M ()
assertRelation var1 slope var2 intercept = do
  xs <- get
  UnionFind.relationBetween var1 var2 xs `shouldBe` Just (slope, intercept)

------------------------------------------------------------------------

instance (Arbitrary ref, Arbitrary n, GaloisField n, Ord ref) => Arbitrary (UnionFind ref n) where
  arbitrary = do
    relations <- Arbitrary.vector 100

    return $ foldl go UnionFind.new relations
    where
      go xs (var, slope, ref, intercept) = Maybe.fromMaybe xs (UnionFind.relate var (slope, ref, intercept) xs)