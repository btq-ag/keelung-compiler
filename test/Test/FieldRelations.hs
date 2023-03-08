module Test.FieldRelations (tests, run) where

import Control.Monad.State
import Data.Maybe qualified as Maybe
import Keelung hiding (run)
import Keelung.Compiler.Constraint
import Keelung.Compiler.Optimize.MinimizeConstraints.FieldRelations (HasRefB, FieldRelations)
import Keelung.Compiler.Optimize.MinimizeConstraints.FieldRelations qualified as FieldRelations
import Test.Hspec (SpecWith, describe, hspec, it)
import Test.Hspec.Expectations.Lifted
import Test.QuickCheck (Arbitrary (arbitrary))
import Test.QuickCheck.Arbitrary qualified as Arbitrary

run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = do
  describe "FieldRelations" $ do
    it "Relate ($0 = $1)" $
      runM $ do
        RefF 0 `relate` (1, RefF 1, 0)

        assertRelation (RefF 0) 1 (RefF 1) 0
        assertRelation (RefF 1) 1 (RefF 0) 0

    it "Relate ($0 = 2$1)" $
      runM $ do
        RefF 0 `relate` (2, RefF 1, 0) -- x = 2y
        assertRelation (RefF 0) 2 (RefF 1) 0
        assertRelation (RefF 0) 1 (RefF 0) 0
        assertRelation (RefF 1) (1 / 2) (RefF 0) 0
        assertRelation (RefF 1) 1 (RefF 1) 0

    it "Relate ($0 = 2$1 + 1)" $
      runM $ do
        RefF 0 `relate` (2, RefF 1, 1) -- x = 2y + 1
        assertRelation (RefF 0) 2 (RefF 1) 1
        assertRelation (RefF 1) (1 / 2) (RefF 0) (-1 / 2) -- y = 1/2x - 1/2
    it "Relate (x = 2y + 1 & y = 3z + 2)" $
      runM $ do
        RefF 0 `relate` (2, RefF 1, 1) -- x = 2y + 1
        RefF 1 `relate` (3, RefF 2, 2) -- y = 3z + 2

        -- x = 2y + 1
        assertRelation (RefF 0) 2 (RefF 1) 1
        -- y = 1/2x - 1/2
        assertRelation (RefF 1) (1 / 2) (RefF 0) (-1 / 2)
        -- x = 6z + 5
        assertRelation (RefF 0) 6 (RefF 2) 5
        -- z = 1/6x - 5/6
        assertRelation (RefF 2) (1 / 6) (RefF 0) (-5 / 6)
        -- y = 3z + 2
        assertRelation (RefF 1) 3 (RefF 2) 2
        -- z = 1/3y - 2/3
        assertRelation (RefF 2) (1 / 3) (RefF 1) (-2 / 3)

type M = StateT (FieldRelations RefF GF181) IO

runM :: M a -> IO a
runM p = evalStateT p FieldRelations.new

relate :: RefF -> (GF181, RefF, GF181) -> M ()
relate var val = do
  xs <- get
  forM_ (FieldRelations.relate var val xs) put

-- | Assert that `var1 = slope * var2 + intercept`
assertRelation :: RefF -> GF181 -> RefF -> GF181 -> M ()
assertRelation var1 slope var2 intercept = do
  xs <- get
  FieldRelations.relationBetween var1 var2 xs `shouldBe` Just (slope, intercept)

------------------------------------------------------------------------

instance (Arbitrary ref, Arbitrary n, GaloisField n, Ord ref, HasRefB ref) => Arbitrary (FieldRelations ref n) where
  arbitrary = do
    relations <- Arbitrary.vector 100

    return $ foldl go FieldRelations.new relations
    where
      go xs (var, slope, ref, intercept) = Maybe.fromMaybe xs (FieldRelations.relate var (slope, ref, intercept) xs)