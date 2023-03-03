module Test.BooleanRelations (tests, run) where

import Control.Monad.State
import Data.Maybe qualified as Maybe
import Keelung hiding (run)
import Keelung.Compiler.Optimize.MinimizeConstraints.BooleanRelations (BooleanRelations)
import Keelung.Compiler.Optimize.MinimizeConstraints.BooleanRelations qualified as BooleanRelations
import Test.Hspec (SpecWith, describe, hspec, it)
import Test.Hspec.Expectations.Lifted
import Test.QuickCheck (Arbitrary (arbitrary))
import Test.QuickCheck.Arbitrary qualified as Arbitrary
import Keelung.Compiler.Constraint (RefB(..))

run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = do
  describe "BooleanRelations" $ do
    it "Relate (x = y)" $
      runM $ do
        RefB 0 `relate` (1, RefB 1)

        assertRelation (RefB 0) 1 (RefB 1) 0
        assertRelation (RefB 1) 1 (RefB 0) 0

type M = StateT (BooleanRelations GF181) IO

runM :: M a -> IO a
runM p = evalStateT p BooleanRelations.new

relate :: RefB -> (GF181, RefB) -> M ()
relate var val = do
  xs <- get
  forM_ (BooleanRelations.relate var val xs) put

-- | Assert that `var1 = slope * var2 + intercept`
assertRelation :: RefB -> GF181 -> RefB -> GF181 -> M ()
assertRelation var1 slope var2 intercept = do
  xs <- get
  BooleanRelations.relationBetween var1 var2 xs `shouldBe` Just (slope, intercept)

------------------------------------------------------------------------

instance (Arbitrary n, GaloisField n) => Arbitrary (BooleanRelations n) where
  arbitrary = do
    relations <- Arbitrary.vector 100

    return $ foldl go BooleanRelations.new relations
    where
      go xs (var, slope, ref) = Maybe.fromMaybe xs (BooleanRelations.relate var (slope, ref) xs)

instance Arbitrary RefB where
  arbitrary = RefB <$> arbitrary