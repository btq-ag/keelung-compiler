module Test.BooleanRelations (tests, run) where

import Control.Monad.State
import Data.Maybe qualified as Maybe
import Keelung.Compiler.Compile.Relations.BooleanRelations (BooleanRelations)
import Keelung.Compiler.Compile.Relations.BooleanRelations qualified as BooleanRelations
import Keelung.Compiler.Constraint (RefB (..))
import Test.Hspec (SpecWith, describe, hspec, it)
import Test.Hspec.Expectations.Lifted
import Test.QuickCheck (Arbitrary (arbitrary))
import Test.QuickCheck.Arbitrary qualified as Arbitrary

run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = do
  describe "BooleanRelations" $ do
    it "x = True" $
      runM $ do
        RefB 0 `bindToValue` True

        assertBinding (RefB 0) (Just True)

    it "x = False" $
      runM $ do
        RefB 0 `bindToValue` False

        assertBinding (RefB 0) (Just False)

    it "x = y" $
      runM $ do
        RefB 0 `relate` (True, RefB 1)

        assertRelation (RefB 0) (RefB 1) (Just True)
        assertRelation (RefB 1) (RefB 0) (Just True)

    it "x = y = True" $
      runM $ do
        RefB 0 `relate` (True, RefB 1)
        RefB 1 `bindToValue` True

        assertRelation (RefB 0) (RefB 1) (Just True)
        assertRelation (RefB 1) (RefB 0) (Just True)
        assertBinding (RefB 0) (Just True)
        assertBinding (RefB 1) (Just True)

    it "x = y = z" $
      runM $ do
        RefB 0 `relate` (True, RefB 1)
        RefB 1 `relate` (True, RefB 2)

        assertRelation (RefB 0) (RefB 1) (Just True)
        assertRelation (RefB 0) (RefB 2) (Just True)
        assertRelation (RefB 1) (RefB 0) (Just True)
        assertRelation (RefB 1) (RefB 2) (Just True)
        assertRelation (RefB 2) (RefB 0) (Just True)
        assertRelation (RefB 2) (RefB 1) (Just True)

    it "x = ¬y" $
      runM $ do
        RefB 0 `relate` (False, RefB 1)

        assertRelation (RefB 0) (RefB 1) (Just False)
        assertRelation (RefB 1) (RefB 0) (Just False)

    it "x = ¬y = True" $
      runM $ do
        RefB 0 `relate` (False, RefB 1)
        RefB 0 `bindToValue` True

        assertRelation (RefB 0) (RefB 1) (Just False)
        assertRelation (RefB 1) (RefB 0) (Just False)
        assertBinding (RefB 0) (Just True)
        assertBinding (RefB 1) (Just False)

    it "x = ¬y, z = True" $
      runM $ do
        RefB 0 `relate` (False, RefB 1)
        RefB 2 `bindToValue` True

        assertRelation (RefB 0) (RefB 1) (Just False)
        assertRelation (RefB 0) (RefB 2) Nothing
        assertRelation (RefB 1) (RefB 0) (Just False)
        assertRelation (RefB 1) (RefB 2) Nothing
        assertRelation (RefB 2) (RefB 0) Nothing
        assertRelation (RefB 2) (RefB 1) Nothing
        assertBinding (RefB 0) Nothing
        assertBinding (RefB 1) Nothing
        assertBinding (RefB 2) (Just True)

type M = StateT BooleanRelations IO

runM :: M a -> IO a
runM p = evalStateT p BooleanRelations.new

relate :: RefB -> (Bool, RefB) -> M ()
relate var val = do
  xs <- get
  forM_ (BooleanRelations.relate var val xs) put

bindToValue :: RefB -> Bool -> M ()
bindToValue var val = do
  modify' $ BooleanRelations.bindToValue var val

-- | Assert that `var1 = slope * var2 + intercept`
assertRelation :: RefB -> RefB -> Maybe Bool -> M ()
assertRelation var1 var2 result = do
  xs <- get
  BooleanRelations.relationBetween var1 var2 xs `shouldBe` result

assertBinding :: RefB -> Maybe Bool -> M ()
assertBinding var val = do
  xs <- get
  case BooleanRelations.lookup xs var of
    BooleanRelations.Constant value -> val `shouldBe` Just value
    _ -> val `shouldBe` Nothing

------------------------------------------------------------------------

instance Arbitrary BooleanRelations where
  arbitrary = do
    relations <- Arbitrary.vector 100

    return $ foldl go BooleanRelations.new relations
    where
      go xs (var, slope, ref) = Maybe.fromMaybe xs (BooleanRelations.relate var (slope, ref) xs)

instance Arbitrary RefB where
  arbitrary = RefB <$> arbitrary