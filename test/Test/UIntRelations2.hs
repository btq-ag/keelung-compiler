module Test.UIntRelations2 (tests, run, debug) where

import Control.Monad.Except
import Control.Monad.State
import Keelung.Compiler.Compile.Error
import Keelung.Compiler.Compile.Relations.UIntRelations2 (UIntRelations)
import Keelung.Compiler.Compile.Relations.UIntRelations2 qualified as UIntRelations
import Keelung.Compiler.Constraint (RefU (..))
import Keelung.Field (GF181)
import Test.Hspec (SpecWith, describe, hspec, it)
import Test.Hspec.Expectations.Lifted

run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = do
  describe "UIntRelations" $ do
    describe "assign" $ do
      it "$0 = 0" $
        runM $ do
          RefUX 4 0 `assign` 0
          assertBinding (RefUX 4 0) (Just 0)
          isValid

      it "$1 = 3" $
        runM $ do
          RefUX 4 1 `assign` 3
          assertBinding (RefUX 4 1) (Just 3)
          isValid

      it "$0 = $I0 <<< 1, $0 = 3" $
        runM $ do
          RefUX 4 0 `relate` (1, RefUI 4 0)
          -- \$0 : 0011
          RefUX 4 0 `assign` 3
          -- \$I0 : 1001
          assertBinding (RefUX 4 0) (Just 3)
          assertBinding (RefUI 4 0) (Just 9)
          assertRelation (RefUX 4 0) (RefUI 4 0) Nothing
          isValid

    describe "relate" $ do
      it "$1 = $0 <<< 1" $
        runM $ do
          RefUX 4 1 `relate` (1, RefUX 4 0)
          assertRelation (RefUX 4 0) (RefUX 4 1) (Just 3) -- \$0 = $1 <<< 3
          assertRelation (RefUX 4 1) (RefUX 4 0) (Just 1) -- \$1 = $0 <<< 1
          isValid

      it "$0 = $1 <<< 3 = 5" $
        runM $ do
          RefUX 4 0 `relate` (3, RefUX 4 1)
          assertRelation (RefUX 4 0) (RefUX 4 1) (Just 3)
          assertRelation (RefUX 4 1) (RefUX 4 0) (Just 1)

          RefUX 4 1 `assign` 5
          assertBinding (RefUX 4 0) (Just 10)
          assertBinding (RefUX 4 1) (Just 5)
          isValid

      it "$0 = $1 <<< 1, $1 = $2 <<< 1" $
        runM $ do
          RefUX 4 0 `relate` (1, RefUX 4 1)
          RefUX 4 1 `relate` (1, RefUX 4 2)
          assertRelation (RefUX 4 0) (RefUX 4 1) (Just 1)
          assertRelation (RefUX 4 0) (RefUX 4 2) (Just 2)
          assertRelation (RefUX 4 1) (RefUX 4 0) (Just 3)
          assertRelation (RefUX 4 1) (RefUX 4 2) (Just 1)
          assertRelation (RefUX 4 2) (RefUX 4 0) (Just 2)
          assertRelation (RefUX 4 2) (RefUX 4 1) (Just 3)
          isValid

      it "$0 = $1 <<< 2 = True" $
        runM $ do
          RefUX 4 0 `relate` (2, RefUX 4 1)
          RefUX 4 0 `assign` 3

          assertRelation (RefUX 4 0) (RefUX 4 1) Nothing
          assertRelation (RefUX 4 1) (RefUX 4 0) Nothing
          assertBinding (RefUX 4 0) (Just 3)
          assertBinding (RefUX 4 1) (Just 12)
          isValid

      it "$0 = $1 <<< 2, $2 = True" $
        runM $ do
          RefUX 4 0 `relate` (2, RefUX 4 1)
          RefUX 4 2 `assign` 3

          assertRelation (RefUX 4 0) (RefUX 4 1) (Just 2)
          assertRelation (RefUX 4 0) (RefUX 4 2) Nothing
          assertRelation (RefUX 4 1) (RefUX 4 0) (Just 2)
          assertRelation (RefUX 4 1) (RefUX 4 2) Nothing
          assertRelation (RefUX 4 2) (RefUX 4 0) Nothing
          assertRelation (RefUX 4 2) (RefUX 4 1) Nothing
          assertBinding (RefUX 4 0) Nothing
          assertBinding (RefUX 4 1) Nothing
          assertBinding (RefUX 4 2) (Just 3)
          isValid

      it "apply `relate` many times for form a cycle" $
        runM $ do
          RefUI 4 0 `relate` (0, RefUO 4 0)
          RefUO 4 0 `relate` (0, RefUI 4 0)
          isValid

    describe "ordering of roots" $ do
      it "$0 = $1 <<< 1 = $2 <<< 2" $
        runM $ do
          RefUX 4 0 `relate` (1, RefUX 4 1)
          RefUX 4 0 `relate` (2, RefUX 4 2)
          assertRelation (RefUX 4 0) (RefUX 4 1) (Just 1)
          assertRelation (RefUX 4 0) (RefUX 4 2) (Just 2)
          isValid

      it "$0 = $1 <<< 1 = $2, $I0 overthrows $0" $
        runM $ do
          RefUX 4 0 `relate` (1, RefUX 4 1)
          RefUX 4 0 `relate` (0, RefUX 4 2)
          RefUI 4 0 `relate` (0, RefUX 4 0)
          assertRelation (RefUX 4 0) (RefUX 4 1) (Just 1)
          assertRelation (RefUX 4 0) (RefUX 4 2) (Just 0)
          assertRelation (RefUX 4 1) (RefUX 4 2) (Just 3)
          isValid

------------------------------------------------------------------------

type M = StateT (UIntRelations GF181) IO

runM :: M a -> IO a
runM p = evalStateT p UIntRelations.new

relate :: RefU -> (Int, RefU) -> M ()
relate a (rotation, b) = do
  xs <- get
  case runExcept (UIntRelations.relate a rotation b xs) of
    Left err -> error $ show (err :: Error GF181)
    Right result -> put result

assign :: RefU -> GF181 -> M ()
assign var val = do
  xs <- get
  case runExcept (UIntRelations.assign var val xs) of
    Left err -> error $ show (err :: Error GF181)
    Right result -> put result

assertRelation :: RefU -> RefU -> Maybe Int -> M ()
assertRelation var1 var2 result = do
  xs <- get
  UIntRelations.relationBetween var1 var2 xs `shouldBe` result

assertBinding :: RefU -> Maybe GF181 -> M ()
assertBinding var val = do
  xs <- get
  case UIntRelations.lookup var xs of
    UIntRelations.Value value -> Just value `shouldBe` val
    _ -> Nothing `shouldBe` val

isValid :: M ()
isValid = do
  xs <- get
  UIntRelations.isValid xs `shouldBe` True

debug :: M ()
debug = get >>= liftIO . print

------------------------------------------------------------------------

-- instance Arbitrary UIntRelations where
--   arbitrary = do
--     relations <- Arbitrary.vector 100

--     return $ foldl go UIntRelations2.new relations
--     where
--       go xs (var, slope, ref) = Maybe.fromMaybe xs (UIntRelations2.relate var (slope, ref) xs)

-- instance Arbitrary RefUX where
--   arbitrary = RefUX <$> arbitrary