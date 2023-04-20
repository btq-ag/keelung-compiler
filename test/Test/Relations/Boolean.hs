module Test.Relations.Boolean (tests, run, debug) where

import Control.Monad.Except
import Control.Monad.State
import Keelung.Compiler.Compile.Error
import Keelung.Compiler.Compile.Relations.Boolean (BooleanRelations)
import Keelung.Compiler.Compile.Relations.Boolean qualified as BooleanRelations
import Keelung.Compiler.Compile.Relations.Relations qualified as Relations
import Keelung.Compiler.Constraint (RefB (..), RefU (RefUX))
import Keelung.Field (GF181)
import Test.Hspec (SpecWith, describe, hspec, it)
import Test.Hspec.Expectations.Lifted

run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = do
  describe "BooleanRelations" $ do
    describe "assign" $ do
      it "$0 = True" $
        runM $ do
          RefBX 0 `assign` True
          assertBinding (RefBX 0) (Just True)
          isValid

      it "$1 = False" $
        runM $ do
          RefBX 1 `assign` False
          assertBinding (RefBX 1) (Just False)
          isValid

      it "$I0 = $1, $1 = False" $
        runM $ do
          RefBX 1 `relate` (False, RefBI 0)
          RefBX 1 `assign` False
          assertBinding (RefBX 1) (Just False)
          assertBinding (RefBI 0) (Just True)
          assertRelation (RefBX 1) (RefBI 0) Nothing
          isValid

    describe "relate" $ do
      it "$1 = $0" $
        runM $ do
          RefBX 1 `relate` (True, RefBX 0)

          assertRelation (RefBX 0) (RefBX 1) (Just True)
          assertRelation (RefBX 1) (RefBX 0) (Just True)
          isValid

      it "$0 = $1 = True" $
        runM $ do
          RefBX 0 `relate` (True, RefBX 1)
          RefBX 1 `assign` True
          assertRelation (RefBX 0) (RefBX 1) Nothing
          assertRelation (RefBX 1) (RefBX 0) Nothing
          assertBinding (RefBX 0) (Just True)
          assertBinding (RefBX 1) (Just True)
          isValid

      it "$0 = $1 = $2" $
        runM $ do
          RefBX 0 `relate` (True, RefBX 1)
          RefBX 1 `relate` (True, RefBX 2)

          assertRelation (RefBX 0) (RefBX 1) (Just True)
          assertRelation (RefBX 0) (RefBX 2) (Just True)
          assertRelation (RefBX 1) (RefBX 0) (Just True)
          assertRelation (RefBX 1) (RefBX 2) (Just True)
          assertRelation (RefBX 2) (RefBX 0) (Just True)
          assertRelation (RefBX 2) (RefBX 1) (Just True)
          isValid

      it "$0 = ¬$1" $
        runM $ do
          RefBX 0 `relate` (False, RefBX 1)

          assertRelation (RefBX 0) (RefBX 1) (Just False)
          assertRelation (RefBX 1) (RefBX 0) (Just False)
          isValid

      it "$0 = ¬$1 = True" $
        runM $ do
          RefBX 0 `relate` (False, RefBX 1)
          RefBX 0 `assign` True

          assertRelation (RefBX 0) (RefBX 1) Nothing
          assertRelation (RefBX 1) (RefBX 0) Nothing
          assertBinding (RefBX 0) (Just True)
          assertBinding (RefBX 1) (Just False)
          isValid

      it "$0 = ¬$1, $2 = True" $
        runM $ do
          RefBX 0 `relate` (False, RefBX 1)
          RefBX 2 `assign` True

          assertRelation (RefBX 0) (RefBX 1) (Just False)
          assertRelation (RefBX 0) (RefBX 2) Nothing
          assertRelation (RefBX 1) (RefBX 0) (Just False)
          assertRelation (RefBX 1) (RefBX 2) Nothing
          assertRelation (RefBX 2) (RefBX 0) Nothing
          assertRelation (RefBX 2) (RefBX 1) Nothing
          assertBinding (RefBX 0) Nothing
          assertBinding (RefBX 1) Nothing
          assertBinding (RefBX 2) (Just True)
          isValid

      it "apply `relate` many times for form a cycle" $
        runM $ do
          RefBI 0 `relate` (True, RefBO 0)
          RefBO 0 `relate` (True, RefBI 0)
          assertRelation (RefBO 0) (RefBI 0) (Just True)
          assertRelation (RefBI 0) (RefBO 0) (Just True)
          isValid

      it "UInt bits" $
        runM $ do
          let bit = RefUBit 4 (RefUX 4 0)
          RefBO 0 `relate` (True, RefBX 0)
          RefBX 0 `relate` (True, bit 0)
          assertRelation (RefBO 0) (RefBX 0) (Just True)
          assertRelation (RefBO 0) (bit 0) (Just True)
          assertRelation (bit 0) (RefBX 0) (Just True)
          isValid

    describe "ordering of roots" $ do
      it "$0 = ¬$1 = $2" $
        runM $ do
          RefBX 0 `relate` (False, RefBX 1)
          RefBX 0 `relate` (True, RefBX 2)
          assertRelation (RefBX 0) (RefBX 1) (Just False)
          assertRelation (RefBX 0) (RefBX 2) (Just True)
          assertRelation (RefBX 1) (RefBX 2) (Just False)
          isValid

      it "$0 = ¬$1 = $2, $I0 overthrows $0" $
        runM $ do
          RefBX 0 `relate` (False, RefBX 1)
          RefBX 0 `relate` (True, RefBX 2)
          RefBI 0 `relate` (True, RefBX 0)
          assertRelation (RefBX 0) (RefBX 1) (Just False)
          assertRelation (RefBX 0) (RefBX 2) (Just True)
          assertRelation (RefBX 1) (RefBX 2) (Just False)
          assertRelation (RefBI 0) (RefBX 0) (Just True)
          assertRelation (RefBI 0) (RefBX 1) (Just False)
          assertRelation (RefBI 0) (RefBX 2) (Just True)
          isValid

      it "$0 = ¬$1, $I0 = $0, $I0 = $O0" $
        runM $ do
          RefBX 0 `relate` (False, RefBX 1)
          RefBI 0 `relate` (True, RefBX 0)
          RefBI 0 `relate` (True, RefBO 0)
          assertRelation (RefBX 0) (RefBX 1) (Just False)
          assertRelation (RefBI 0) (RefBX 0) (Just True)
          assertRelation (RefBI 0) (RefBX 1) (Just False)

          RefBX 0 `relate` (True, RefBX 2)

          assertRelation (RefBX 0) (RefBX 2) (Just True)
          assertRelation (RefBX 1) (RefBX 2) (Just False)
          assertRelation (RefBI 0) (RefBX 2) (Just True)

          isValid

------------------------------------------------------------------------

type M = StateT BooleanRelations IO

runM :: M a -> IO a
runM p = evalStateT p BooleanRelations.new

relate :: RefB -> (Bool, RefB) -> M ()
relate a (polarity, b) = do
  xs <- get
  case runExcept (Relations.runM $ BooleanRelations.relate a polarity b xs) of
    Left err -> error $ show (err :: Error GF181)
    Right Nothing -> return ()
    Right (Just result) -> put result

assign :: RefB -> Bool -> M ()
assign var val = do
  xs <- get
  case runExcept (Relations.runM $ BooleanRelations.assign var val xs) of
    Left err -> error $ show (err :: Error GF181)
    Right Nothing -> return ()
    Right (Just result) -> put result

assertRelation :: RefB -> RefB -> Maybe Bool -> M ()
assertRelation var1 var2 result = do
  xs <- get
  BooleanRelations.relationBetween var1 var2 xs `shouldBe` result

assertBinding :: RefB -> Maybe Bool -> M ()
assertBinding var val = do
  xs <- get
  case BooleanRelations.lookup var xs of
    BooleanRelations.Value value -> Just value `shouldBe` val
    _ -> Nothing `shouldBe` val

isValid :: M ()
isValid = do
  xs <- get
  BooleanRelations.isValid xs `shouldBe` True

------------------------------------------------------------------------

debug :: M ()
debug = get >>= liftIO . print

-- instance Arbitrary BooleanRelations where
--   arbitrary = do
--     relations <- Arbitrary.vector 100

--     return $ foldl go Boolean.new relations
--     where
--       go xs (var, slope, ref) = Maybe.fromMaybe xs (Boolean.relate var (slope, ref) xs)

-- instance Arbitrary RefBX where
--   arbitrary = RefBX <$> arbitrary
