module Test.BooleanRelations2 (tests, run) where

import Control.Monad.Except
import Control.Monad.State
import Data.Map.Strict qualified as Map
import Keelung.Compiler.Compile.Error
import Keelung.Compiler.Compile.Relations.BooleanRelations2 (BooleanRelations)
import Keelung.Compiler.Compile.Relations.BooleanRelations2 qualified as BooleanRelations
import Keelung.Compiler.Constraint (RefB (..))
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
          assertRelation (RefBX 1) (RefBI 0) (Just False)
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

          assertRelation (RefBX 0) (RefBX 1) (Just True)
          assertRelation (RefBX 1) (RefBX 0) (Just True)
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

          assertRelation (RefBX 0) (RefBX 1) (Just False)
          assertRelation (RefBX 1) (RefBX 0) (Just False)
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

    describe "ordering of roots" $ do
      it "$0 = ¬$1 = $2" $
        runM $ do
          RefBX 0 `relate` (False, RefBX 1)
          RefBX 0 `relate` (True, RefBX 2)
          relations <- get
          BooleanRelations.inspectChildrenOf (RefBX 1) relations `shouldBe` Just (Right (Map.fromList [(RefBX 0, False), (RefBX 2, False)]))
          isValid

      it "$0 = ¬$1 = $2, $I0 overthrows $0" $
        runM $ do
          RefBX 0 `relate` (False, RefBX 1)
          RefBX 0 `relate` (True, RefBX 2)
          RefBI 0 `relate` (True, RefBX 0)

          relations <- get
          BooleanRelations.lookupOneStep (RefBX 0) relations `shouldBe` BooleanRelations.ChildOf True (RefBI 0)
          BooleanRelations.lookupOneStep (RefBX 1) relations `shouldBe` BooleanRelations.ChildOf False (RefBI 0)
          BooleanRelations.lookupOneStep (RefBX 2) relations `shouldBe` BooleanRelations.ChildOf True (RefBI 0)
          isValid

      it "$0 = ¬$1, $I0 = $0, $I0 = $O0" $
        runM $ do
          RefBX 0 `relate` (False, RefBX 1)
          RefBI 0 `relate` (True, RefBX 0)
          RefBI 0 `relate` (True, RefBO 0)

          relations <- get
          -- liftIO $ print relations

          BooleanRelations.inspectChildrenOf (RefBX 0) relations `shouldBe` Nothing
          BooleanRelations.inspectChildrenOf (RefBX 1) relations `shouldBe` Nothing

          BooleanRelations.inspectChildrenOf (RefBI 0) relations
            `shouldBe` Just
              ( Right $
                  Map.fromList
                    [ (RefBO 0, True),
                      (RefBX 0, True),
                      (RefBX 1, False)
                    ]
              )

          RefBX 0 `relate` (True, RefBX 2)
          relations2 <- get
          BooleanRelations.inspectChildrenOf (RefBI 0) relations2
            `shouldBe` Just
              ( Right $
                  Map.fromList
                    [ (RefBO 0, True),
                      (RefBX 0, True),
                      (RefBX 1, False),
                      (RefBX 2, True)
                    ]
              )

          isValid

------------------------------------------------------------------------

type M = StateT BooleanRelations IO

runM :: M a -> IO a
runM p = evalStateT p BooleanRelations.new

relate :: RefB -> (Bool, RefB) -> M ()
relate a (polarity, b) = do
  xs <- get
  case runExcept (BooleanRelations.relate a polarity b xs) of
    Left err -> error $ show (err :: Error GF181)
    Right result -> put result

-- modify' $ BooleanRelations.relate a polarity b

assign :: RefB -> Bool -> M ()
assign var val = do
  xs <- get
  case runExcept (BooleanRelations.assign var val xs) of
    Left err -> error $ show (err :: Error GF181)
    Right result -> put result

assertRelation :: RefB -> RefB -> Maybe Bool -> M ()
assertRelation var1 var2 result = do
  xs <- get
  BooleanRelations.relationBetween var1 var2 xs `shouldBe` result

assertBinding :: RefB -> Maybe Bool -> M ()
assertBinding var val = do
  xs <- get
  case BooleanRelations.lookup var xs of
    BooleanRelations.Value value -> val `shouldBe` Just value
    _ -> val `shouldBe` Nothing

isValid :: M ()
isValid = do
  xs <- get
  BooleanRelations.isValid xs `shouldBe` True

------------------------------------------------------------------------

-- instance Arbitrary BooleanRelations where
--   arbitrary = do
--     relations <- Arbitrary.vector 100

--     return $ foldl go BooleanRelations2.new relations
--     where
--       go xs (var, slope, ref) = Maybe.fromMaybe xs (BooleanRelations2.relate var (slope, ref) xs)

-- instance Arbitrary RefBX where
--   arbitrary = RefBX <$> arbitrary