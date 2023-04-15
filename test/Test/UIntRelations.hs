module Test.UIntRelations (tests, run) where

import Control.Monad.Except
import Control.Monad.State
import Keelung.Compiler.Compile.Error
import Keelung.Compiler.Compile.Relations.UIntRelations2 (UIntRelations)
import Keelung.Compiler.Compile.Relations.UIntRelations2 qualified as UIntRelations
import Keelung.Compiler.Constraint (RefU (..), RefU (RefUX))
import Keelung.Field (GF181)
import Test.Hspec (SpecWith, describe, hspec, it)
import Test.Hspec.Expectations.Lifted

run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = do
  describe "UIntRelations" $ do
    describe "assign" $ do
      -- it "$0 = 0" $
      --   runM $ do
      --     RefUX 4 0 `assign` 0
      --     assertBinding (RefUX 4 0) (Just 0)
      --     isValid

      -- it "$1 = 3" $
      --   runM $ do
      --     RefUX 4 1 `assign` 3
      --     assertBinding (RefUX 4 1) (Just 3)
      --     isValid

      it "$0 = $I0 `rotateL` 1, $0 = 3" $
        runM $ do
          RefUX 4 0 `relate` (1, RefUI 4 0)
          RefUX 4 0 `assign` 3
          debug
          -- assertBinding (RefUX 4 0) (Just 3)
          -- assertBinding (RefUI 4 0) (Just 9)

          -- assertRelation (RefUX 4 0) (RefUI 4 0) (Just 1)
          -- isValid

    -- describe "relate" $ do
    --   it "$1 = $0" $
    --     runM $ do
    --       RefUX 1 `relate` (True, RefUX 0)

    --       assertRelation (RefUX 0) (RefUX 1) (Just True)
    --       assertRelation (RefUX 1) (RefUX 0) (Just True)
    --       isValid

    --   it "$0 = $1 = True" $
    --     runM $ do
    --       RefUX 0 `relate` (True, RefUX 1)
    --       RefUX 1 `assign` True

    --       assertRelation (RefUX 0) (RefUX 1) (Just True)
    --       assertRelation (RefUX 1) (RefUX 0) (Just True)
    --       assertBinding (RefUX 0) (Just True)
    --       assertBinding (RefUX 1) (Just True)
    --       isValid

    --   it "$0 = $1 = $2" $
    --     runM $ do
    --       RefUX 0 `relate` (True, RefUX 1)
    --       RefUX 1 `relate` (True, RefUX 2)

    --       assertRelation (RefUX 0) (RefUX 1) (Just True)
    --       assertRelation (RefUX 0) (RefUX 2) (Just True)
    --       assertRelation (RefUX 1) (RefUX 0) (Just True)
    --       assertRelation (RefUX 1) (RefUX 2) (Just True)
    --       assertRelation (RefUX 2) (RefUX 0) (Just True)
    --       assertRelation (RefUX 2) (RefUX 1) (Just True)
    --       isValid

    --   it "$0 = ¬$1" $
    --     runM $ do
    --       RefUX 0 `relate` (False, RefUX 1)

    --       assertRelation (RefUX 0) (RefUX 1) (Just False)
    --       assertRelation (RefUX 1) (RefUX 0) (Just False)
    --       isValid

    --   it "$0 = ¬$1 = True" $
    --     runM $ do
    --       RefUX 0 `relate` (False, RefUX 1)
    --       RefUX 0 `assign` True

    --       assertRelation (RefUX 0) (RefUX 1) (Just False)
    --       assertRelation (RefUX 1) (RefUX 0) (Just False)
    --       assertBinding (RefUX 0) (Just True)
    --       assertBinding (RefUX 1) (Just False)
    --       isValid

    --   it "$0 = ¬$1, $2 = True" $
    --     runM $ do
    --       RefUX 0 `relate` (False, RefUX 1)
    --       RefUX 2 `assign` True

    --       assertRelation (RefUX 0) (RefUX 1) (Just False)
    --       assertRelation (RefUX 0) (RefUX 2) Nothing
    --       assertRelation (RefUX 1) (RefUX 0) (Just False)
    --       assertRelation (RefUX 1) (RefUX 2) Nothing
    --       assertRelation (RefUX 2) (RefUX 0) Nothing
    --       assertRelation (RefUX 2) (RefUX 1) Nothing
    --       assertBinding (RefUX 0) Nothing
    --       assertBinding (RefUX 1) Nothing
    --       assertBinding (RefUX 2) (Just True)
    --       isValid

    --   it "apply `relate` many times for form a cycle" $
    --     runM $ do
    --       RefUI 0 `relate` (True, RefUO 0)
    --       RefUO 0 `relate` (True, RefUI 0)

    -- describe "ordering of roots" $ do
    --   it "$0 = ¬$1 = $2" $
    --     runM $ do
    --       RefUX 0 `relate` (False, RefUX 1)
    --       RefUX 0 `relate` (True, RefUX 2)
    --       relations <- get
    --       UIntRelations.inspectChildrenOf (RefUX 1) relations `shouldBe` Just (Right (Map.fromList [(RefUX 0, False), (RefUX 2, False)]))
    --       isValid

    --   it "$0 = ¬$1 = $2, $I0 overthrows $0" $
    --     runM $ do
    --       RefUX 0 `relate` (False, RefUX 1)
    --       RefUX 0 `relate` (True, RefUX 2)
    --       RefUI 0 `relate` (True, RefUX 0)

    --       relations <- get
    --       UIntRelations.lookupOneStep (RefUX 0) relations `shouldBe` UIntRelations.ChildOf True (RefUI 0)
    --       UIntRelations.lookupOneStep (RefUX 1) relations `shouldBe` UIntRelations.ChildOf False (RefUI 0)
    --       UIntRelations.lookupOneStep (RefUX 2) relations `shouldBe` UIntRelations.ChildOf True (RefUI 0)
    --       isValid

    --   it "$0 = ¬$1, $I0 = $0, $I0 = $O0" $
    --     runM $ do
    --       RefUX 0 `relate` (False, RefUX 1)
    --       RefUI 0 `relate` (True, RefUX 0)
    --       RefUI 0 `relate` (True, RefUO 0)

    --       relations <- get
    --       -- liftIO $ print relations

    --       UIntRelations.inspectChildrenOf (RefUX 0) relations `shouldBe` Nothing
    --       UIntRelations.inspectChildrenOf (RefUX 1) relations `shouldBe` Nothing

    --       UIntRelations.inspectChildrenOf (RefUI 0) relations
    --         `shouldBe` Just
    --           ( Right $
    --               Map.fromList
    --                 [ (RefUO 0, True),
    --                   (RefUX 0, True),
    --                   (RefUX 1, False)
    --                 ]
    --           )

    --       RefUX 0 `relate` (True, RefUX 2)
    --       relations2 <- get
    --       UIntRelations.inspectChildrenOf (RefUI 0) relations2
    --         `shouldBe` Just
    --           ( Right $
    --               Map.fromList
    --                 [ (RefUO 0, True),
    --                   (RefUX 0, True),
    --                   (RefUX 1, False),
    --                   (RefUX 2, True)
    --                 ]
    --           )

    --       isValid

      -- it "UInt bits" $
      --   runM $ do
      --     let bit = RefUBit 4 (RefUX 4 0)
      --     RefUO 0 `relate` (True, RefUX 0)
      --     RefUX 0 `relate` (True, bit 0)

      --     isValid


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
    UIntRelations.Value value -> val `shouldBe` Just value
    _ -> val `shouldBe` Nothing

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