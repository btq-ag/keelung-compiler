{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Data.UnionFind (run, tests) where

import Control.Monad.Except (runExcept)
-- import Keelung.Compiler.Relations.Reference qualified as RefRelations

import Control.Monad.State
import Data.Field.Galois (Binary, GaloisField, Prime)
import Data.IntMap.Strict qualified as IntMap
import Data.Kind (Type)
import Data.Maybe qualified as Maybe
import Keelung (GF181, Var)
import Keelung.Compiler.Options (Options, defaultOptions)
import Keelung.Compiler.Relations qualified as Relations
import Keelung.Compiler.Relations.Reference qualified as FieldRef
import Keelung.Data.Reference (Ref (..), RefF (..))
import Keelung.Data.UnionFind.Boolean qualified as Boolean
import Keelung.Data.UnionFind.Field qualified as Field
import Test.Arbitrary ()
import Test.Hspec
import Test.QuickCheck

run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = describe "UnionFind" $ do
  -- it "error" $ do 
  --   let relates = [RelateVarBool 20 10 True,RelateVarBool 0 20 False]
  --   let xs = foldl applyRelate Boolean.new (relates :: [Relate Boolean.UnionFind Var Bool]) :: Boolean.UnionFind
  --   print xs
  --   Boolean.validate xs `shouldBe` []


  describe "operations" $ do
    describe "relate" $ do
      it "Var / Boolean" $ do
        property $ \relates -> do
          let xs = foldl applyRelate Boolean.new (relates :: [Relate (Boolean.UnionFind Bool Bool) Var Bool]) :: Boolean.UnionFind Bool Bool
          Boolean.validate xs `shouldBe` []
      it "Var / Field / GF181" $ do
        property $ \relates -> do
          let xs = foldl applyRelate Field.new (relates :: [Relate (Field.UnionFind GF181) Var GF181]) :: Field.UnionFind GF181
          Field.validate xs `shouldBe` []
      it "Var / Field / Prime 17" $ do
        property $ \relates -> do
          let xs = foldl applyRelate Field.new (relates :: [Relate (Field.UnionFind (Prime 17)) Var (Prime 17)]) :: Field.UnionFind (Prime 17)
          Field.validate xs `shouldBe` []
      it "Var / Field / Binary 7" $ do
        property $ \relates -> do
          let xs = foldl applyRelate Field.new (relates :: [Relate (Field.UnionFind (Binary 7)) Var (Binary 7)]) :: Field.UnionFind (Binary 7)
          Field.validate xs `shouldBe` []
    -- it "Ref / Field / GF181" $ do
    --   property $ \relates -> do
    --     let xs = foldl applyRelate FieldRef.new (relates :: [Relate (FieldRef.RefRelations GF181) Ref GF181]) :: FieldRef.RefRelations GF181
    --     RefRelations.isValid xs `shouldBe` True
    -- it "Ref / Field / Prime 17" $ do
    --   property $ \relates -> do
    --     let xs = foldl applyRelate FieldRef.new (relates :: [Relate (FieldRef.RefRelations (Prime 17)) Ref (Prime 17)]) :: FieldRef.RefRelations (Prime 17)
    --     RefRelations.isValid xs `shouldBe` True
    -- it "Ref / Field / Binary 7" $ do
    --   property $ \relates -> do
    --     let xs = foldl applyRelate FieldRef.new (relates :: [Relate (FieldRef.RefRelations (Binary 7)) Ref (Binary 7)]) :: FieldRef.RefRelations (Binary 7)
    --     RefRelations.isValid xs `shouldBe` True

    describe "relate and then assign" $ do
      it "Boolean" $ do
        property $ \(relates, assignments) -> do
          let xs = foldl applyRelate Boolean.new (relates :: [Relate (Boolean.UnionFind Bool Bool) Var Bool])
          let xs' = foldl applyAssign xs (assignments :: [Assign (Boolean.UnionFind Bool Bool) Var Bool])
          Boolean.validate xs' `shouldBe` []
      it "Field / GF181" $ do
        property $ \(relates, assignments) -> do
          let xs = foldl applyRelate Field.new (relates :: [Relate (Field.UnionFind GF181) Var GF181])
          let xs' = foldl applyAssign xs (assignments :: [Assign (Field.UnionFind GF181) Var GF181])
          Field.validate xs' `shouldBe` []
      it "Field / Prime 17" $ do
        property $ \(relates, assignments) -> do
          let xs = foldl applyRelate Field.new (relates :: [Relate (Field.UnionFind (Prime 17)) Var (Prime 17)])
          let xs' = foldl applyAssign xs (assignments :: [Assign (Field.UnionFind (Prime 17)) Var (Prime 17)])
          Field.validate xs' `shouldBe` []
      it "Field / Binary 7" $ do
        property $ \(relates, assignments) -> do
          let xs = foldl applyRelate Field.new (relates :: [Relate (Field.UnionFind (Binary 7)) Var (Binary 7)])
          let xs' = foldl applyAssign xs (assignments :: [Assign (Field.UnionFind (Binary 7)) Var (Binary 7)])
          Field.validate xs' `shouldBe` []

  describe "symmetricity" $ do
    it "relate and then assign" $ do
      property $ \xs -> do
        let (_assignments, families) = Field.export (xs :: Field.UnionFind GF181)
        forM_ (IntMap.toList families) $ \(root, family) -> do
          Field.lookup root xs `shouldBe` Field.Root
          forM_ (IntMap.toList family) $ \(child, (slope, intercept)) -> do
            Field.lookup child xs `shouldBe` Field.ChildOf root (Field.LinRel slope intercept)

  describe "Field.LinRel" $ do
    describe "invertLinRel . invertLinRel = id" $ do
      it "GF181" $ do
        property $ \rel -> do
          (Field.invertLinRel . Field.invertLinRel) rel `shouldBe` (rel :: Field.LinRel GF181)
      it "Prime 17" $ do
        property $ \rel -> do
          (Field.invertLinRel . Field.invertLinRel) rel `shouldBe` (rel :: Field.LinRel (Prime 17))
      it "Binary 7" $ do
        property $ \rel -> do
          (Field.invertLinRel . Field.invertLinRel) rel `shouldBe` (rel :: Field.LinRel (Binary 7))

    describe "execLinRel invertLinRel rel . execLinRel rel = id" $ do
      it "GF181" $ do
        property $ \(rel, points) -> do
          map (Field.execLinRel (Field.invertLinRel rel) . Field.execLinRel rel) points `shouldBe` (points :: [GF181])
      it "Prime 17" $ do
        property $ \(rel, points) -> do
          map (Field.execLinRel (Field.invertLinRel rel) . Field.execLinRel rel) points `shouldBe` (points :: [Prime 17])
      it "Binary 7" $ do
        property $ \(rel, points) -> do
          map (Field.execLinRel (Field.invertLinRel rel) . Field.execLinRel rel) points `shouldBe` (points :: [Binary 7])

  describe "concrete cases" $ do
    describe "Var / Field" $ do
      it "Binary 7" $ do
        let xs =
              foldl
                applyRelate
                Field.new
                ( [ RelateVarField 4 51 (1, 0),
                    RelateVarField 5 52 (1, 1),
                    RelateVarField 4 5 (2, 1)
                  ] ::
                    [Relate (Field.UnionFind (Binary 7)) Var (Binary 7)]
                )
        Field.validate xs `shouldBe` []
        Field.lookup 52 xs `shouldBe` Field.ChildOf 4 (Field.LinRel 3 2)

      it "Prime 7" $ do
        let xs =
              foldl
                applyRelate
                Field.new
                ( [ RelateVarField 4 51 (1, 0),
                    RelateVarField 5 52 (1, 1),
                    RelateVarField 4 5 (2, 1)
                  ] ::
                    [Relate (Field.UnionFind (Prime 7)) Var (Prime 7)]
                )
        Field.validate xs `shouldBe` []
        Field.lookup 52 xs `shouldBe` Field.ChildOf 4 (Field.LinRel 4 2)

    describe "Ref / Field / GF181" $ do
      it "$0 = 0" $
        runM defaultOptions $ do
          F (RefFX 0) `assign` 0 :: M GF181 ()

      it "$0 = $1" $
        runM defaultOptions $ do
          RefFX 0 `relate` (1, RefFX 1, 0) :: M GF181 ()
          assertRelation (RefFX 0) 1 (RefFX 1) 0
          assertRelation (RefFX 1) 1 (RefFX 0) 0

      it "$0 = 2$1" $
        runM defaultOptions $ do
          RefFX 0 `relate` (2, RefFX 1, 0) :: M GF181 () -- x = 2y
          assertRelation (RefFX 0) 2 (RefFX 1) 0
          assertRelation (RefFX 0) 1 (RefFX 0) 0
          assertRelation (RefFX 1) (1 / 2) (RefFX 0) 0
          assertRelation (RefFX 1) 1 (RefFX 1) 0

      it "$0 = 2$1 + 1" $
        runM defaultOptions $ do
          RefFX 0 `relate` (2, RefFX 1, 1) :: M GF181 () -- x = 2y + 1
          assertRelation (RefFX 0) 2 (RefFX 1) 1
          assertRelation (RefFX 1) (1 / 2) (RefFX 0) (-1 / 2) -- y = 1/2x - 1/2
      it "$0 = 2$1 + 1 & $1 = 3$2 + 2" $
        runM defaultOptions $ do
          RefFX 0 `relate` (2, RefFX 1, 1) :: M GF181 () -- x = 2y + 1
          RefFX 1 `relate` (3, RefFX 2, 2) -- y = 3z + 2

          -- x = 2y + 1
          assertRelation (RefFX 0) 2 (RefFX 1) 1
          -- y = 1/2x - 1/2
          assertRelation (RefFX 1) (1 / 2) (RefFX 0) (-1 / 2)
          -- x = 6z + 5
          assertRelation (RefFX 0) 6 (RefFX 2) 5
          -- z = 1/6x - 5/6
          assertRelation (RefFX 2) (1 / 6) (RefFX 0) (-5 / 6)
          -- y = 3z + 2
          assertRelation (RefFX 1) 3 (RefFX 2) 2
          -- z = 1/3y - 2/3
          assertRelation (RefFX 2) (1 / 3) (RefFX 1) (-2 / 3)

--------------------------------------------------------------------------------

data Relate :: Type -> Type -> Type -> Type where
  RelateVarField :: (GaloisField n, Integral n) => Var -> Var -> (n, n) -> Relate (Field.UnionFind n) Var n
  RelateVarBool :: Var -> Var -> Bool -> Relate (Boolean.UnionFind Bool Bool) Var Bool
  RelateRefField :: (GaloisField n, Integral n) => Ref -> Ref -> (n, n) -> Relate (FieldRef.RefRelations n) Ref n

instance (GaloisField n, Integral n, Show var) => Show (Relate (Field.UnionFind n) var n) where
  show (RelateVarField var1 var2 (slope, intercept)) = "RelateField " <> show var1 <> " " <> show var2 <> " (" <> show slope <> ", " <> show intercept <> ")"

instance (Show var) => Show (Relate (Boolean.UnionFind Bool Bool) var Bool) where
  show (RelateVarBool var1 var2 relation) = "RelateVarBool " <> show var1 <> " " <> show var2 <> " " <> show relation

instance (GaloisField n, Integral n, Show var) => Show (Relate (FieldRef.RefRelations n) var n) where
  show (RelateRefField var1 var2 (slope, intercept)) = "RelateRefField " <> show var1 <> " " <> show var2 <> " (" <> show slope <> ", " <> show intercept <> ")"

instance (Arbitrary n, GaloisField n, Integral n) => Arbitrary (Relate (Field.UnionFind n) Var n) where
  arbitrary =
    RelateVarField
      <$> chooseInt (0, 100)
      <*> chooseInt (0, 100)
      <*> ((,) <$> (arbitrary `suchThat` (/= 0)) <*> arbitrary)

instance (Arbitrary n, GaloisField n, Integral n) => Arbitrary (Relate (FieldRef.RefRelations n) Ref n) where
  arbitrary =
    RelateRefField
      <$> arbitrary
      <*> arbitrary
      <*> ((,) <$> (arbitrary `suchThat` (/= 0)) <*> arbitrary)

instance Arbitrary (Relate (Boolean.UnionFind Bool Bool) Var Bool) where
  arbitrary =
    RelateVarBool
      <$> chooseInt (0, 100)
      <*> chooseInt (0, 100)
      <*> arbitrary

applyRelate :: a -> Relate a var val -> a
applyRelate xs (RelateVarField var1 var2 (slope, intercept)) = Maybe.fromMaybe xs (Field.relate var1 var2 (Field.LinRel slope intercept) xs)
applyRelate xs (RelateVarBool var1 var2 relation) = Boolean.relate xs var1 var2 relation
applyRelate xs (RelateRefField var1 var2 (slope, intercept)) = case runExcept (FieldRef.relateR var1 slope var2 intercept xs) of
  Left err -> error (show err)
  Right (Just xs') -> xs'
  Right Nothing -> xs -- no-op

--------------------------------------------------------------------------------

data Assign :: Type -> Type -> Type -> Type where
  AssignVarField :: (GaloisField n, Integral n) => var -> n -> Assign (Field.UnionFind n) var n
  AssignVarBool :: var -> Bool -> Assign (Boolean.UnionFind Bool Bool) var Bool
  AssignRefField :: (GaloisField n, Integral n) => Ref -> n -> Assign (FieldRef.RefRelations n) Ref n

instance (GaloisField n, Integral n, Show var) => Show (Assign (Field.UnionFind n) var n) where
  show (AssignVarField var val) = "AssignVarField " <> show var <> " " <> show val

instance Show (Assign (Boolean.UnionFind Bool Bool) Var Bool) where
  show (AssignVarBool var val) = "AssignVarBool " <> show var <> " " <> show val

instance (GaloisField n, Integral n, Show var) => Show (Assign (FieldRef.RefRelations n) var n) where
  show (AssignRefField var val) = "AssignRefField " <> show var <> " " <> show val

instance {-# OVERLAPPING #-} (Arbitrary n, GaloisField n, Integral n) => Arbitrary (Assign (Field.UnionFind n) Var n) where
  arbitrary =
    AssignVarField
      <$> chooseInt (0, 100)
      <*> arbitrary

instance (Arbitrary n, GaloisField n, Integral n, Arbitrary var) => Arbitrary (Assign (Field.UnionFind n) var n) where
  arbitrary =
    AssignVarField
      <$> arbitrary
      <*> arbitrary

instance (Arbitrary n, GaloisField n, Integral n) => Arbitrary (Assign (FieldRef.RefRelations n) Ref n) where
  arbitrary =
    AssignRefField
      <$> arbitrary
      <*> arbitrary

instance Arbitrary (Assign (Boolean.UnionFind Bool Bool) Var Bool) where
  arbitrary =
    AssignVarBool
      <$> chooseInt (0, 100)
      <*> arbitrary

applyAssign :: a -> Assign a Var val -> a
applyAssign xs (AssignVarField target val) = case Field.lookup target xs of
  Field.Constant _ -> xs -- no-op
  _ -> Maybe.fromMaybe xs (Field.assign target val xs)
applyAssign xs (AssignVarBool target val) = case Boolean.lookup xs target of
  Just (Boolean.Constant _) -> xs -- no-op
  _ -> Boolean.assign xs target val

--------------------------------------------------------------------------------

instance (GaloisField n, Integral n) => Arbitrary (Field.UnionFind n) where
  arbitrary = do
    relates <- arbitrary :: Gen [Relate (Field.UnionFind n) Var n]
    assignments <- arbitrary :: Gen [Assign (Field.UnionFind n) Var n]
    let xs = foldl applyRelate Field.new relates
    return $ foldl applyAssign xs assignments

--------------------------------------------------------------------------------

instance (GaloisField val, Integral val) => Arbitrary (Field.LinRel val) where
  arbitrary = Field.LinRel <$> (arbitrary `suchThat` (/= 0)) <*> arbitrary

--------------------------------------------------------------------------------

type M n = StateT (Relations.Relations n) IO

runM :: Options -> M n a -> IO a
runM options p = evalStateT p (Relations.new options)

assign :: (GaloisField n, Integral n) => Ref -> n -> M n ()
assign var val = do
  xs <- get
  case runExcept (Relations.assignR var val xs) of
    Left err -> error $ show err
    Right Nothing -> return ()
    Right (Just result) -> put result

relate :: (GaloisField n, Integral n) => RefF -> (n, RefF, n) -> M n ()
relate var (slope, val, intercept) = do
  xs <- get
  case runExcept (Relations.relateR (F var) slope (F val) intercept xs) of
    Left err -> error $ show err
    Right Nothing -> return ()
    Right (Just result) -> put result

-- | Assert that `var1 = slope * var2 + intercept`
assertRelation :: (GaloisField n, Integral n) => RefF -> n -> RefF -> n -> M n ()
assertRelation var1 slope var2 intercept = do
  xs <- get
  lift $ Relations.relationBetween (F var1) (F var2) xs `shouldBe` Just (slope, intercept)
