{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}

module Test.Data.UnionFind (run, tests) where

import Control.Monad.Except (runExcept)
import Control.Monad.State
import Data.Field.Galois (Binary, GaloisField, Prime)
import Data.IntMap.Strict qualified as IntMap
import Data.Kind (Type)
import Data.Maybe qualified as Maybe
import Keelung (GF181, Var)
import Keelung.Compiler.Options (Options, defaultOptions)
import Keelung.Compiler.Options qualified as Options
import Keelung.Compiler.Relations qualified as Relations
import Keelung.Compiler.Relations.EquivClass qualified as EC
import Keelung.Compiler.Relations.Monad (Seniority)
import Keelung.Compiler.Relations.Reference ()
import Keelung.Data.Reference (Ref (..), RefB (..), RefF (..))
import Keelung.Data.UnionFind qualified as UnionFind
import Keelung.Data.UnionFind.Boolean qualified as Boolean
import Keelung.Data.UnionFind.Field qualified as Field
import Keelung.Data.UnionFind.Relation qualified as UnionFind.Relation
import Keelung.Field qualified as Field
import Test.Arbitrary ()
import Test.Hspec
import Test.QuickCheck

run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = describe "UnionFind" $ do
  -- -- it "Relations / Ref / GF181" $ do
  -- --   property $ \relates -> do
  -- --     let xs = foldl applyRelate (Relations.new (Options.new Field.gf181)) (relates :: [Relate (Relations.Relations GF181) Ref GF181]) :: Relations.Relations GF181
  -- --     Relations.isValid xs `shouldBe` True
  -- it "error" $ do
  --   --  [RelateRelations F0 BP0 (P (1078936104348021732734147004977251905910385367168331932 `modulo` 1552511030102430251236801561344621993261920897571225601), P (175045228176580001514165878868385845338554771781719336 `modulo` 1552511030102430251236801561344621993261920897571225601)),RelateRelations F0 FI5 (P (105946717925123061829485584721240966793283594296367397 `modulo` 1552511030102430251236801561344621993261920897571225601), P (476199024211118671754238663712601041772701772451390232 `modulo` 1552511030102430251236801561344621993261920897571225601))]
  --   let relates =
  --         [ RelateRelations (F (RefFX 0)) (B (RefBP 0)) (1, 2),
  --           RelateRelations (F (RefFX 0)) (B (RefBI 5)) (3, 4)
  --         ]
  --   -- [(BP0,[(F0,LinRel 1 2),(BI5,LinRel (P (1035007353401620167491201040896414662174613931714150401)) (P (1035007353401620167491201040896414662174613931714150400)))])]

  --   let xs = foldl applyRelate (Relations.new (Options.new Field.gf181)) (relates :: [Relate (Relations.Relations GF181) Ref GF181]) :: Relations.Relations GF181
  --   print xs
  --   Relations.validate xs `shouldBe` []

  describe "operations" $ do
    describe "relate" $ do
      it "Var / Boolean" $ do
        property $ \relates -> do
          let xs = foldl applyRelate Boolean.new (relates :: [Relate (Boolean.UnionFind Bool Boolean.Rel) Var Bool]) :: Boolean.UnionFind Bool Boolean.Rel
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
      it "Relations / Ref / GF181" $ do
        property $ \relates -> do
          let xs = foldl applyRelate (Relations.new (Options.new Field.gf181)) (relates :: [Relate (Relations.Relations GF181) Ref GF181]) :: Relations.Relations GF181
          Relations.validate xs `shouldBe` []
      it "Relations / Ref / Prime 17" $ do
        property $ \relates -> do
          let xs = foldl applyRelate (Relations.new (Options.new (Field.Prime 17))) (relates :: [Relate (Relations.Relations (Prime 17)) Ref (Prime 17)]) :: Relations.Relations (Prime 17)
          Relations.validate xs `shouldBe` []
      it "Relations / Ref / Binary 7" $ do
        property $ \relates -> do
          let xs = foldl applyRelate (Relations.new (Options.new (Field.Binary 7))) (relates :: [Relate (Relations.Relations (Binary 7)) Ref (Binary 7)]) :: Relations.Relations (Binary 7)
          Relations.validate xs `shouldBe` []
      it "EC / Ref / GF181" $ do
        property $ \relates -> do
          let xs = foldl applyRelate (EC.new "Ref / GF181") (relates :: [Relate (EC.EquivClass Ref GF181 (Field.LinRel GF181)) Ref GF181]) :: EC.EquivClass Ref GF181 (Field.LinRel GF181)
          EC.validate xs `shouldBe` []
    -- it "Relations / Ref / Prime 17" $ do
    --   property $ \relates -> do
    --     let xs = foldl applyRelate (Relations.new (Options.new (Field.Prime 17))) (relates :: [Relate (Relations.Relations (Prime 17)) Ref (Prime 17)]) :: Relations.Relations (Prime 17)
    --     Relations.validate xs `shouldBe` []
    -- it "Relations / Ref / Binary 7" $ do
    --   property $ \relates -> do
    --     let xs = foldl applyRelate (Relations.new (Options.new (Field.Binary 7))) (relates :: [Relate (Relations.Relations (Binary 7)) Ref (Binary 7)]) :: Relations.Relations (Binary 7)
    --     Relations.validate xs `shouldBe` []

    describe "relate and then assign" $ do
      it "Boolean" $ do
        property $ \(relates, assignments) -> do
          let xs = foldl applyRelate Boolean.new (relates :: [Relate (Boolean.UnionFind Bool Boolean.Rel) Var Bool])
          let xs' = foldl applyAssign xs (assignments :: [Assign (Boolean.UnionFind Bool Boolean.Rel) Var Bool])
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
        forM_ (IntMap.toList families) $ \(root, (_range, family)) -> do
          Field.lookup root xs `shouldBe` Field.Root mempty
          forM_ (IntMap.toList family) $ \(child, (slope, intercept)) -> do
            Field.lookup child xs `shouldBe` Field.ChildOf root (Field.LinRel slope intercept) mempty

  describe "Field.LinRel" $ do
    describe "invertLinRel . invertLinRel = id" $ do
      it "GF181" $ do
        property $ \rel -> do
          (UnionFind.Relation.invert . UnionFind.Relation.invert) rel `shouldBe` (rel :: Field.LinRel GF181)
      it "Prime 17" $ do
        property $ \rel -> do
          (UnionFind.Relation.invert . UnionFind.Relation.invert) rel `shouldBe` (rel :: Field.LinRel (Prime 17))
      it "Binary 7" $ do
        property $ \rel -> do
          (UnionFind.Relation.invert . UnionFind.Relation.invert) rel `shouldBe` (rel :: Field.LinRel (Binary 7))

  describe "execLinRel invertLinRel rel . execLinRel rel = id" $ do
    it "GF181" $ do
      property $ \(rel, points) -> do
        map (UnionFind.Relation.execute (UnionFind.Relation.invert rel) . UnionFind.Relation.execute (rel :: Field.LinRel GF181)) points `shouldBe` (points :: [Field.Wrapper GF181])
    it "Prime 17" $ do
      property $ \(rel, points) -> do
        map (UnionFind.Relation.execute (UnionFind.Relation.invert rel) . UnionFind.Relation.execute (rel :: Field.LinRel (Prime 17))) points `shouldBe` (points :: [Field.Wrapper (Prime 17)])
    it "Binary 7" $ do
      property $ \(rel, points) -> do
        map (UnionFind.Relation.execute (UnionFind.Relation.invert rel) . UnionFind.Relation.execute (rel :: Field.LinRel (Binary 7))) points `shouldBe` (points :: [Field.Wrapper (Binary 7)])

  describe "Concrete cases: relate + desginate range" $ do
    describe "Var / Field" $ do
      it "GF181" $ do
        let xs =
              foldl
                applyRelate
                Field.new
                ( [ RelateVarField 0 1 (1, 0),
                    -- \$0 = $1
                    RelateVarField 0 2 (1, -1),
                    -- \$0 = $2 - 1
                    RelateVarField 0 3 (1, 1),
                    -- \$0 = $3 + 1
                    RelateVarField 0 4 (2, 3)
                  ] ::
                    -- \$0 = 2$4 + 3

                    [Relate (Field.UnionFind GF181) Var GF181]
                )
        let xs' =
              foldl
                applyDesignateRange
                xs
                ( [ DesignateRangeVarField 0 (UnionFind.Range (Just (Field.Wrapper 0, Field.Wrapper 2)))
                  ] ::
                    [DesignateRange (Field.UnionFind GF181) Var GF181]
                )
        Field.validate xs' `shouldBe` []
        Field.lookup 1 xs' `shouldBe` Field.ChildOf 0 (Field.LinRel 1 0) (UnionFind.Range (Just (Field.Wrapper 0, Field.Wrapper 2)))
        Field.lookup 2 xs' `shouldBe` Field.ChildOf 0 (Field.LinRel 1 1) (UnionFind.Range (Just (Field.Wrapper 1, Field.Wrapper 3)))
        Field.lookup 3 xs' `shouldBe` Field.ChildOf 0 (Field.LinRel 1 (-1)) (UnionFind.Range (Just (Field.Wrapper (-1), Field.Wrapper 1)))
        Field.lookup 4 xs' `shouldBe` Field.ChildOf 0 (Field.LinRel (1 / 2) (-3 / 2)) (UnionFind.Range (Just (Field.Wrapper (-3 / 2), Field.Wrapper (-1 / 2))))

  describe "Concrete cases: assign + relate" $ do
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
        Field.lookup 52 xs `shouldBe` Field.ChildOf 4 (Field.LinRel 3 2) mempty

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
        Field.lookup 52 xs `shouldBe` Field.ChildOf 4 (Field.LinRel 4 2) mempty

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
  RelateVarBool :: Var -> Var -> Bool -> Relate (Boolean.UnionFind Bool Boolean.Rel) Var Bool
  RelateRelations :: (GaloisField n, Integral n) => Ref -> Ref -> (n, n) -> Relate (Relations.Relations n) Ref n
  RelateEC :: (GaloisField n, Integral n, Seniority var, Ord var) => var -> var -> (n, n) -> Relate (EC.EquivClass var n (Field.LinRel n)) var n

instance (GaloisField n, Integral n, Show var) => Show (Relate (Field.UnionFind n) var n) where
  show (RelateVarField var1 var2 (slope, intercept)) = "RelateField " <> show var1 <> " " <> show var2 <> " (" <> show slope <> ", " <> show intercept <> ")"

instance (Show var) => Show (Relate (Boolean.UnionFind Bool Boolean.Rel) var Bool) where
  show (RelateVarBool var1 var2 relation) = "RelateVarBool " <> show var1 <> " " <> show var2 <> " " <> show relation

instance (GaloisField n, Integral n, Show var) => Show (Relate (Relations.Relations n) var n) where
  show (RelateRelations var1 var2 (slope, intercept)) = "RelateRelations " <> show var1 <> " " <> show var2 <> " (" <> show slope <> ", " <> show intercept <> ")"

instance (GaloisField n, Integral n, Show var) => Show (Relate (EC.EquivClass Ref n (Field.LinRel n)) var n) where
  show (RelateEC var1 var2 (slope, intercept)) = "RelateEC " <> show var1 <> " " <> show var2 <> " (" <> show slope <> ", " <> show intercept <> ")"

instance (Arbitrary n, GaloisField n, Integral n) => Arbitrary (Relate (Field.UnionFind n) Var n) where
  arbitrary =
    RelateVarField
      <$> chooseInt (0, 100)
      <*> chooseInt (0, 100)
      <*> ((,) <$> (arbitrary `suchThat` (/= 0)) <*> arbitrary)

instance (Arbitrary n, GaloisField n, Integral n) => Arbitrary (Relate (Relations.Relations n) Ref n) where
  arbitrary =
    RelateRelations
      <$> arbitrary
      <*> arbitrary
      <*> ((,) <$> (arbitrary `suchThat` (/= 0)) <*> arbitrary)

instance Arbitrary (Relate (Boolean.UnionFind Bool Boolean.Rel) Var Bool) where
  arbitrary =
    RelateVarBool
      <$> chooseInt (0, 100)
      <*> chooseInt (0, 100)
      <*> arbitrary

instance (GaloisField n, Integral n, Arbitrary n, Arbitrary var, Seniority var, Ord var) => Arbitrary (Relate (EC.EquivClass var n (Field.LinRel n)) var n) where
  arbitrary =
    RelateEC
      <$> arbitrary
      <*> arbitrary
      <*> arbitrary

applyRelate :: a -> Relate a var val -> a
applyRelate xs (RelateVarField var1 var2 (slope, intercept)) = Maybe.fromMaybe xs (Field.relate var1 var2 (Field.LinRel slope intercept) xs)
applyRelate xs (RelateVarBool var1 var2 relation) = Maybe.fromMaybe xs (UnionFind.relate var1 var2 (Boolean.Rel relation) xs)
applyRelate xs (RelateRelations var1 var2 (slope, intercept)) = case runExcept (Relations.relateRef var1 slope var2 intercept xs) of
  Left err -> error (show err)
  Right (Just xs') -> xs'
  Right Nothing -> xs -- no-op
applyRelate xs (RelateEC var1 var2 (slope, intercept)) = case runExcept (EC.runM (EC.relate var1 (Field.LinRel slope intercept) var2 xs)) of
  Left err -> error (show err)
  Right (Just xs') -> xs'
  Right Nothing -> xs -- no-op

--------------------------------------------------------------------------------

data Assign :: Type -> Type -> Type -> Type where
  AssignVarField :: (GaloisField n, Integral n) => var -> n -> Assign (Field.UnionFind n) var n
  AssignVarBool :: var -> Bool -> Assign (Boolean.UnionFind Bool Boolean.Rel) var Bool
  AssignRelations :: (GaloisField n, Integral n) => Ref -> n -> Assign (Relations.Relations n) Ref n

instance (GaloisField n, Integral n, Show var) => Show (Assign (Field.UnionFind n) var n) where
  show (AssignVarField var val) = "AssignVarField " <> show var <> " " <> show val

instance Show (Assign (Boolean.UnionFind Bool Boolean.Rel) Var Bool) where
  show (AssignVarBool var val) = "AssignVarBool " <> show var <> " " <> show val

instance (GaloisField n, Integral n, Show var) => Show (Assign (Relations.Relations n) var n) where
  show (AssignRelations var val) = "Assign Relations " <> show var <> " " <> show val

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

instance (Arbitrary n, GaloisField n, Integral n) => Arbitrary (Assign (Relations.Relations n) Ref n) where
  arbitrary =
    AssignRelations
      <$> arbitrary
      <*> arbitrary

instance Arbitrary (Assign (Boolean.UnionFind Bool Boolean.Rel) Var Bool) where
  arbitrary =
    AssignVarBool
      <$> chooseInt (0, 100)
      <*> arbitrary

applyAssign :: a -> Assign a Var val -> a
applyAssign xs (AssignVarField target val) = case Field.lookup target xs of
  Field.Constant _ -> xs -- no-op
  _ -> Maybe.fromMaybe xs (Field.assign target (Field.Wrapper val) xs)
applyAssign xs (AssignVarBool target val) = case UnionFind.lookup target xs of
  UnionFind.Constant _ -> xs -- no-op
  _ -> Maybe.fromMaybe xs (Boolean.assign target val xs)

--------------------------------------------------------------------------------

data DesignateRange :: Type -> Type -> Type -> Type where
  DesignateRangeVarField :: (GaloisField n, Integral n) => Var -> UnionFind.Range (Field.Wrapper n) -> DesignateRange (Field.UnionFind n) Var n

-- DesignateRangeRefField :: (GaloisField n, Integral n) => Ref -> UnionFind.Range n -> DesignateRange (Field.UnionFind n) Var n
-- DesignateRangeRefField :: (GaloisField n, Integral n) => Ref -> Ref -> (n, n) -> Relate (Relations.Relations n) Ref n

applyDesignateRange :: a -> DesignateRange a var val -> a
applyDesignateRange xs (DesignateRangeVarField var range) = Maybe.fromMaybe xs (Field.designateRange var range xs)

--------------------------------------------------------------------------------

instance (GaloisField n, Integral n) => Arbitrary (Field.UnionFind n) where
  arbitrary = do
    relates <- arbitrary :: Gen [Relate (Field.UnionFind n) Var n]
    assignments <- arbitrary :: Gen [Assign (Field.UnionFind n) Var n]
    let xs = foldl applyRelate Field.new relates
    return $ foldl applyAssign xs assignments

instance (Arbitrary n) => Arbitrary (Field.Wrapper n) where
  arbitrary = Field.Wrapper <$> arbitrary

--------------------------------------------------------------------------------

instance (GaloisField val, Integral val) => Arbitrary (Field.LinRel val) where
  arbitrary = Field.LinRel <$> (arbitrary `suchThat` (/= 0)) <*> arbitrary

instance Arbitrary Boolean.Rel where
  arbitrary = Boolean.Rel <$> arbitrary

--------------------------------------------------------------------------------

type M n = StateT (Relations.Relations n) IO

runM :: Options -> M n a -> IO a
runM options p = evalStateT p (Relations.new options)

assign :: (GaloisField n, Integral n) => Ref -> n -> M n ()
assign var val = do
  xs <- get
  case runExcept (Relations.assignRef var val xs) of
    Left err -> error $ show err
    Right Nothing -> return ()
    Right (Just result) -> put result

relate :: (GaloisField n, Integral n) => RefF -> (n, RefF, n) -> M n ()
relate var (slope, val, intercept) = do
  xs <- get
  case runExcept (Relations.relateRef (F var) slope (F val) intercept xs) of
    Left err -> error $ show err
    Right Nothing -> return ()
    Right (Just result) -> put result

-- | Assert that `var1 = slope * var2 + intercept`
assertRelation :: (GaloisField n, Integral n) => RefF -> n -> RefF -> n -> M n ()
assertRelation var1 slope var2 intercept = do
  xs <- get
  lift $ Relations.relationBetween (F var1) (F var2) xs `shouldBe` Just (slope, intercept)
