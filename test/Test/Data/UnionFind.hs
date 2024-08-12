{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
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
  -- it "error 1" $ do
  --   let relates =
  --         [ RelateCompilerRefField (F (RefFX 0)) (B (RefBP 0)) (1, 2),
  --           RelateCompilerRefField (F (RefFX 0)) (B (RefBI 5)) (3, 4)
  --         ]
  --   let xs = foldl applyRelate (Relations.new (Options.new Field.gf181)) (relates :: [Relate (Relations.Relations GF181) Ref GF181]) :: Relations.Relations GF181
  --   print xs
  --   Relations.validate xs `shouldBe` []

  -- it "error 2" $ do
  --     let relates =
  --           [ RelateEC  (B (RefBX 0)) (F (RefFX 0)) (1, 2),
  --             RelateEC  (B (RefBX 0))(F(RefFO 5)) (1/3, 4)
  --           ]
  --     let xs = foldl applyRelate (EC.new "Ref / GF181") (relates :: [Relate (EC.EquivClass Ref GF181 (Field.LinRel GF181)) Ref GF181]) ::  EC.EquivClass Ref GF181 (Field.LinRel GF181)
  --     print xs
  --     EC.validate xs `shouldBe` []

  -- it "error 3" $ do
  --   let relates =
  --         [ RelateCompilerRefField (B (RefBX 0)) (F (RefFX 0)) (1, 2),
  --           RelateCompilerRefField (B (RefBX 0))(F(RefFO 5)) (1/3, 4)
  --         ]
  --   let xs = foldl applyRelate (Relations.new (Options.new Field.gf181)) (relates :: [Relate (Relations.Relations GF181) Ref GF181]) :: Relations.Relations GF181
  --   print xs
  --   Relations.validate xs `shouldBe` []

  -- B = F + 2
  -- F = B - 2
  -- B = X/3 + 4
  -- 3F + 6 = X + 12
  -- X = 3F - 6
  --   = 3B - 12

  describe "operations" $ do
    describe "relate" $ do
      it "SolverVarBool" $ do
        property $ \relates -> do
          let xs = applyRelates new relates :: SolverVarBool
          Boolean.validate xs `shouldBe` []
      it "SolverVarField GF181" $ do
        property $ \relates -> do
          let xs = applyRelates new relates :: SolverVarField GF181
          Field.validate xs `shouldBe` []
      it "SolverVarField (Prime 17)" $ do
        property $ \relates -> do
          let xs = applyRelates new relates :: SolverVarField (Prime 17)
          Field.validate xs `shouldBe` []
      it "SolverVarField (Binary 7)" $ do
        property $ \relates -> do
          let xs = applyRelates new relates :: SolverVarField (Binary 7)
          Field.validate xs `shouldBe` []
      it "CompilerRef GF181" $ do
        property $ \relates -> do
          let xs = applyRelates new relates :: CompilerRefField GF181
          Relations.validate xs `shouldBe` []
      it "CompilerRef (Prime 17)" $ do
        property $ \relates -> do
          let xs = applyRelates new relates :: CompilerRefField (Prime 17)
          Relations.validate xs `shouldBe` []
      it "CompilerRef (Binary 7)" $ do
        property $ \relates -> do
          let xs = applyRelates new relates :: CompilerRefField (Binary 7)
          Relations.validate xs `shouldBe` []
    -- it "EC / Ref / GF181" $ do
    --   property $ \relates -> do
    --     let xs = foldl applyRelate (EC.new "Ref / GF181") (relates :: [Relate (EC.EquivClass Ref GF181 (Field.LinRel GF181)) Ref GF181]) :: EC.EquivClass Ref GF181 (Field.LinRel GF181)
    --     EC.validate xs `shouldBe` []
    -- it "Relations / Ref / Prime 17" $ do
    --   property $ \relates -> do
    --     let xs = foldl applyRelate (Relations.new (Options.new (Field.Prime 17))) (relates :: [Relate (Relations.Relations (Prime 17)) Ref (Prime 17)]) :: Relations.Relations (Prime 17)
    --     Relations.validate xs `shouldBe` []
    -- it "Relations / Ref / Binary 7" $ do
    --   property $ \relates -> do
    --     let xs = foldl applyRelate (Relations.new (Options.new (Field.Binary 7))) (relates :: [Relate (Relations.Relations (Binary 7)) Ref (Binary 7)]) :: Relations.Relations (Binary 7)
    --     Relations.validate xs `shouldBe` []

    describe "relate 2 variables and then lookup the relation" $ do
      it "CompilerRefField GF181" $ do
        property $ \rel1 -> do
          let relates = [rel1]
          let xs = applyRelates new relates :: CompilerRefField GF181
          Relations.validate xs `shouldBe` []

          let (var1, var2, rel1') = elimRelate rel1
          if var1 == var2
            then Relations.relationBetween var1 var2 xs `shouldBe` Just (1, 0)
            else Relations.relationBetween var1 var2 xs `shouldBe` Just rel1'

    -- it "relate 3 variables and then lookup the relation" $ do
    --   property $ \(var1, var2, var3, rel1, rel2) -> do
    --     let relates =
    --           [ RelateCompilerRefField var1 var2 rel1,
    --             RelateCompilerRefField var2 var3 rel2
    --           ]
    --     let xs = foldl applyRelate (Relations.new (Options.new Field.gf181)) (relates :: [Relate (Relations.Relations GF181) Ref (GF181, GF181)]) :: Relations.Relations GF181
    --     Relations.validate xs `shouldBe` []

    --     if var1 == var2
    --       then Relations.relationBetween var1 var2 xs `shouldBe` Just (1, 0)
    --       else Relations.relationBetween var1 var2 xs `shouldBe` Just rel1

    describe "relate and then assign" $ do
      it "Boolean" $ do
        property $ \(relates, assignments) -> do
          let xs = foldl applyRelate Boolean.new (relates :: [Relate SolverVarBool Var Bool])
          let xs' = foldl applyAssign xs (assignments :: [Assign SolverVarBool Var Bool])
          Boolean.validate xs' `shouldBe` []
      it "Field / GF181" $ do
        property $ \(relates, assignments) -> do
          let xs = foldl applyRelate Field.new (relates :: [Relate (SolverVarField GF181) Var (GF181, GF181)])
          let xs' = foldl applyAssign xs (assignments :: [Assign (SolverVarField GF181) Var GF181])
          Field.validate xs' `shouldBe` []
      it "Field / Prime 17" $ do
        property $ \(relates, assignments) -> do
          let xs = foldl applyRelate Field.new (relates :: [Relate (Field.UnionFind (Prime 17)) Var (Prime 17, Prime 17)])
          let xs' = foldl applyAssign xs (assignments :: [Assign (Field.UnionFind (Prime 17)) Var (Prime 17)])
          Field.validate xs' `shouldBe` []
      it "Field / Binary 7" $ do
        property $ \(relates, assignments) -> do
          let xs = foldl applyRelate Field.new (relates :: [Relate (Field.UnionFind (Binary 7)) Var (Binary 7, Binary 7)])
          let xs' = foldl applyAssign xs (assignments :: [Assign (Field.UnionFind (Binary 7)) Var (Binary 7)])
          Field.validate xs' `shouldBe` []

  describe "symmetricity" $ do
    it "relate and then assign" $ do
      property $ \xs -> do
        let (_assignments, families) = Field.export (xs :: SolverVarField GF181)
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
                ( [ RelateSolverVarField 0 1 (1, 0),
                    -- \$0 = $1
                    RelateSolverVarField 0 2 (1, -1),
                    -- \$0 = $2 - 1
                    RelateSolverVarField 0 3 (1, 1),
                    -- \$0 = $3 + 1
                    RelateSolverVarField 0 4 (2, 3)
                  ] ::
                    -- \$0 = 2$4 + 3

                    [Relate (SolverVarField GF181) Var (GF181, GF181)]
                )
        let xs' =
              foldl
                applyDesignateRange
                xs
                ( [ DesignateRangeVarField 0 (UnionFind.Range (Just (Field.Wrapper 0, Field.Wrapper 2)))
                  ] ::
                    [DesignateRange (SolverVarField GF181) Var GF181]
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
                ( [ RelateSolverVarField 4 51 (1, 0),
                    RelateSolverVarField 5 52 (1, 1),
                    RelateSolverVarField 4 5 (2, 1)
                  ] ::
                    [Relate (Field.UnionFind (Binary 7)) Var (Binary 7, Binary 7)]
                )
        Field.validate xs `shouldBe` []
        Field.lookup 52 xs `shouldBe` Field.ChildOf 4 (Field.LinRel 3 2) mempty

      it "Prime 7" $ do
        let xs =
              foldl
                applyRelate
                Field.new
                ( [ RelateSolverVarField 4 51 (1, 0),
                    RelateSolverVarField 5 52 (1, 1),
                    RelateSolverVarField 4 5 (2, 1)
                  ] ::
                    [Relate (Field.UnionFind (Prime 7)) Var (Prime 7, Prime 7)]
                )
        Field.validate xs `shouldBe` []
        Field.lookup 52 xs `shouldBe` Field.ChildOf 4 (Field.LinRel 4 2) mempty

    describe "Ref / Field / GF181" $ do
      it "$0 = 0" $
        runM defaultOptions $ do
          F (RefFX 0) `assignM` 0 :: M GF181 ()

      it "$0 = $1" $
        runM defaultOptions $ do
          RefFX 0 `relateM` (1, RefFX 1, 0) :: M GF181 ()
          assertRelation (RefFX 0) 1 (RefFX 1) 0
          assertRelation (RefFX 1) 1 (RefFX 0) 0

      it "$0 = 2$1" $
        runM defaultOptions $ do
          RefFX 0 `relateM` (2, RefFX 1, 0) :: M GF181 () -- x = 2y
          assertRelation (RefFX 0) 2 (RefFX 1) 0
          assertRelation (RefFX 0) 1 (RefFX 0) 0
          assertRelation (RefFX 1) (1 / 2) (RefFX 0) 0
          assertRelation (RefFX 1) 1 (RefFX 1) 0

      it "$0 = 2$1 + 1" $
        runM defaultOptions $ do
          RefFX 0 `relateM` (2, RefFX 1, 1) :: M GF181 () -- x = 2y + 1
          assertRelation (RefFX 0) 2 (RefFX 1) 1
          assertRelation (RefFX 1) (1 / 2) (RefFX 0) (-1 / 2) -- y = 1/2x - 1/2
      it "$0 = 2$1 + 1 & $1 = 3$2 + 2" $
        runM defaultOptions $ do
          RefFX 0 `relateM` (2, RefFX 1, 1) :: M GF181 () -- x = 2y + 1
          RefFX 1 `relateM` (3, RefFX 2, 2) -- y = 3z + 2

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

-- | UnionFind for the solver with Var as variables, Bool as values, and Boolean.Rel as relations
type SolverVarBool = Boolean.UnionFind Bool Boolean.Rel

-- | UnionFind for the solver with Var as variables, Field as values, and Field.LinRel as relations
type SolverVarField field = Field.UnionFind field

-- | UnionFind for the compiler with Ref as variables, Field as values, and (n, n) as relations
type CompilerRefField field = Relations.Relations field

-- | Unified UnionFind with Field.LinRel as relations
type Unified var field rel = EC.EquivClass var field rel

-- | Typeclass for UnionFind data structures
class RelateC a var rel | a -> var, a -> rel where
  relate :: a -> Relate a var rel -> a
  new :: a

instance (GaloisField n, Integral n) => RelateC (SolverVarField n) Var (n, n) where
  relate = applyRelate
  new = Field.new

instance RelateC SolverVarBool Var Bool where
  relate = applyRelate
  new = Boolean.new

instance (GaloisField n, Integral n) => RelateC (CompilerRefField n) Ref (n, n) where
  relate = applyRelate
  new = Relations.new (Options.new Field.gf181)

instance (GaloisField n, Integral n, Seniority var, Ord var) => RelateC (Unified var n (Field.LinRel n)) var (n, n) where
  relate = applyRelate
  new = EC.new "Ref / GF181"

-- | Datatype for relating two variables
data Relate :: Type -> Type -> Type -> Type where
  RelateSolverVarField :: (GaloisField n, Integral n) => Var -> Var -> (n, n) -> Relate (SolverVarField n) Var (n, n)
  RelateSolverVarBool :: Var -> Var -> Bool -> Relate SolverVarBool Var Bool
  RelateCompilerRefField :: (GaloisField n, Integral n) => Ref -> Ref -> (n, n) -> Relate (CompilerRefField n) Ref (n, n)
  RelateEC :: (GaloisField n, Integral n, Seniority var, Ord var) => var -> var -> (n, n) -> Relate (Unified var n (Field.LinRel n)) var (n, n)

elimRelate :: Relate a var rel -> (var, var, rel)
elimRelate (RelateSolverVarField var1 var2 rel) = (var1, var2, rel)
elimRelate (RelateSolverVarBool var1 var2 rel) = (var1, var2, rel)
elimRelate (RelateCompilerRefField var1 var2 rel) = (var1, var2, rel)
elimRelate (RelateEC var1 var2 rel) = (var1, var2, rel)

applyRelates :: (RelateC a var rel) => a -> [Relate a var rel] -> a
applyRelates = foldl relate

instance (GaloisField n, Integral n, Show var) => Show (Relate (SolverVarField n) var (n, n)) where
  show (RelateSolverVarField var1 var2 (slope, intercept)) = "RelateField " <> show var1 <> " " <> show var2 <> " (" <> show slope <> ", " <> show intercept <> ")"

instance (Show var) => Show (Relate SolverVarBool var Bool) where
  show (RelateSolverVarBool var1 var2 relation) = "RelateSolverVarBool " <> show var1 <> " " <> show var2 <> " " <> show relation

instance (GaloisField n, Integral n, Show var) => Show (Relate (CompilerRefField n) var (n, n)) where
  show (RelateCompilerRefField var1 var2 (slope, intercept)) = "RelateCompilerRefField " <> show var1 <> " " <> show var2 <> " (" <> show slope <> ", " <> show intercept <> ")"

instance (GaloisField n, Integral n, Show var) => Show (Relate (EC.EquivClass Ref n (Field.LinRel n)) var (n, n)) where
  show (RelateEC var1 var2 (slope, intercept)) = "RelateEC " <> show var1 <> " " <> show var2 <> " (" <> show slope <> ", " <> show intercept <> ")"

instance (Arbitrary n, GaloisField n, Integral n) => Arbitrary (Relate (SolverVarField n) Var (n, n)) where
  arbitrary =
    RelateSolverVarField
      <$> chooseInt (0, 100)
      <*> chooseInt (0, 100)
      <*> ((,) <$> (arbitrary `suchThat` (/= 0)) <*> arbitrary)

instance (Arbitrary n, GaloisField n, Integral n) => Arbitrary (Relate (CompilerRefField n) Ref (n, n)) where
  arbitrary =
    RelateCompilerRefField
      <$> arbitrary
      <*> arbitrary
      <*> ((,) <$> (arbitrary `suchThat` (/= 0)) <*> arbitrary)

instance Arbitrary (Relate SolverVarBool Var Bool) where
  arbitrary =
    RelateSolverVarBool
      <$> chooseInt (0, 100)
      <*> chooseInt (0, 100)
      <*> arbitrary

instance (GaloisField n, Integral n, Arbitrary n, Arbitrary var, Seniority var, Ord var) => Arbitrary (Relate (EC.EquivClass var n (Field.LinRel n)) var (n, n)) where
  arbitrary =
    RelateEC
      <$> arbitrary
      <*> arbitrary
      <*> arbitrary

applyRelate :: a -> Relate a var val -> a
applyRelate xs (RelateSolverVarField var1 var2 (slope, intercept)) = Maybe.fromMaybe xs (Field.relate var1 var2 (Field.LinRel slope intercept) xs)
applyRelate xs (RelateSolverVarBool var1 var2 relation) = Maybe.fromMaybe xs (UnionFind.relate var1 var2 (Boolean.Rel relation) xs)
applyRelate xs (RelateCompilerRefField var1 var2 (slope, intercept)) = case runExcept (Relations.relateRef var1 slope var2 intercept xs) of
  Left err -> error (show err)
  Right (Just xs') -> xs'
  Right Nothing -> xs -- no-op
applyRelate xs (RelateEC var1 var2 (slope, intercept)) = case runExcept (EC.runM (EC.relate var1 (Field.LinRel slope intercept) var2 xs)) of
  Left err -> error (show err)
  Right (Just xs') -> xs'
  Right Nothing -> xs -- no-op

--------------------------------------------------------------------------------

data Assign :: Type -> Type -> Type -> Type where
  AssignVarField :: (GaloisField n, Integral n) => var -> n -> Assign (SolverVarField n) var n
  AssignVarBool :: var -> Bool -> Assign SolverVarBool var Bool
  AssignRelations :: (GaloisField n, Integral n) => Ref -> n -> Assign (CompilerRefField n) Ref n

instance (GaloisField n, Integral n, Show var) => Show (Assign (SolverVarField n) var n) where
  show (AssignVarField var val) = "AssignVarField " <> show var <> " " <> show val

instance Show (Assign SolverVarBool Var Bool) where
  show (AssignVarBool var val) = "AssignVarBool " <> show var <> " " <> show val

instance (GaloisField n, Integral n, Show var) => Show (Assign (CompilerRefField n) var n) where
  show (AssignRelations var val) = "Assign Relations " <> show var <> " " <> show val

instance {-# OVERLAPPING #-} (Arbitrary n, GaloisField n, Integral n) => Arbitrary (Assign (SolverVarField n) Var n) where
  arbitrary =
    AssignVarField
      <$> chooseInt (0, 100)
      <*> arbitrary

instance (Arbitrary n, GaloisField n, Integral n, Arbitrary var) => Arbitrary (Assign (SolverVarField n) var n) where
  arbitrary =
    AssignVarField
      <$> arbitrary
      <*> arbitrary

instance (Arbitrary n, GaloisField n, Integral n) => Arbitrary (Assign (CompilerRefField n) Ref n) where
  arbitrary =
    AssignRelations
      <$> arbitrary
      <*> arbitrary

instance Arbitrary (Assign SolverVarBool Var Bool) where
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
  DesignateRangeVarField :: (GaloisField n, Integral n) => Var -> UnionFind.Range (Field.Wrapper n) -> DesignateRange (SolverVarField n) Var n

-- DesignateRangeRefField :: (GaloisField n, Integral n) => Ref -> UnionFind.Range n -> DesignateRange (SolverVarField n) Var n
-- DesignateRangeRefField :: (GaloisField n, Integral n) => Ref -> Ref -> (n, n) -> Relate (CompilerRefField n) Ref n

applyDesignateRange :: a -> DesignateRange a var val -> a
applyDesignateRange xs (DesignateRangeVarField var range) = Maybe.fromMaybe xs (Field.designateRange var range xs)

--------------------------------------------------------------------------------

instance (GaloisField n, Integral n) => Arbitrary (SolverVarField n) where
  arbitrary = do
    relates <- arbitrary :: Gen [Relate (SolverVarField n) Var (n, n)]
    assignments <- arbitrary :: Gen [Assign (SolverVarField n) Var n]
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

type M n = StateT (CompilerRefField n) IO

runM :: Options -> M n a -> IO a
runM options p = evalStateT p (Relations.new options)

assignM :: (GaloisField n, Integral n) => Ref -> n -> M n ()
assignM var val = do
  xs <- get
  case runExcept (Relations.assignRef var val xs) of
    Left err -> error $ show err
    Right Nothing -> return ()
    Right (Just result) -> put result

relateM :: (GaloisField n, Integral n) => RefF -> (n, RefF, n) -> M n ()
relateM var (slope, val, intercept) = do
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
