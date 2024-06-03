{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}

module Test.Data.UnionFind.Field (run, tests) where

import Control.Monad (forM_)
import Data.Field.Galois (Binary, GaloisField, Prime)
import Data.IntMap qualified as IntMap
import Data.Maybe qualified as Maybe
import Keelung (GF181, N (N), Var)
import Keelung.Data.UnionFind.Field (UnionFind)
import Keelung.Data.UnionFind.Field qualified as UnionFind
import Test.HUnit
import Test.Hspec
import Test.QuickCheck

run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = describe "Field UnionFind" $ do
  -- it "test" $ do
  --   --
  --   -- $300 = 2 * $200 + 8  <=> 9 * $300 + 13 = $200
  --   --                          3 * $300 + 4 = $100
  --   -- $200 = 3 * $100 + 1  <=> 6 * $200 + 11 = $100
  --   --
  --   let relates = [Relate 200 2 300 8, Relate 100 3 200 1]
  --   let xs = foldl applyRelate UnionFind.new (relates :: [Relate (Prime 17)])
  --   UnionFind.validate xs `shouldBe` []

  describe "operations" $ do
    it "relate" $ do
      property $ \relates -> do
        let xs = foldl applyRelate UnionFind.new (relates :: [Relate (Prime 17)])
        UnionFind.validate xs `shouldBe` []

    it "relate and then assign" $ do
      property $ \(relates, assignments) -> do
        let xs = foldl applyRelate UnionFind.new (relates :: [Relate (Prime 17)])
        let xs' =
              foldr
                ( \(Assign target val) acc -> case UnionFind.lookup target acc of
                    UnionFind.Constant _ -> acc
                    _ -> applyAssign acc (Assign target val)
                )
                xs
                (assignments :: [Assign (Prime 17)])

        UnionFind.validate xs' `shouldBe` []

  describe "symmetricity" $ do
    it "relate and then assign" $ do
      property $ \xs -> do
        let (_assignments, families) = UnionFind.export (xs :: UnionFind GF181)
        forM_ (IntMap.toList families) $ \(root, family) -> do
          UnionFind.lookup root xs `shouldBe` UnionFind.Root
          forM_ (IntMap.toList family) $ \(child, (slope, intercept)) -> do
            UnionFind.lookup child xs `shouldBe` UnionFind.ChildOf slope root intercept

  describe "LinRel" $ do
    describe "invertLinRel . invertLinRel = id" $ do
      it "GF181" $ do
        property $ \rel -> do
          (UnionFind.invertLinRel . UnionFind.invertLinRel) rel `shouldBe` (rel :: UnionFind.LinRel GF181)
      it "Prime 17" $ do
        property $ \rel -> do
          (UnionFind.invertLinRel . UnionFind.invertLinRel) rel `shouldBe` (rel :: UnionFind.LinRel (Prime 17))
      it "Binary 7" $ do
        property $ \rel -> do
          (UnionFind.invertLinRel . UnionFind.invertLinRel) rel `shouldBe` (rel :: UnionFind.LinRel (Binary 7))

    describe "execLinRel invertLinRel rel . execLinRel rel = id" $ do
      it "GF181" $ do
        property $ \(rel, points) -> do
          map (UnionFind.execLinRel (UnionFind.invertLinRel rel) . UnionFind.execLinRel rel) points `shouldBe` (points :: [GF181])
      it "Prime 17" $ do
        property $ \(rel, points) -> do
          map (UnionFind.execLinRel (UnionFind.invertLinRel rel) . UnionFind.execLinRel rel) points `shouldBe` (points :: [Prime 17])
      it "Binary 7" $ do
        property $ \(rel, points) -> do
          map (UnionFind.execLinRel (UnionFind.invertLinRel rel) . UnionFind.execLinRel rel) points `shouldBe` (points :: [Binary 7])

------------------------------------------------------------

data Relate n = Relate Var n Var n -- var1 = slope * var2 + intercept

instance (GaloisField n, Integral n) => Show (Relate n) where
  show (Relate var1 slope var2 intercept) = "$" <> show var1 <> " = " <> show (N slope) <> " * $" <> show var2 <> " + " <> show (N intercept)

instance (Arbitrary n, Eq n, Num n) => Arbitrary (Relate n) where
  arbitrary =
    Relate
      <$> chooseInt (0, 100) -- var1
      <*> (arbitrary `suchThat` (/= 0))
      <*> chooseInt (0, 100) -- var2
      <*> arbitrary

data Assign n = Assign Var n
  deriving (Show)

instance (GaloisField n, Integral n) => Arbitrary (Assign n) where
  arbitrary = Assign <$> chooseInt (0, 100) <*> arbitrary

instance (GaloisField n, Integral n) => Arbitrary (UnionFind.LinRel n) where
  arbitrary = UnionFind.LinRel <$> (arbitrary `suchThat` (/= 0)) <*> arbitrary

------------------------------------------------------------

instance (GaloisField n, Integral n) => Arbitrary (UnionFind n) where
  arbitrary = do
    relates <- arbitrary :: Gen [Relate n]
    assignments <- arbitrary :: Gen [Assign n]
    let xs = foldl applyRelate UnionFind.new relates
    return $
      foldr
        ( \(Assign target val) acc -> case UnionFind.lookup target acc of
            UnionFind.Constant _ -> acc
            _ -> applyAssign acc (Assign target val)
        )
        xs
        assignments

------------------------------------------------------------

applyRelate :: (GaloisField n, Integral n) => UnionFind n -> Relate n -> UnionFind n
applyRelate xs (Relate var1 slope var2 intercept) = Maybe.fromMaybe xs (UnionFind.relate var1 slope var2 intercept xs)

applyAssign :: (GaloisField n, Integral n) => UnionFind n -> Assign n -> UnionFind n
applyAssign xs (Assign var value) = Maybe.fromMaybe xs (UnionFind.assign var value xs)