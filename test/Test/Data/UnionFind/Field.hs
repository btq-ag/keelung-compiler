{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}

module Test.Data.UnionFind.Field (run, tests) where

import Data.Field.Galois (GaloisField, Prime)
import Data.Maybe qualified as Maybe
import Keelung (GF181, N (N), Var)
import Keelung.Data.UnionFind.Field (UnionFind)
import Keelung.Data.UnionFind.Field qualified as UnionFind
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

  it "relate" $ do
    property $ \relates -> do
      let xs = foldl applyRelate UnionFind.new (relates :: [Relate (Prime 17)])
      UnionFind.validate xs `shouldBe` []

  it "relate and then assign once" $ do
    property $ \(relates, assign) -> do
      let xs = foldl applyRelate UnionFind.new (relates :: [Relate (Prime 17)])
      let xs' = applyAssign xs assign
      UnionFind.validate xs' `shouldBe` []

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

applyRelate :: (GaloisField n, Integral n) => UnionFind n -> Relate n -> UnionFind n
applyRelate xs (Relate var1 slope var2 intercept) = Maybe.fromMaybe xs (UnionFind.relate var1 slope var2 intercept xs)

applyAssign :: (GaloisField n, Integral n) => UnionFind n -> Assign n -> UnionFind n
applyAssign xs (Assign var value) = Maybe.fromMaybe xs (UnionFind.assign var value xs)