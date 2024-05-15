-- | TODO: add more tests
module Test.Data.UnionFind.Boolean (run, tests) where

import Keelung (Var)
import Keelung.Data.UnionFind.Boolean (UnionFind)
import Keelung.Data.UnionFind.Boolean qualified as UnionFind
import Test.Hspec
import Test.QuickCheck

run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = describe "Boolean UnionFind" $ do
  it "relate" $ do
    property $ \relates -> do
      let xs = foldl applyRelate UnionFind.empty (relates :: [Relate])
      UnionFind.validate xs `shouldBe` []

  it "relate and then assign once" $ do
    property $ \(relates, assign) -> do
      let xs = foldl applyRelate UnionFind.empty (relates :: [Relate])
      let xs' = applyAssign xs assign
      UnionFind.validate xs' `shouldBe` []

data Relate = Relate Var Var Bool
  deriving (Show)

instance Arbitrary Relate where
  arbitrary = Relate <$> chooseInt (0, 100) <*> chooseInt (0, 100) <*> arbitrary

data Assign = Assign Var Bool
  deriving (Show)

instance Arbitrary Assign where
  arbitrary = Assign <$> chooseInt (0, 100) <*> arbitrary

applyRelate :: UnionFind -> Relate -> UnionFind
applyRelate xs (Relate var1 var2 sign) = UnionFind.relate xs var1 var2 sign

applyAssign :: UnionFind -> Assign -> UnionFind
applyAssign xs (Assign var value) = UnionFind.assign xs var value