{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module Test.Data.UnionFind.Field (run, tests) where

import Data.Field.Galois (GaloisField, Prime)
import Keelung (Var, GF181, N (N))
import Keelung.Data.UnionFind.Field (UnionFind)
import Keelung.Data.UnionFind.Field qualified as UnionFind
import Test.Hspec
import Test.QuickCheck
import qualified Data.Maybe as Maybe

run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = describe "Field UnionFind" $ do
  it "relate" $ do
    property $ \relates -> do
      let xs = foldl applyRelate UnionFind.new (relates :: [Relate (Prime 17)])
      UnionFind.validate xs `shouldBe` []

--   it "relate and then assign once" $ do
--     property $ \(relates, assign) -> do
--       let xs = foldl applyRelate UnionFind.new (relates :: [Relate])
--       let xs' = applyAssign xs assign
--       UnionFind.validate xs' `shouldBe` []

data Relate n = Relate Var n Var n -- var1 = slope * var2 + intercept

instance (GaloisField n, Integral n) => Show (Relate n) where 
    show (Relate var1 slope var2 intercept) = "$" <> show var1 <> " = " <> show (N slope) <> " * $" <> show var2 <> " + " <> show (N intercept)

instance (Arbitrary n) => Arbitrary (Relate n) where
  arbitrary =
    Relate
      <$> chooseInt (0, 100) -- var1
      <*> arbitrary
      <*> chooseInt (0, 100) -- var2
      <*> arbitrary

-- data Assign = Assign Var Bool
--   deriving (Show)

-- instance Arbitrary Assign where
--   arbitrary = Assign <$> chooseInt (0, 100) <*> arbitrary

applyRelate :: (GaloisField n, Integral n) => UnionFind n -> Relate n -> UnionFind n
applyRelate xs (Relate var1 slope var2 intercept) = Maybe.fromMaybe xs (UnionFind.relate var1 slope var2 intercept xs)

-- applyAssign :: UnionFind n -> Assign -> Maybe (UnionFind n)
-- applyAssign xs (Assign var value) = UnionFind.assign xs var value

-- data Operation
--   = Relate Var Var Bool
--   | Assign Var Bool
--   deriving (Show)

-- generateOperationFromModel :: Model -> Gen Operation
-- generateOperationFromModel (Model xs size) = do
--   var <- chooseInt (0, size - 1)
--   case IntMap.lookup var xs of
--     Nothing -> error "[ panic ] Solver Testing: not in model"
--     Just (UnionFind.IsConstant val) -> pure $ Assign var val
--     Just (UnionFind.IsRoot sameSign oppositeSign) -> do
--       let sameSignList = IntSet.toList sameSign
--       let oppositeSignList = IntSet.toList oppositeSign
--       if null sameSignList && null oppositeSignList
--         then error "[ panic ] Solver Testing: empty root"
--         else do
--           let (var1, var2) = if null sameSignList then (head oppositeSignList, var) else (head sameSignList, var)
--           sign <- arbitrary
--           pure $ Relate var1 var2 sign
--     Just (UnionFind.IsChildOf root sign) -> do
--       -- chooce from any of the same equivalence class
--       _

--   -- oneof [
--   --   Relate <$> arbitraryVar <*> arbitraryVar <*> arbitraryBool,
--   --   Assign <$> arbitraryVar <*> arbitraryBool
--   -- ]
--   where
--     arbitraryVar = elements (IntMap.keys xs)
--     arbitraryBool = arbitrary
