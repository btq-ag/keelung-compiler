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
      let xs = foldl applyRelate UnionFind.new (relates :: [Relate])
      UnionFind.validate xs `shouldBe` []

  it "relate and then assign once" $ do
    property $ \(relates, assign) -> do
      let xs = foldl applyRelate UnionFind.new (relates :: [Relate])
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

-- --------------------------------------------------------------------------------

-- -- | Create a model so that we won't generate conflicting operations for testing.
-- data Model = Model (IntMap UnionFind.VarStatus) Int

-- instance Arbitrary Model where
--   arbitrary = do
--     entries <- arbitrary :: Gen [Entry]
--     (model, size) <- foldM step (mempty, 0) entries
--     pure $ Model model size
--     where
--       step :: (IntMap UnionFind.VarStatus, Var) -> Entry -> Gen (IntMap UnionFind.VarStatus, Var)
--       step (xs, var) Constant = do
--         value <- arbitrary
--         pure (IntMap.insert var (UnionFind.IsConstant value) xs, var + 1)
--       step (xs, var) EquivClass = do
--         sameSignSize <- arbitrary
--         let sameSign = IntSet.fromList [var + 1 .. var + 1 + sameSignSize]
--         oppositeSignSize <- arbitrary
--         let oppositeSign = IntSet.fromList [var + 1 + sameSignSize .. var + 1 + sameSignSize + oppositeSignSize]
--         let insertedRoot = IntMap.insert var (UnionFind.IsRoot sameSign oppositeSign) xs
--         let insertedChildren =
--               insertedRoot
--                 <> IntMap.fromSet (const (UnionFind.IsChildOf var True)) sameSign
--                 <> IntMap.fromSet (const (UnionFind.IsChildOf var False)) oppositeSign
--         pure (insertedChildren, var + 1 + sameSignSize + oppositeSignSize)

-- data Entry = Constant | EquivClass

-- instance Arbitrary Entry where
--   arbitrary = elements [Constant, EquivClass]
