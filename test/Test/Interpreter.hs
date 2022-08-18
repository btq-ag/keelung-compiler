{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}

module Test.Interpreter (tests) where

import Control.Arrow (left)
import qualified Keelung.Compiler.Interpret.Kinded as Kinded
import qualified Keelung.Compiler.Interpret.Typed as Typed
import Keelung.Field (GF181)
import qualified Keelung.Monad as Kinded
import qualified Keelung.Syntax.Kinded as Kinded
import qualified Keelung.Syntax.Simplify as Kinded
import qualified Keelung.Types as Kinded
import Test.Hspec
import Test.QuickCheck

-- import qualified Keelung.Syntax.Typed as Typed
-- import Keelung.Syntax.Kinded

tests :: SpecWith ()
tests = do
  describe "Interpreters of different syntaxes" $ do
    it " should computes the same result" $
      property $ \program ->
        let Program elab inputs = program :: Program 'Kinded.Num GF181
         in left show (Typed.run (Kinded.simplify elab) inputs)
              `shouldBe` left show (Kinded.run elab inputs)

--------------------------------------------------------------------------------

data Program t n = Program (Kinded.Elaborated t n) [n]
  deriving (Eq, Show)

instance Arbitrary n => Arbitrary (Program 'Kinded.Num n) where
  arbitrary = do
    Program <$> arbitrary <*> return []

instance Arbitrary n => Arbitrary (Kinded.Elaborated 'Kinded.Num n) where
  arbitrary = do
    Kinded.Elaborated <$> arbitrary <*> arbitrary

instance Arbitrary n => Arbitrary (Kinded.Val 'Kinded.Num n) where
  arbitrary = Kinded.Number <$> arbitrary

instance Arbitrary n => Arbitrary (Kinded.Computation n) where
  arbitrary = return $ Kinded.Computation 0 0 mempty mempty mempty mempty mempty

-- Kinded.Computation 0 0
-- <$> return mempty
-- <*> return mempty
-- <*> return mempty
-- <*> return mempty
-- <*> return mempty

-- -- | Data structure for elaboration bookkeeping
-- data Computation n = Computation
--   { -- Counter for generating fresh variables
--     compNextVar :: Int,
--     -- Counter for allocating fresh heap addresses
--     compNextAddr :: Int,
--     -- Variables marked as inputs
--     compInputVars :: IntSet,
--     -- Heap for arrays
--     compHeap :: Heap,
--     -- Assignments
--     compNumAsgns :: [Assignment 'Num n],
--     compBoolAsgns :: [Assignment 'Bool n],
--     -- Assertions are expressions that are expected to be true
--     compAssertions :: [Val 'Bool n]
--   }
--   deriving (Eq)

--------------------------------------------------------------------------------