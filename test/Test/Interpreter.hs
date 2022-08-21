{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}

module Test.Interpreter (tests) where

import Control.Arrow (left)
-- import Test.QuickCheck.GenT
import Control.Monad.Reader
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import qualified Keelung.Compiler.Interpret.Kinded as Kinded
import qualified Keelung.Compiler.Interpret.Typed as Typed
import Keelung.Field (GF181)
import qualified Keelung.Monad as Kinded
import qualified Keelung.Syntax.Kinded as Kinded
import qualified Keelung.Syntax.Simplify as Kinded
import qualified Keelung.Types as Kinded
import Test.Hspec
import Test.QuickCheck (chooseInt)
import Test.QuickCheck.Arbitrary
import Test.QuickCheck.GenT
import Test.QuickCheck.Property

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

data Ctx = Ctx
  { ctxNumVar :: Int,
    ctxNumInputVar :: Int,
    ctxBoolVars :: IntSet
  }
  deriving (Show)

data Program t n = Program (Kinded.Elaborated t n) [n]
  deriving (Eq, Show)

type M = Reader Ctx

--------------------------------------------------------------------------------

instance Arbitrary Ctx where
  arbitrary = do
    let range = (0, 10)
    numVar <- chooseInt range
    numInputVar <- chooseInt range `suchThat` (<= numVar)
    numBoolVar <- chooseInt range `suchThat` (<= numVar)
    boolVars <- IntSet.fromList <$> replicateM numInputVar arbitrary
    return $ Ctx numVar numBoolVar boolVars

--------------------------------------------------------------------------------

instance Arbitrary n => Arbitrary (Program 'Kinded.Num n) where
  arbitrary = do
    a <- runGenT arbitraryM
    runReader a <$> liftGen arbitrary

--------------------------------------------------------------------------------

class ArbitraryM a where
  arbitraryM :: GenT M a

instance ArbitraryM a => Arbitrary (M a) where
  arbitrary = runGenT arbitraryM

instance Arbitrary n => ArbitraryM (Program 'Kinded.Num n) where
  arbitraryM = Program <$> arbitraryM <*> return []

instance Arbitrary n => ArbitraryM (Kinded.Computation n) where
  arbitraryM = return $ Kinded.Computation 0 0 mempty mempty mempty mempty mempty

instance Arbitrary n => ArbitraryM (Kinded.Elaborated 'Kinded.Num n) where
  arbitraryM = Kinded.Elaborated <$> arbitraryM <*> arbitraryM

instance Arbitrary n => ArbitraryM (Kinded.Val 'Kinded.Num n) where
  arbitraryM = do
    oneof
      [ Kinded.Number <$> liftGen arbitrary,
        Kinded.Ref <$> arbitraryM
      ]

instance ArbitraryM (Kinded.Ref 'Kinded.Num) where
  arbitraryM = do
    n <- lift $ asks ctxNumVar
    boolVars <- lift $ asks ctxBoolVars
    Kinded.NumVar <$> liftGen (chooseInt (0, n - 1)) `suchThat` (\x -> not (IntSet.member x boolVars))

-- instance Arbitrary n => Arbitrary (Kinded.Computation n) where
--   arbitrary = return $ Kinded.Computation 0 0 mempty mempty mempty mempty mempty

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