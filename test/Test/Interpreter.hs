{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}

module Test.Interpreter (tests) where

import qualified Basic
import Control.Arrow (left)
import Data.Field.Galois (GaloisField)
import Keelung (Comp, Computation (compVarCounters), Elaborable, Elaborated (elabComp), GF181, elaborate, elaborate')
import Keelung.Compiler (Error (..))
import qualified Keelung.Compiler.Interpret.Kinded as Kinded
import qualified Keelung.Compiler.Interpret.Typed as Typed
import qualified Keelung.Compiler.Syntax.Inputs as Inputs
import Test.Hspec
import Test.QuickCheck

kinded :: (GaloisField n, Integral n, Elaborable t, Kinded.FreeVar t, Kinded.Interpret t n) => Comp t -> [n] -> Either String [n]
kinded prog rawInputs = do
  elab <- left show (elaborate' prog)
  let inputs = Inputs.deserialize (compVarCounters (elabComp elab)) rawInputs
  left show (Kinded.runAndCheck elab inputs)

typed :: (GaloisField n, Integral n, Elaborable t) => Comp t -> [n] -> Either (Error n) [n]
typed prog rawInputs = do
  elab <- left ElabError (elaborate prog)
  let inputs = Inputs.deserializeElab elab rawInputs
  left InterpretError (Typed.runAndCheck elab inputs)

tests :: SpecWith ()
tests = do
  describe "Interpreters of different syntaxes should computes the same result" $ do
    it "Basic.identity" $
      property $ \input -> do
        kinded Basic.identity [input :: GF181]
          `shouldBe` Right [input]
        typed Basic.identity [input :: GF181]
          `shouldBe` Right [input]

    it "Basic.add3" $
      property $ \input -> do
        kinded Basic.add3 [input :: GF181]
          `shouldBe` Right [input + 3]
        typed Basic.add3 [input :: GF181]
          `shouldBe` Right [input + 3]

    it "Basic.eq1" $
      property $ \input -> do
        let expectedOutput = if input == 3 then [1] else [0]
        kinded Basic.eq1 [input :: GF181]
          `shouldBe` Right expectedOutput
        typed Basic.eq1 [input :: GF181]
          `shouldBe` Right expectedOutput

    it "Basic.cond'" $
      property $ \input -> do
        let expectedOutput = if input == 3 then [12] else [789]
        kinded Basic.cond' [input :: GF181]
          `shouldBe` Right expectedOutput
        typed Basic.cond' [input :: GF181]
          `shouldBe` Right expectedOutput

    it "Basic.summation" $
      forAll (vector 4) $ \input -> do
        let expectedOutput = [sum input]
        kinded Basic.summation (input :: [GF181])
          `shouldBe` Right expectedOutput
        typed Basic.summation input
          `shouldBe` Right expectedOutput

    it "Basic.summation2" $
      forAll (vector 4) $ \input -> do
        let expectedOutput = []
        kinded Basic.summation2 (input :: [GF181])
          `shouldBe` Right expectedOutput
        typed Basic.summation2 input
          `shouldBe` Right expectedOutput

-- tests :: SpecWith ()
-- tests = do
--   return ()
--   -- describe "Interpreters of different syntaxes" $ do
--   --   it " should computes the same result" $
--   --     property $ \program ->
--   --       let Program elab inputs = program :: Program 'Kinded.Num GF181
--   --        in left show (Typed.run (Kinded.simplify elab) inputs)
--   --             `shouldBe` left show (Kinded.run elab inputs)

-- data Ctx = Ctx
--   { ctxNumVar :: Int,
--     ctxNumInputVar :: Int,
--     ctxBoolVars :: IntSet
--   }
--   deriving (Show)

-- data Program t n = Program (Kinded.Elaborated t) [n]
--   deriving (Eq, Show)

-- type M = Reader Ctx

-- --------------------------------------------------------------------------------

-- instance Arbitrary Ctx where
--   arbitrary = do
--     let range = (0, 10)
--     numVar <- chooseInt range
--     numInputVar <- chooseInt range `suchThat` (<= numVar)
--     numBoolVar <- chooseInt range `suchThat` (<= numVar)
--     boolVars <- IntSet.fromList <$> replicateM numInputVar arbitrary
--     return $ Ctx numVar numBoolVar boolVars

-- --------------------------------------------------------------------------------

-- instance Arbitrary n => Arbitrary (Program 'Kinded.Num n) where
--   arbitrary = do
--     a <- runGenT arbitraryM
--     runReader a <$> liftGen arbitrary

-- --------------------------------------------------------------------------------

-- class ArbitraryM a where
--   arbitraryM :: GenT M a

-- instance ArbitraryM a => Arbitrary (M a) where
--   arbitrary = runGenT arbitraryM

-- instance Arbitrary n => ArbitraryM (Program 'Kinded.Num n) where
--   arbitraryM = Program <$> arbitraryM <*> return []

-- instance ArbitraryM Kinded.Computation where
--   arbitraryM = return $ Kinded.Computation 0 0 mempty mempty mempty mempty mempty

-- instance ArbitraryM (Kinded.Elaborated 'Kinded.Num) where
--   arbitraryM = Kinded.Elaborated <$> arbitraryM <*> arbitraryM

-- instance ArbitraryM (Kinded.Val 'Kinded.Num) where
--   arbitraryM = do
--     oneof
--       [ Kinded.Integer <$> liftGen arbitrary,
--         Kinded.Ref <$> arbitraryM
--       ]

-- instance ArbitraryM (Kinded.Ref 'Kinded.Num) where
--   arbitraryM = do
--     n <- lift $ asks ctxNumVar
--     boolVars <- lift $ asks ctxBoolVars
--     Kinded.NumVar <$> liftGen (chooseInt (0, n - 1)) `suchThat` (\x -> not (IntSet.member x boolVars))

-- -- instance Arbitrary n => Arbitrary (Kinded.Computation n) where
-- --   arbitrary = return $ Kinded.Computation 0 0 mempty mempty mempty mempty mempty

-- -- -- | Data structure for elaboration bookkeeping
-- -- data Computation n = Computation
-- --   { -- Counter for generating fresh variables
-- --     compNextVar :: Int,
-- --     -- Counter for allocating fresh heap addresses
-- --     compNextAddr :: Int,
-- --     -- Variables marked as inputs
-- --     compInputVars :: IntSet,
-- --     -- Heap for arrays
-- --     compHeap :: Heap,
-- --     -- Assignments
-- --     compNumAsgns :: [Assignment 'Num n],
-- --     compBoolAsgns :: [Assignment 'Bool n],
-- --     -- Assertions are expressions that are expected to be true
-- --     compAssertions :: [Boolean]
-- --   }
-- --   deriving (Eq)

-- --------------------------------------------------------------------------------