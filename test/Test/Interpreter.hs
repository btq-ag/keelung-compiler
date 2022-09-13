{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}

module Test.Interpreter (tests) where

import qualified Basic
import Keelung (GF181, Comp, Val (..), elaborate, elaborateOnly)
import Test.Hspec
import Control.Arrow (left)
import Test.QuickCheck
import qualified Keelung.Compiler.Interpret.Kinded as Kinded
import Data.Field.Galois (GaloisField)
import Keelung.Compiler (Error(..))
import qualified Keelung.Compiler.Interpret.Typed as Typed

kinded :: (GaloisField n, Integral n) => Comp (Val t) -> [n] -> Either String [n]
kinded prog ins = do
  elab <- left show (elaborateOnly prog) 
  left show (Kinded.runAndCheck elab ins)

typed :: (GaloisField n, Integral n) => Comp (Val t) -> [n] -> Either (Error n) [n]
typed prog ins = do
  elab <- left ElabError (elaborate prog)
  left InterpretError (Typed.run elab ins)

tests :: SpecWith ()
tests = do
  describe "Interpreters of different syntaxes should computes the same result" $ do
    it "Basic.identity" $
      property $ \input -> do 
        kinded Basic.identity [input :: GF181]
          `shouldBe` return [input]
        typed Basic.identity [input :: GF181]
          `shouldBe` return [input]

    it "Basic.add3" $
      property $ \input -> do 
        kinded Basic.add3 [input :: GF181]
          `shouldBe` return [input + 3]
        typed Basic.add3 [input :: GF181]
          `shouldBe` return [input + 3]
          
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
-- --     compAssertions :: [Val 'Bool]
-- --   }
-- --   deriving (Eq)

-- --------------------------------------------------------------------------------