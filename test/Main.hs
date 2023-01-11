{-# LANGUAGE DataKinds #-}

module Main where

import qualified Basic
-- import Control.Arrow (ArrowChoice (right), left)

import Control.Arrow (ArrowChoice (..))
import qualified Data.Set as Set
import Keelung
import Keelung.Compiler
import qualified Keelung.Compiler as Compiler
import Keelung.Compiler.Relocated (cadd)
import Keelung.Constraint.Polynomial (Poly)
import qualified Keelung.Constraint.Polynomial as Poly
import Keelung.Constraint.R1CS (R1CS)
import Keelung.Syntax.Counters
import qualified Test.Compilation as Compilation
import qualified Test.ConstraintMinimizer as ConstraintMinimizer
import Test.Hspec
import qualified Test.Interpreter as Interpreter
import qualified Test.Optimization as Optimization
import qualified Test.VarLayout as VarBookkeep

main :: IO ()
main = hspec $ do
  describe "Interpreter" Interpreter.tests

  describe "Compilation" Compilation.tests

  describe "Constraint Minimization" ConstraintMinimizer.tests

  describe "Optimization" Optimization.tests

  describe "Variable Bookkeeping" VarBookkeep.tests

  describe "Poly" $ do
    it "instance Eq 1" $ Poly.buildEither 42 [(1, 1)] `shouldBe` (Poly.buildEither 42 [(1, 1)] :: Either GF181 (Poly GF181))
    it "instance Eq 2" $ Poly.buildEither 42 [(1, 1)] `shouldBe` (Poly.buildEither (-42) [(1, -1)] :: Either GF181 (Poly GF181))

  describe "Constraint Generation" $ do
    it "assertToBe42" $
      let cs =
            RelocatedConstraintSystem
              { csConstraints =
                  Set.fromList $
                    cadd (-42 :: GF181) [(0, 1)],
                csCounters = addCount OfInput OfField 1 mempty
              }
       in Compiler.compileOnly Basic.assertToBe42 `shouldBe` Right cs

  describe "Keelung `compile`" $ do
    it "Program that throws ElabError.IndexOutOfBoundsError" $ do
      let expected = left show ((toR1CS :: RelocatedConstraintSystem GF181 -> R1CS GF181) <$> Compiler.compile Basic.outOfBound)
      actual <- right (fmap fromInteger) . left show <$> Keelung.compile GF181 Basic.outOfBound
      actual `shouldBe` expected

    it "Program that throws ElabError.EmptyArrayError" $ do
      let expected = left show ((toR1CS :: RelocatedConstraintSystem GF181 -> R1CS GF181) <$> Compiler.compile Basic.emptyArray)
      actual <- right (fmap fromInteger) . left show <$> Keelung.compile GF181 Basic.emptyArray
      actual `shouldBe` expected

    it "Program that compiles successfully" $ do
      let expected = left show ((toR1CS :: RelocatedConstraintSystem GF181 -> R1CS GF181) <$> Compiler.compile Basic.identity)
      actual <- right (fmap fromInteger) . left show <$> Keelung.compile GF181 Basic.identity
      actual `shouldBe` expected

  describe "Keelung `interpret`" $ do
    it "Program that throws ElabError.IndexOutOfBoundsError" $ do
      let expected = left show (Compiler.interpret Basic.outOfBound ([] :: [GF181]))
      actual <- left show <$> Keelung.interpret_ GF181 Basic.outOfBound []
      actual `shouldBe` expected

    it "Program that throws ElabError.EmptyArrayError" $ do
      let expected = left show (Compiler.interpret Basic.emptyArray ([] :: [GF181]))
      actual <- left show <$> Keelung.interpret_ GF181 Basic.emptyArray []
      actual `shouldBe` expected

    it "Basic.eq1 1" $ do
      let expected = left show (Compiler.interpret Basic.eq1 ([0] :: [GF181]))
      actual <- left show <$> Keelung.interpret_ GF181 Basic.eq1 [0]
      actual `shouldBe` expected

    it "Basic.eq1 2" $ do
      let expected = left show (Compiler.interpret Basic.eq1 ([3] :: [GF181]))
      actual <- left show <$> Keelung.interpret_ GF181 Basic.eq1 [3]
      actual `shouldBe` expected
