{-# LANGUAGE DataKinds #-}

module Main where

import Basic qualified
-- import Control.Arrow (ArrowChoice (right), left)

import Control.Arrow (ArrowChoice (..))
import Data.Sequence qualified as Seq
import Keelung
import Keelung.Compiler
import Keelung.Compiler qualified as Compiler
import Keelung.Compiler.Relocated (cadd)
import Keelung.Constraint.R1CS (R1CS)
import Keelung.Data.Polynomial (Poly)
import Keelung.Data.Polynomial qualified as Poly
import Keelung.Syntax.Counters
import Test.Hspec
import Test.Interpreter qualified as Interpreter
import Test.Interpreter.Util (gf181Info)
import Test.Optimization qualified as Optimization
import Test.Relations.Boolean qualified as Relations.Boolean
import Test.Relations.Field qualified as Relations.Field
import Test.Relations.UInt qualified as Relations.UInt
import Test.VarLayout qualified as VarBookkeep
import Test.WitnessGeneration qualified as WitnessGeneration

main :: IO ()
main = hspec $ do
  describe "Witness generation" WitnessGeneration.tests

  describe "Interpreter" Interpreter.tests

  describe "Optimization" Optimization.tests

  describe "Variable Bookkeeping" VarBookkeep.tests

  describe "Field Relations" Relations.Field.tests

  describe "Boolean Relations" Relations.Boolean.tests

  describe "UInt Relations" Relations.UInt.tests

  describe "Poly" $ do
    it "instance Eq 1" $ Poly.buildEither 42 [(1, 1)] `shouldBe` (Poly.buildEither 42 [(1, 1)] :: Either GF181 (Poly GF181))
    it "instance Eq 2" $ Poly.buildEither 42 [(1, 1)] `shouldBe` (Poly.buildEither (-42) [(1, -1)] :: Either GF181 (Poly GF181))

  describe "Constraint Generation" $ do
    it "assertToBe42" $
      let cs =
            RelocatedConstraintSystem
              { csField = gf181Info,
                csUseNewOptimizer = False,
                csConstraints =
                  Seq.fromList $
                    cadd (-42 :: GF181) [(0, 1)],
                csBinReps = [],
                csCounters = addCount OfPublicInput OfField 1 mempty,
                csDivMods = [],
                csModInvs = []
              }
       in Compiler.compileWithoutConstProp gf181Info Basic.assertToBe42 `shouldBe` Right cs

  describe "Keelung `compile`" $ do
    it "Program that throws ElabError.IndexOutOfBoundsError" $ do
      let expected = left show ((toR1CS :: RelocatedConstraintSystem GF181 -> R1CS GF181) <$> Compiler.compile gf181Info Basic.outOfBound)
      actual <- right (fmap fromInteger) . left show <$> Keelung.compile gf181 Basic.outOfBound
      actual `shouldBe` expected

    it "Program that throws ElabError.EmptyArrayError" $ do
      let expected = left show ((toR1CS :: RelocatedConstraintSystem GF181 -> R1CS GF181) <$> Compiler.compile gf181Info Basic.emptyArray)
      actual <- right (fmap fromInteger) . left show <$> Keelung.compile gf181 Basic.emptyArray
      actual `shouldBe` expected

    it "Program that compiles successfully" $ do
      let expected = left show ((toR1CS :: RelocatedConstraintSystem GF181 -> R1CS GF181) <$> Compiler.compile gf181Info Basic.identity)
      actual <- right (fmap fromInteger) . left show <$> Keelung.compile gf181 Basic.identity
      actual `shouldBe` expected

  describe "Keelung `interpret`" $ do
    it "Program that throws ElabError.IndexOutOfBoundsError" $ do
      let expected = left show (Compiler.interpret Basic.outOfBound ([] :: [GF181]) ([] :: [GF181]))
      actual <- left show <$> Keelung.interpret_ gf181 Basic.outOfBound [] []
      actual `shouldBe` expected

    it "Program that throws ElabError.EmptyArrayError" $ do
      let expected = left show (Compiler.interpret Basic.emptyArray ([] :: [GF181]) ([] :: [GF181]))
      actual <- left show <$> Keelung.interpret_ gf181 Basic.emptyArray [] []
      actual `shouldBe` expected

    it "Basic.eq1 1" $ do
      let expected = left show (Compiler.interpret Basic.eq1 ([0] :: [GF181]) ([] :: [GF181]))
      actual <- left show <$> Keelung.interpret_ gf181 Basic.eq1 [0] []
      actual `shouldBe` expected

    it "Basic.eq1 2" $ do
      let expected = left show (Compiler.interpret Basic.eq1 ([3] :: [GF181]) ([] :: [GF181]))
      actual <- left show <$> Keelung.interpret_ gf181 Basic.eq1 [3] []
      actual `shouldBe` expected
