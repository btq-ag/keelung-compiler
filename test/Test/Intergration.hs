module Test.Intergration (tests, run) where

import Basic qualified
import Control.Arrow
import Keelung
import Keelung.Compiler (ConstraintSystem)
import Keelung.Compiler qualified as Compiler
import Keelung.Constraint.R1CS
import Test.Compilation.Util (gf181Info)
import Test.Hspec

run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = describe "Intergration tests" $ do
  describe "Keelung `compile`" $ do
    it "Program that throws ElabError.IndexOutOfBoundsError" $ do
      let expected = left show ((Compiler.toR1CS :: ConstraintSystem GF181 -> R1CS GF181) <$> Compiler.compileAndLink gf181Info Basic.outOfBound)
      actual <- right (fmap fromInteger) . left show <$> Keelung.compile gf181 Basic.outOfBound
      actual `shouldBe` expected

    it "Program that throws ElabError.EmptyArrayError" $ do
      let expected = left show ((Compiler.toR1CS :: ConstraintSystem GF181 -> R1CS GF181) <$> Compiler.compileAndLink gf181Info Basic.emptyArray)
      actual <- right (fmap fromInteger) . left show <$> Keelung.compile gf181 Basic.emptyArray
      actual `shouldBe` expected

    it "Program that compiles successfully" $ do
      let expected = left show ((Compiler.toR1CS :: ConstraintSystem GF181 -> R1CS GF181) <$> Compiler.compileAndLink gf181Info Basic.identity)
      actual <- right (fmap fromInteger) . left show <$> Keelung.compile gf181 Basic.identity
      actual `shouldBe` expected

  describe "Keelung `interpret`" $ do
    it "Program that throws ElabError.IndexOutOfBoundsError" $ do
      let expected = left show (Compiler.interpret Basic.outOfBound [] [] :: Either (Compiler.Error GF181) [Integer])
      actual <- right (map toInteger) . left show <$> Keelung.interpretEither gf181 Basic.outOfBound [] []
      actual `shouldBe` expected

    it "Program that throws ElabError.EmptyArrayError" $ do
      let expected = left show (Compiler.interpret Basic.emptyArray [] [] :: Either (Compiler.Error GF181) [Integer])
      actual <- right (map toInteger) . left show <$> Keelung.interpretEither gf181 Basic.emptyArray [] []
      actual `shouldBe` expected

    it "Basic.eq1 1" $ do
      let expected = left show (Compiler.interpret Basic.eq1 [0] [] :: Either (Compiler.Error GF181) [Integer])
      actual <- right (map toInteger) . left show <$> Keelung.interpretEither gf181 Basic.eq1 [0] []
      actual `shouldBe` expected

    it "Basic.eq1 2" $ do
      let expected = left show (Compiler.interpret Basic.eq1 [3] [] :: Either (Compiler.Error GF181) [Integer])
      actual <- right (map toInteger) . left show <$> Keelung.interpretEither gf181 Basic.eq1 [3] []
      actual `shouldBe` expected
