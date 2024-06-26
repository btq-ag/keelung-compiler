module Test.Intergration (tests, run) where

import Basic qualified
import Control.Arrow
import Hash.Poseidon qualified
import Keelung
import Keelung.Compiler qualified as Compiler
import Keelung.Constraint.R1CS
import Test.Util
import Test.Hspec

-- import qualified Hash.Poseidon as Poseidon

run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = describe "Intergration tests" $ do
  describe "Keelung `compile`" $ do
    it "Program that throws ElabError.IndexOutOfBoundsError" $ do
      let expected = left show (Compiler.compile gf181 Basic.outOfBound >>= Compiler.link >>= Compiler.toR1CS) :: Either String (R1CS GF181)
      actual <- right (fmap fromInteger) . left show <$> Keelung.compile gf181 Basic.outOfBound
      actual `shouldBe` expected

    it "Program that throws ElabError.EmptyArrayError" $ do
      let expected = left show (Compiler.compile gf181 Basic.emptyArray >>= Compiler.link >>= Compiler.toR1CS) :: Either String (R1CS GF181)
      actual <- right (fmap fromInteger) . left show <$> Keelung.compile gf181 Basic.emptyArray
      actual `shouldBe` expected

    it "Program that compiles successfully" $ do
      let expected = left show (Compiler.compile gf181 Basic.identity >>= Compiler.link >>= Compiler.toR1CS) :: Either String (R1CS GF181)
      actual <- right (fmap fromInteger) . left show <$> Keelung.compile gf181 Basic.identity
      actual `shouldBe` expected

  describe "Keelung `interpret`" $ do
    it "Program that throws ElabError.IndexOutOfBoundsError" $ do
      let expected = left show (Compiler.interpret gf181Info Basic.outOfBound [] [] :: Either (Compiler.Error GF181) [Integer])
      actual <- right (map toInteger) . left show <$> Keelung.interpretEither gf181 Basic.outOfBound [] []
      actual `shouldBe` expected

    it "Program that throws ElabError.EmptyArrayError" $ do
      let expected = left show (Compiler.interpret gf181Info Basic.emptyArray [] [] :: Either (Compiler.Error GF181) [Integer])
      actual <- right (map toInteger) . left show <$> Keelung.interpretEither gf181 Basic.emptyArray [] []
      actual `shouldBe` expected

    it "Basic.eq1 1" $ do
      let expected = left show (Compiler.interpret gf181Info Basic.eq1 [0] [] :: Either (Compiler.Error GF181) [Integer])
      actual <- right (map toInteger) . left show <$> Keelung.interpretEither gf181 Basic.eq1 [0] []
      actual `shouldBe` expected

    it "Basic.eq1 2" $ do
      let expected = left show (Compiler.interpret gf181Info Basic.eq1 [3] [] :: Either (Compiler.Error GF181) [Integer])
      actual <- right (map toInteger) . left show <$> Keelung.interpretEither gf181 Basic.eq1 [3] []
      actual `shouldBe` expected

  describe "Keelung `compile`" $ do
    let test program = do
          let expected = left show ((Compiler.compile gf181 program >>= Compiler.link >>= Compiler.toR1CS) :: Either (Compiler.Error GF181) (R1CS GF181))
          actual <- right (fmap fromIntegral) . left show <$> Keelung.compile gf181 program
          actual `shouldBe` expected

    it "Basic.eq1" $ do
      test Basic.eq1

    it "Hash.Poseidon.hash" $ do
      test $ do
        x <- input Public
        result <- Hash.Poseidon.hash [x]
        return [result]