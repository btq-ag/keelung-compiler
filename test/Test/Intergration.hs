module Test.Intergration (tests, run) where

import Basic qualified
import Hash.Poseidon qualified
import Control.Arrow
import Keelung
import Keelung.Compiler (ConstraintSystem)
import Keelung.Compiler qualified as Compiler
import Keelung.Constraint.R1CS
import Test.Compilation.Util (gf181Info)
import Test.Hspec
-- import qualified Hash.Poseidon as Poseidon

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
    
    -- describe "Poseidon" $ do
    --   it "length: 1" $ do
    --     let expected = left show ((Compiler.toR1CS :: ConstraintSystem GF181 -> R1CS GF181) <$> Compiler.compileAndLink gf181Info Basic.outOfBound)
    --     let program = do 
    --           x <- input Public
    --           result <- Poseidon.hash [x]
    --           return [result]
    --     actual <- right (fmap fromInteger) . left show <$> Keelung.compile gf181 program
    --     -- (Poseidon.hash [0]) [] [] [969784935791658820122994814042437418105599415561111385]
    --     actual `shouldBe` expected

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
          let expected = right Compiler.toR1CS $ left show (Compiler.compileAndLinkO1 gf181Info program :: Either (Compiler.Error GF181) (ConstraintSystem GF181))
          actual <- right (fmap fromIntegral) . left show <$> Keelung.compile gf181 program
          actual `shouldBe` expected

    it "Basic.eq1" $ do
      test Basic.eq1

    it "Hash.Poseidon.hash" $ do
      test $ do 
        x <- input Public
        result <- Hash.Poseidon.hash [x]
        return [result]