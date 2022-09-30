module Test.Optimization (tests) where

import qualified Basic
import Keelung (Comp, Elaborable, GF181)
import Keelung.Compiler (asGF181, optimize1, toR1CS)
import Keelung.Compiler.Error (Error)
import Keelung.Constraint.R1CS (toR1Cs)
import Keelung.Field (N)
import Test.Hspec

tests :: SpecWith ()
tests = do
  describe "Constraint Number" $ do
    describe "AND Chaining" $ do
      it "1 variable" $ count (Basic.chainingAND 1) `shouldBe` Right (1 + 1)
      it "2 variable" $ count (Basic.chainingAND 2) `shouldBe` Right (2 + 1)
      it "3 variable" $ count (Basic.chainingAND 3) `shouldBe` Right (3 + 2)
      it "4 variable" $ count (Basic.chainingAND 4) `shouldBe` Right (4 + 2)
      it "5 variable" $ count (Basic.chainingAND 5) `shouldBe` Right (5 + 2)
  where
    -- | Count the number of generated constraints from a given program.
    count :: Elaborable t => Comp t -> Either (Error (N GF181)) Int
    count program = do
      cs <- asGF181 (optimize1 program)
      return $ length $ toR1Cs $ toR1CS cs
