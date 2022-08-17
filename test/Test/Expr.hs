module Test.Expr (tests) where 

import Test.Hspec
import Test.QuickCheck

tests :: SpecWith ()
tests = do
  describe "read" $ do
    context "when used with Int" $ do
      it "is inverse to show" $ property $
        \x -> (read . show) x `shouldBe` (x :: Int)