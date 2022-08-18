module Test.Elaboration (tests) where 

import Test.Hspec
import Test.QuickCheck

tests :: SpecWith ()
tests = do
  describe "Elaboration should be successful" $ do
    it "is inverse to show" $ property $
      \x -> (read . show) x `shouldBe` (x :: Int)
      