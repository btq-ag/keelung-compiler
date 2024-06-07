{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}
{-# LANGUAGE DeriveGeneric #-}

module Test.Generic (run, tests) where

import Keelung hiding (MulU, VarUI)
import Keelung.Compiler.ConstraintModule (ConstraintModule (..))
import Keelung.Compiler.Relations qualified as Relations
import Test.Hspec
import Test.QuickCheck
import Test.Util
import GHC.Generics hiding (UInt)


run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests = describe "Generic Datatypes" $ do
  let program1 :: Integer -> Comp (Maybe (UInt 8, UInt 8))
      program1 divisor = do dividend <- inputUInt Public :: Comp (UInt 8)
                            if divisor == 0 then
                              return Nothing
                            else
                              Just <$> performDivMod dividend (UInt divisor)
  it "as intermediate values (Maybe)" $ do
    let (dividend, divisor) = (44, 2)
    let expected = [dividend `div` divisor, dividend `mod` divisor]
    check gf181 (program1 divisor) [dividend] [] expected
  it "as intermediate values (Maybe but returns Nothing)" $ do
    let (dividend, divisor) = (44, 0)
    let expected = []
    actual <- interpret gf181 (program1 divisor) [dividend] []
    actual `shouldBe` expected
  it "as inputs (inputData) and conditionals (eqData)" $ do
    let sameParent :: Comp Boolean
        sameParent = do p1 <- inputData Public :: Comp Person
                        p2 <- inputData Private :: Comp Person
                        return (eqData (parent p1) (parent p2))
    check gf181 sameParent [123, 456, 1, 3] [789, 321, 1, 3] [1]

data Person = Person {
  name :: Field,
  number :: UInt 8,
  parent :: (Boolean, UInt 8)
} deriving Generic

instance Inputable Person