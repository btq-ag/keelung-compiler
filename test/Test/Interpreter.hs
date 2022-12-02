{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}

module Test.Interpreter (tests) where

import qualified Basic
import Control.Arrow (left)
import Data.Field.Galois (GaloisField)
import Keelung (Comp, Computation (compCounters), Encode, Elaborated (elabComp), GF181, elaborate, elaborate')
import Keelung.Compiler (Error (..))
import qualified Keelung.Compiler.Interpret.Kinded as Kinded
import qualified Keelung.Compiler.Interpret.Typed as Typed
import qualified Keelung.Compiler.Syntax.Inputs as Inputs
import Test.Hspec
import Test.QuickCheck

kinded :: (GaloisField n, Integral n, Encode t, Kinded.FreeVar t, Kinded.Interpret t n) => Comp t -> [n] -> Either String [n]
kinded prog rawInputs = do
  elab <- left show (elaborate' prog)
  let inputs = Inputs.deserialize (compCounters (elabComp elab)) rawInputs
  left show (Kinded.runAndCheck elab inputs)

typed :: (GaloisField n, Integral n, Encode t) => Comp t -> [n] -> Either (Error n) [n]
typed prog rawInputs = do
  elab <- left LangError (elaborate prog)
  let inputs = Inputs.deserializeElab elab rawInputs
  left InterpretError (Typed.runAndCheck elab inputs)

tests :: SpecWith ()
tests = do
  describe "Interpreters of different syntaxes should computes the same result" $ do
    it "Basic.identity" $
      property $ \input -> do
        kinded Basic.identity [input :: GF181]
          `shouldBe` Right [input]
        typed Basic.identity [input :: GF181]
          `shouldBe` Right [input]

    it "Basic.add3" $
      property $ \input -> do
        kinded Basic.add3 [input :: GF181]
          `shouldBe` Right [input + 3]
        typed Basic.add3 [input :: GF181]
          `shouldBe` Right [input + 3]

    it "Basic.eq1" $
      property $ \input -> do
        let expectedOutput = if input == 3 then [1] else [0]
        kinded Basic.eq1 [input :: GF181]
          `shouldBe` Right expectedOutput
        typed Basic.eq1 [input :: GF181]
          `shouldBe` Right expectedOutput

    it "Basic.cond'" $
      property $ \input -> do
        let expectedOutput = if input == 3 then [12] else [789]
        kinded Basic.cond' [input :: GF181]
          `shouldBe` Right expectedOutput
        typed Basic.cond' [input :: GF181]
          `shouldBe` Right expectedOutput

    it "Basic.summation" $
      forAll (vector 4) $ \input -> do
        let expectedOutput = [sum input]
        kinded Basic.summation (input :: [GF181])
          `shouldBe` Right expectedOutput
        typed Basic.summation input
          `shouldBe` Right expectedOutput

    it "Basic.summation2" $
      forAll (vector 4) $ \input -> do
        let expectedOutput = []
        kinded Basic.summation2 (input :: [GF181])
          `shouldBe` Right expectedOutput
        typed Basic.summation2 input
          `shouldBe` Right expectedOutput

    -- it "Rotate" $
    --   let program = do 
    --     x <- inputUInt @4 
    --     return [shift (-4) x, shift 4 
    
    --   kinded Basic.summation2 (input :: [GF181])
    --     `shouldBe` Right expectedOutput
    --   typed Basic.summation2 input
    --     `shouldBe` Right expectedOutput
