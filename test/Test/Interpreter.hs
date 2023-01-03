{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}

module Test.Interpreter (tests) where

import qualified Basic
import Control.Arrow (left)
import Keelung hiding (compile, run)
import Keelung.Compiler (Error (..), compile, toR1CS)
import qualified Keelung.Compiler.Interpret.Kinded as Kinded
import Keelung.Compiler.Interpret.Monad hiding (Error)
import qualified Keelung.Compiler.Interpret.R1CS as R1CS1
import qualified Keelung.Compiler.Interpret.R1CS2 as R1CS2
import qualified Keelung.Compiler.Interpret.Typed as Typed
import qualified Keelung.Compiler.Syntax.Inputs as Inputs
import Keelung.Constraint.R1CS (R1CS (..))
import Test.Hspec
import Test.QuickCheck hiding ((.&.))

kinded :: (GaloisField n, Integral n, Encode t, FreeVar t, Interpret t n) => Comp t -> [n] -> Either (Error n) [n]
kinded prog rawInputs = do
  elab <- left LangError (elaborate' prog)
  let inps = Inputs.deserialize (compCounters (elabComp elab)) rawInputs
  left InterpretError (Kinded.run elab inps)

typed :: (GaloisField n, Integral n, Encode t) => Comp t -> [n] -> Either (Error n) [n]
typed prog rawInputs = do
  elab <- left LangError (elaborate prog)
  let inps = Inputs.deserializeElab elab rawInputs
  left InterpretError (Typed.run elab inps)

r1cs1 :: (GaloisField n, Integral n, Encode t) => Comp t -> [n] -> Either (Error n) [n]
r1cs1 prog rawInputs = do
  r1cs <- toR1CS <$> compile prog
  let inps = Inputs.deserialize (r1csCounters r1cs) rawInputs
  left ExecError (R1CS1.run r1cs inps)

r1cs2 :: (GaloisField n, Integral n, Encode t) => Comp t -> [n] -> Either (Error n) [n]
r1cs2 prog rawInputs = do
  r1cs <- toR1CS <$> compile prog
  let inps = Inputs.deserialize (r1csCounters r1cs) rawInputs
  left InterpretError (R1CS2.run r1cs inps)

-- run :: (GaloisField n, Integral n, Encode t) => Comp t -> [n] -> Expectation
run :: (GaloisField n, Integral n, Encode t, FreeVar t, Interpret t n) => Comp t -> [n] -> [n] -> IO ()
run program rawInputs rawOutputs = do
  kinded program rawInputs
    `shouldBe` Right rawOutputs
  typed program rawInputs
    `shouldBe` Right rawOutputs
  r1cs1 program rawInputs
    `shouldBe` Right rawOutputs
  r1cs2 program rawInputs
    `shouldBe` Right rawOutputs

tests :: SpecWith ()
tests = do
  describe "Interpreters of different syntaxes should computes the same result" $ do
    it "Basic.identity" $
      property $ \inp -> do
        run Basic.identity [inp :: GF181] [inp]

    it "Basic.add3" $ do
      property $ \inp -> do
        run Basic.add3 [inp :: GF181] [inp + 3]

    it "Basic.eq1" $
      property $ \inp -> do
        let expectedOutput = if inp == 3 then [1] else [0]
        run Basic.eq1 [inp :: GF181] expectedOutput

    it "Basic.cond'" $
      property $ \inp -> do
        let expectedOutput = if inp == 3 then [12] else [789]
        run Basic.cond' [inp :: GF181] expectedOutput

    it "Basic.summation" $
      forAll (vector 4) $ \inp -> do
        let expectedOutput = [sum inp]
        run Basic.summation (inp :: [GF181]) expectedOutput

    it "Basic.summation2" $
      forAll (vector 4) $ \inp -> do
        let expectedOutput = []
        run Basic.summation2 (inp :: [GF181]) expectedOutput

    it "Mixed 0" $ do
      let program = do
            f <- inputField
            u4 <- inputUInt @4
            b <- inputBool
            return $
              cond
                (b .&. (u4 !!! 0))
                (f + 1)
                (f + 2)

      run program [100, 1, 1 :: GF181] [101]

      run program [100, 0, 1 :: GF181] [102]

    -- it "Rotate" $ do
    --   let program = do
    --         x <- inputUInt @4
    --         return $ toArray [rotate x (-4), rotate x (-3), rotate x (-2), rotate x (-1), rotate x 0, rotate x 1, rotate x 2, rotate x 3, rotate x 4]

    --   run program [0 :: GF181] [0, 0, 0, 0, 0, 0, 0, 0, 0]

      
      -- run program [1 :: GF181] [1, 2, 4, 8, 1, 2, 4, 8, 1]
      -- run program [3 :: GF181] [3, 6, 12, 9, 3, 6, 12, 9, 3]
      -- run program [5 :: GF181] [5, 10, 5, 10, 5, 10, 5, 10, 5]

-- it "Shift" $ do
--   let program = do
--         x <- inputUInt @4
--         return $ toArray [shift x (-4), shift x (-3), shift x (-2), shift x (-1), shift x 0, shift x 1, shift x 2, shift x 3, shift x 4]

--   kinded program [0 :: GF181]
--     `shouldBe` Right [0, 0, 0, 0, 0, 0, 0, 0, 0]
--   typed program [0 :: GF181]
--     `shouldBe` Right [0, 0, 0, 0, 0, 0, 0, 0, 0]

--   kinded program [1 :: GF181]
--     `shouldBe` Right [0, 0, 0, 0, 1, 2, 4, 8, 0]
--   typed program [1 :: GF181]
--     `shouldBe` Right [0, 0, 0, 0, 1, 2, 4, 8, 0]

--   kinded program [3 :: GF181]
--     `shouldBe` Right [0, 0, 0, 1, 3, 6, 12, 8, 0]
--   typed program [3 :: GF181]
--     `shouldBe` Right [0, 0, 0, 1, 3, 6, 12, 8, 0]

--   kinded program [5 :: GF181]
--     `shouldBe` Right [0, 0, 1, 2, 5, 10, 4, 8, 0]
--   typed program [5 :: GF181]
--     `shouldBe` Right [0, 0, 1, 2, 5, 10, 4, 8, 0]