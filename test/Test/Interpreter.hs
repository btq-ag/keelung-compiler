{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}

module Test.Interpreter (tests, run) where

import AggregateSignature.Program qualified as AggSig
import AggregateSignature.Util qualified as AggSig
import Basic qualified
import Control.Arrow (left)
import Keelung hiding (compile, run)
import Keelung.Compiler (Error (..), compile, toR1CS)
import Keelung.Compiler qualified as Compiler
import Keelung.Compiler.Constraint (relocateConstraintSystem)
import Keelung.Compiler.Syntax.Inputs qualified as Inputs
import Keelung.Constraint.R1CS (R1CS (..))
import Keelung.Interpreter.Kinded qualified as Kinded
import Keelung.Interpreter.Monad hiding (Error)
import Keelung.Interpreter.R1CS qualified as R1CS
import Keelung.Interpreter.Relocated qualified as Relocated
import Keelung.Interpreter.Typed qualified as Typed
import Test.Hspec
import Test.QuickCheck hiding ((.&.))

run :: IO ()
run = hspec tests

kinded :: (GaloisField n, Integral n, Encode t, Interpret t n) => Comp t -> [n] -> Either (Error n) [n]
kinded prog rawInputs = do
  elab <- left LangError (elaborate prog)
  let inps = Inputs.deserialize (compCounters (elabComp elab)) rawInputs
  left InterpretError (Kinded.run elab inps)

typed :: (GaloisField n, Integral n, Encode t) => Comp t -> [n] -> Either (Error n) [n]
typed prog rawInputs = do
  elab <- left LangError (elaborateAndEncode prog)
  let inps = Inputs.deserializeElab elab rawInputs
  left InterpretError (Typed.run elab inps)

cs :: (GaloisField n, Integral n, Encode t) => Comp t -> [n] -> Either (Error n) [n]
cs prog rawInputs = do
  r1cs' <- toR1CS . relocateConstraintSystem <$> Compiler.compileO1' prog
  let inps = Inputs.deserialize (r1csCounters r1cs') rawInputs
  case R1CS.run r1cs' inps of
    Left err -> Left (InterpretError err)
    Right outputs -> Right (Inputs.removeBinRepsFromOutputs (r1csCounters r1cs') outputs)

relocated :: (GaloisField n, Integral n, Encode t) => Comp t -> [n] -> Either (Error n) [n]
relocated prog rawInputs = do
  r1cs' <- toR1CS <$> compile prog
  let inps = Inputs.deserialize (r1csCounters r1cs') rawInputs
  case Relocated.run r1cs' inps of
    Left err -> Left (ExecError err)
    Right outputs -> Right (Inputs.removeBinRepsFromOutputs (r1csCounters r1cs') outputs)

r1cs :: (GaloisField n, Integral n, Encode t) => Comp t -> [n] -> Either (Error n) [n]
r1cs prog rawInputs = do
  r1cs' <- toR1CS <$> Compiler.compileO0 prog
  let inps = Inputs.deserialize (r1csCounters r1cs') rawInputs
  case R1CS.run r1cs' inps of
    Left err -> Left (InterpretError err)
    Right outputs -> Right (Inputs.removeBinRepsFromOutputs (r1csCounters r1cs') outputs)

-- runAll :: (GaloisField n, Integral n, Encode t) => Comp t -> [n] -> Expectation
runAll :: (GaloisField n, Integral n, Encode t, Interpret t n) => Comp t -> [n] -> [n] -> IO ()
runAll program rawInputs rawOutputs = do
  kinded program rawInputs
    `shouldBe` Right rawOutputs
  typed program rawInputs
    `shouldBe` Right rawOutputs
  cs program rawInputs
    `shouldBe` Right rawOutputs
  relocated program rawInputs
    `shouldBe` Right rawOutputs
  r1cs program rawInputs
    `shouldBe` Right rawOutputs

tests :: SpecWith ()
tests = do
  describe "Interpreters of different syntaxes should computes the same result" $ do
    it "Basic.identity" $
      property $ \inp -> do
        runAll Basic.identity [inp :: GF181] [inp]

    it "Basic.identityB" $ do
      runAll Basic.identityB [1 :: GF181] [1]
      runAll Basic.identityB [0 :: GF181] [0]

    it "Basic.add3" $ do
      property $ \inp -> do
        runAll Basic.add3 [inp :: GF181] [inp + 3]

    it "Basic.eq1" $
      property $ \inp -> do
        let expectedOutput = if inp == 3 then [1] else [0]
        runAll Basic.eq1 [inp :: GF181] expectedOutput

    it "Basic.cond'" $
      property $ \inp -> do
        let expectedOutput = if inp == 3 then [12] else [789]
        runAll Basic.cond' [inp :: GF181] expectedOutput

    it "Basic.assert1" $
      runAll Basic.assert1 [3 :: GF181] []

    it "Basic.toArrayM1" $
      runAll Basic.toArrayM1 [] [0 :: GF181]

    it "Basic.summation" $
      forAll (vector 4) $ \inp -> do
        let expectedOutput = [sum inp]
        runAll Basic.summation (inp :: [GF181]) expectedOutput

    it "Basic.summation2" $
      forAll (vector 4) $ \inp -> do
        let expectedOutput = []
        runAll Basic.summation2 (inp :: [GF181]) expectedOutput

    it "Basic.assertArraysEqual" $
      runAll Basic.assertArraysEqual [0, 2, 4, 8, 0, 2, 4, 8 :: GF181] []

    it "Basic.assertArraysEqual2" $
      runAll Basic.assertArraysEqual2 [0, 2, 4, 8, 0, 2, 4, 8 :: GF181] []

    it "Basic.array1D" $
      runAll (Basic.array1D 1) [2, 4 :: GF181] []

    it "Basic.array2D 1" $
      runAll (Basic.array2D 1 1) [2, 4 :: GF181] []

    it "Basic.array2D 2" $
      runAll (Basic.array2D 2 2) [0, 1, 2, 3, 0, 1, 4, 9 :: GF181] []

    it "Basic.toArray1" $
      runAll Basic.toArray1 [0 .. 7 :: GF181] []

    it "Basic.xorLists" $
      runAll Basic.xorLists [] [1 :: GF181]

    it "Basic.dupArray" $
      runAll Basic.dupArray [1] [1 :: GF181]

    it "Basic.returnArray2" $
      runAll Basic.returnArray2 [2] [2, 4 :: GF181]

    it "Basic.arithU0" $
      runAll Basic.arithU0 [2, 3] [5 :: GF181]

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

      runAll program [100, 1, 1 :: GF181] [101]
      runAll program [100, 0, 1 :: GF181] [102]

    it "Rotate" $ do
      let program = do
            x <- inputUInt @4
            return [rotate x (-4), rotate x (-3), rotate x (-2), rotate x (-1), rotate x 0, rotate x 1, rotate x 2, rotate x 3, rotate x 4]

      runAll program [0 :: GF181] [0, 0, 0, 0, 0, 0, 0, 0, 0]
      runAll program [1 :: GF181] [1, 2, 4, 8, 1, 2, 4, 8, 1]
      runAll program [3 :: GF181] [3, 6, 12, 9, 3, 6, 12, 9, 3]
      runAll program [5 :: GF181] [5, 10, 5, 10, 5, 10, 5, 10, 5]

    it "Basic.rotateAndBitTest" $
      -- 0011 0100211003
      runAll Basic.rotateAndBitTest [2, 3] [0, 0, 1, 1 :: GF181]

    it "Shift" $ do
      let program = do
            x <- inputUInt @4
            return [shift x (-4), shift x (-3), shift x (-2), shift x (-1), shift x 0, shift x 1, shift x 2, shift x 3, shift x 4]

      runAll program [0 :: GF181] [0, 0, 0, 0, 0, 0, 0, 0, 0]
      runAll program [1 :: GF181] [0, 0, 0, 0, 1, 2, 4, 8, 0]
      runAll program [3 :: GF181] [0, 0, 0, 1, 3, 6, 12, 8, 0]
      runAll program [5 :: GF181] [0, 0, 1, 2, 5, 10, 4, 8, 0]

    describe "Aggregate Signature" $ do
      it "dim:1 sig:1" $
        runAllKeelungAggSig 1 1 []
      it "dim:1 sig:10" $
        runAllKeelungAggSig 1 10 []
      it "dim:10 sig:1" $
        runAllKeelungAggSig 10 1 []
      it "dim:10 sig:10" $
        runAllKeelungAggSig 10 10 []
  where
    runAllKeelungAggSig :: Int -> Int -> [GF181] -> IO ()
    runAllKeelungAggSig dimension numberOfSignatures outputs =
      let settings =
            AggSig.Settings
              { AggSig.enableAggChecking = True,
                AggSig.enableSizeChecking = True,
                AggSig.enableLengthChecking = True
              }
          param = AggSig.makeParam dimension numberOfSignatures 42 settings :: AggSig.Param GF181
       in runAll
            (AggSig.aggregateSignature param :: Comp ())
            (AggSig.genInputFromParam param)
            outputs
