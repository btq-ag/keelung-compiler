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
import qualified Keelung.Compiler as Compiler
import qualified Keelung.Compiler.Syntax.Inputs as Inputs
import Keelung.Constraint.R1CS (R1CS (..))
import qualified Keelung.Interpreter.Kinded as Kinded
import Keelung.Interpreter.Monad hiding (Error)
import qualified Keelung.Interpreter.Relocated as Relocated
import qualified Keelung.Interpreter.R1CS as R1CS
import qualified Keelung.Interpreter.Typed as Typed
import Test.Hspec
import Test.QuickCheck hiding ((.&.))
import qualified AggregateSignature.Util as AggSig
import qualified AggregateSignature.Program as AggSig
import Keelung.Compiler.Constraint (relocateConstraintSystem)

kinded :: (GaloisField n, Integral n, Encode t, Interpret t n) => Comp t -> [n] -> Either (Error n) [n]
kinded prog rawInputs = do
  elab <- left LangError (elaborate' prog)
  let inps = Inputs.deserialize (compCounters (elabComp elab)) rawInputs
  left InterpretError (Kinded.run elab inps)

typed :: (GaloisField n, Integral n, Encode t) => Comp t -> [n] -> Either (Error n) [n]
typed prog rawInputs = do
  elab <- left LangError (elaborate prog)
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

-- run :: (GaloisField n, Integral n, Encode t) => Comp t -> [n] -> Expectation
run :: (GaloisField n, Integral n, Encode t, Interpret t n) => Comp t -> [n] -> [n] -> IO ()
run program rawInputs rawOutputs = do
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
        run Basic.identity [inp :: GF181] [inp]

    it "Basic.identityB" $ do
      run Basic.identityB [1 :: GF181] [1]
      run Basic.identityB [0 :: GF181] [0]

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

    it "Basic.assert1" $
      run Basic.assert1 [3 :: GF181] []

    it "Basic.toArrayM1" $
      run Basic.toArrayM1 [] [0 :: GF181]

    it "Basic.summation" $
      forAll (vector 4) $ \inp -> do
        let expectedOutput = [sum inp]
        run Basic.summation (inp :: [GF181]) expectedOutput

    it "Basic.summation2" $
      forAll (vector 4) $ \inp -> do
        let expectedOutput = []
        run Basic.summation2 (inp :: [GF181]) expectedOutput

    it "Basic.assertArraysEqual" $
      run Basic.assertArraysEqual [0, 2, 4, 8, 0, 2, 4, 8 :: GF181] []

    it "Basic.assertArraysEqual2" $
      run Basic.assertArraysEqual2 [0, 2, 4, 8, 0, 2, 4, 8 :: GF181] []

    it "Basic.array1D" $
      run (Basic.array1D 1) [2, 4 :: GF181] []

    it "Basic.array2D 1" $
      run (Basic.array2D 1 1) [2, 4 :: GF181] []

    it "Basic.array2D 2" $
      run (Basic.array2D 2 2) [0, 1, 2, 3, 0, 1, 4, 9 :: GF181] []

    it "Basic.toArray1" $
      run Basic.toArray1 [0 .. 7 :: GF181] []

    it "Basic.xorLists" $
      run Basic.xorLists [] [1 :: GF181]

    it "Basic.dupArray" $
      run Basic.dupArray [1] [1 :: GF181]

    it "Basic.returnArray2" $
      run Basic.returnArray2 [2] [2, 4 :: GF181]

    it "Basic.arithU0" $
      run Basic.arithU0 [2, 3] [5 :: GF181]

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

    it "Rotate" $ do
      let program = do
            x <- inputUInt @4
            return $ toArray [rotate x (-4), rotate x (-3), rotate x (-2), rotate x (-1), rotate x 0, rotate x 1, rotate x 2, rotate x 3, rotate x 4]

      run program [0 :: GF181] [0, 0, 0, 0, 0, 0, 0, 0, 0]
      run program [1 :: GF181] [1, 2, 4, 8, 1, 2, 4, 8, 1]
      run program [3 :: GF181] [3, 6, 12, 9, 3, 6, 12, 9, 3]
      run program [5 :: GF181] [5, 10, 5, 10, 5, 10, 5, 10, 5]

    it "Basic.rotateAndBitTest" $
      -- 0011 0100211003
      run Basic.rotateAndBitTest [2, 3] [0, 0, 1, 1 :: GF181]

    it "Shift" $ do
      let program = do
            x <- inputUInt @4
            return $ toArray [shift x (-4), shift x (-3), shift x (-2), shift x (-1), shift x 0, shift x 1, shift x 2, shift x 3, shift x 4]

      run program [0 :: GF181] [0, 0, 0, 0, 0, 0, 0, 0, 0]
      run program [1 :: GF181] [0, 0, 0, 0, 1, 2, 4, 8, 0]
      run program [3 :: GF181] [0, 0, 0, 1, 3, 6, 12, 8, 0]
      run program [5 :: GF181] [0, 0, 1, 2, 5, 10, 4, 8, 0]

    describe "Aggregate Signature" $ do
      it "dim:1 sig:1" $
        runKeelungAggSig 1 1 []
      it "dim:1 sig:10" $
        runKeelungAggSig 1 10 []
      it "dim:10 sig:1" $
        runKeelungAggSig 10 1 []
      it "dim:10 sig:10" $
        runKeelungAggSig 10 10 []
  where
    runKeelungAggSig :: Int -> Int -> [GF181] -> IO ()
    runKeelungAggSig dimension numberOfSignatures outputs =
      let settings =
            AggSig.Settings
              { AggSig.enableAggChecking = True,
                AggSig.enableSizeChecking = True,
                AggSig.enableLengthChecking = True
              }
          param = AggSig.makeParam dimension numberOfSignatures 42 settings :: AggSig.Param GF181
       in run
            (AggSig.aggregateSignature param :: Comp ())
            (AggSig.genInputFromParam param)
            outputs
