{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}

module Test.Interpreter (tests, run, runAll) where

import AggregateSignature.Program qualified as AggSig
import AggregateSignature.Util qualified as AggSig
import Basic qualified
import Control.Arrow (left)
import Control.Monad (when)
import Hash.Poseidon qualified as Poseidon
import Keelung hiding (compile, run)
import Keelung.Compiler (Error (..), toR1CS)
import Keelung.Compiler qualified as Compiler
import Keelung.Compiler.ConstraintSystem qualified as Relocated
import Keelung.Compiler.Syntax.Inputs qualified as Inputs
import Keelung.Constraint.R1CS (R1CS (..))
import Keelung.Interpreter.Kinded qualified as Kinded
import Keelung.Interpreter.Monad hiding (Error)
import Keelung.Interpreter.R1CS qualified as R1CS
import Keelung.Interpreter.Relocated qualified as Relocated
import Keelung.Interpreter.Typed qualified as Typed
import Keelung.Syntax.Encode.Syntax qualified as Encoded
import Test.Hspec
import Test.QuickCheck hiding ((.&.))

run :: IO ()
run = hspec tests

kinded :: (GaloisField n, Integral n, Encode t, Interpret t n) => Comp t -> [n] -> [n] -> Either (Error n) [n]
kinded prog rawPublicInputs rawPrivateInputs = do
  elab <- left LangError (elaborate prog)
  inputs <- left (InterpretError . InputError) (Inputs.deserialize (compCounters (elabComp elab)) rawPublicInputs rawPrivateInputs)
  left InterpretError (Kinded.run elab inputs)

typed :: (GaloisField n, Integral n, Encode t) => Comp t -> [n] -> [n] -> Either (Error n) [n]
typed prog rawPublicInputs rawPrivateInputs = do
  elab <- left LangError (elaborateAndEncode prog)
  inputs <- left (InterpretError . InputError) (Inputs.deserialize (Encoded.compCounters (Encoded.elabComp elab)) rawPublicInputs rawPrivateInputs)
  left InterpretError (Typed.run elab inputs)

-- csOld :: (GaloisField n, Integral n, Encode t) => Comp t -> [n] -> Either (Error n) [n]
-- csOld prog rawInputs = do
--   r1cs <- toR1CS <$> Compiler.compileO1 prog
--   let inputs = Inputs.deserialize (r1csCounters r1cs) rawInputs
--   case R1CS.run r1cs inputs of
--     Left err -> Left (InterpretError err)
--     Right outputs -> Right (Inputs.removeBinRepsFromOutputs (r1csCounters r1cs) outputs)

r1csNew :: (GaloisField n, Integral n, Encode t) => Comp t -> [n] -> [n] -> Either (Error n) [n]
r1csNew prog rawPublicInputs rawPrivateInputs = do
  r1cs <- toR1CS <$> Compiler.compileO1 prog
  inputs <- left (InterpretError . InputError) (Inputs.deserialize (r1csCounters r1cs) rawPublicInputs rawPrivateInputs)
  case R1CS.run r1cs inputs of
    Left err -> Left (InterpretError err)
    Right outputs -> Right (Inputs.removeBinRepsFromOutputs (r1csCounters r1cs) outputs)

r1csOld :: (GaloisField n, Integral n, Encode t) => Comp t -> [n] -> [n] -> Either (Error n) [n]
r1csOld prog rawPublicInputs rawPrivateInputs = do
  r1cs <- toR1CS <$> Compiler.compileO1Old prog
  inputs <- left (InterpretError . InputError) (Inputs.deserialize (r1csCounters r1cs) rawPublicInputs rawPrivateInputs)
  case Relocated.run r1cs inputs of
    Left err -> Left (ExecError err)
    Right outputs -> Right (Inputs.removeBinRepsFromOutputs (r1csCounters r1cs) outputs)

r1csO0New :: (GaloisField n, Integral n, Encode t) => Comp t -> [n] -> [n] -> Either (Error n) [n]
r1csO0New prog rawPublicInputs rawPrivateInputs = do
  r1cs <- toR1CS . Relocated.relocateConstraintSystem <$> Compiler.compileO0 prog
  inputs <- left (InterpretError . InputError) (Inputs.deserialize (r1csCounters r1cs) rawPublicInputs rawPrivateInputs)
  case R1CS.run r1cs inputs of
    Left err -> Left (InterpretError err)
    Right outputs -> Right (Inputs.removeBinRepsFromOutputs (r1csCounters r1cs) outputs)

runAll' :: (GaloisField n, Integral n, Encode t, Interpret t n, Show t) => Bool -> Comp t -> [n] -> [n] -> Either (Error n) [n] -> IO ()
runAll' enableOldOptimizer program rawPublicInputs rawPrivateInputs rawOutputs = do
  -- print $ Compiler.asGF181N $ Compiler.compileO0 program
  -- print $ Compiler.asGF181N $ Compiler.compileO1 program
  -- print $ Compiler.asGF181N $ Compiler.compileO1' program
  -- print (Compiler.asGF181N $ toR1CS . relocateConstraintSystem <$> Compiler.compileO1' program)

  -- kinded program rawPublicInputs rawPrivateInputs
  --   `shouldBe` rawOutputs
  -- typed program rawPublicInputs rawPrivateInputs
  --   `shouldBe` rawOutputs
  r1csNew program rawPublicInputs rawPrivateInputs
    `shouldBe` rawOutputs
  -- when enableOldOptimizer $
  --   r1csOld program rawPublicInputs rawPrivateInputs
  --     `shouldBe` rawOutputs
  -- r1csO0New program rawPublicInputs rawPrivateInputs
  --   `shouldBe` rawOutputs

runAll :: (GaloisField n, Integral n, Encode t, Interpret t n, Show t) => Comp t -> [n] -> [n] -> [n] -> IO ()
runAll f i p o = runAll' True f i p (Right o)

throwAll :: (GaloisField n, Integral n, Encode t, Interpret t n, Show t) => Comp t -> [n] -> [n] -> Error n -> IO ()
throwAll f i p e = runAll' True f i p (Left e)

runAllExceptForTheOldOptimizer :: (GaloisField n, Integral n, Encode t, Interpret t n, Show t) => Comp t -> [n] -> [n] -> [n] -> IO ()
runAllExceptForTheOldOptimizer f i p o = runAll' False f i p (Right o)

runAndCompare :: (GaloisField n, Integral n, Encode t, Interpret t n) => Bool -> Comp t -> [n] -> [n] -> IO ()
runAndCompare enableOldOptimizer program rawPublicInputs rawPrivateInputs = do
  let expectedOutput = kinded program rawPublicInputs rawPrivateInputs
  typed program rawPublicInputs rawPrivateInputs
    `shouldBe` expectedOutput
  r1csNew program rawPublicInputs rawPrivateInputs
    `shouldBe` expectedOutput
  when enableOldOptimizer $
    r1csOld program rawPublicInputs rawPrivateInputs
      `shouldBe` expectedOutput
  r1csO0New program rawPublicInputs rawPrivateInputs
    `shouldBe` expectedOutput

_debug :: Encode t => Comp t -> IO ()
_debug program = do
  -- print $ Compiler.asGF181N $ Compiler.compileO0 program
  -- print $ Compiler.asGF181N $ Compiler.compileO1 program
  print $ Compiler.asGF181N $ Compiler.compileO1 program
  print (Compiler.asGF181N $ toR1CS <$> Compiler.compileO1 program)

tests :: SpecWith ()
tests = do
  describe "Interpreters of different syntaxes should computes the same result" $ do
    describe "Errors" $ do
      it "missing 1 public input" $ do
        let program = complement <$> inputBool Public
        throwAll program [] [] (InterpretError (InputError (Inputs.PublicInputSizeMismatch 1 0)) :: Error GF181)

      it "missing 1 private input" $ do
        let program = complement <$> inputBool Private
        throwAll program [] [] (InterpretError (InputError (Inputs.PrivateInputSizeMismatch 1 0)) :: Error GF181)

    describe "Boolean" $ do
      it "not 1" $ do
        let program = return $ complement true
        runAll program [] [] [0 :: GF181]

      it "not 2" $ do
        let program = complement <$> inputBool Public
        runAll program [0] [] [1 :: GF181]
        runAll program [1] [] [0 :: GF181]

      it "and 1" $ do
        let program = return $ true `And` false
        runAll program [] [] [0 :: GF181]

      it "and 2" $ do
        let program = And <$> input Public <*> input Private
        runAll program [1] [0] [0 :: GF181]
        runAll program [1] [1] [1 :: GF181]
        runAll program [0] [1] [0 :: GF181]
        runAll program [1] [1] [1 :: GF181]

      it "or 1" $ do
        let program = return $ true `Or` false
        runAll program [] [] [1 :: GF181]

      it "or 2" $ do
        let program = Or true <$> input Private
        runAll program [] [0] [1 :: GF181]
        runAll program [] [1] [1 :: GF181]

      it "xor 1" $ do
        let program = return $ true `Xor` false
        runAll program [] [] [1 :: GF181]

      it "xor 2" $ do
        let program = Xor <$> input Public <*> return true
        runAll program [0] [] [1 :: GF181]
        runAll program [1] [] [0 :: GF181]

      it "mixed 1" $ do
        let program = do
              x <- input Public
              y <- input Private
              let z = true
              return $ x `Or` y `And` z
        runAll program [0] [0] [0 :: GF181]
        runAll program [0] [1] [1 :: GF181]
        runAll program [1] [0] [1 :: GF181]
        runAll program [1] [1] [1 :: GF181]

      it "mixed 2" $ do
        let program = do
              x <- input Public
              y <- input Private
              let z = false
              w <- reuse $ x `Or` y
              return $ x `And` w `Or` z
        runAll program [0] [0] [0 :: GF181]
        runAll program [0] [1] [0 :: GF181]
        runAll program [1] [0] [1 :: GF181]
        runAll program [1] [1] [1 :: GF181]

      it "eq 1" $ do
        -- takes an input and see if its equal to False
        let program = do
              x <- input Public
              return $ x `eq` false

        runAll program [0] [] [1 :: GF181]
        runAll program [1] [] [0 :: GF181]

      it "conditional" $ do
        let program = do
              x <- inputField Public
              return $ cond (x `eq` 3) true false
        property $ \x -> do
          let expectedOutput = if x == 3 then [1] else [0]
          runAll program [x :: GF181] [] expectedOutput

      it "BtoF" $ do
        let program = do
              x <- input Public
              y <- input Private
              return $ BtoF x * BtoF y
        runAll program [1 :: GF181] [1] [1]

    describe "Field" $ do
      it "arithmetics 1" $ do
        let program = do
              x <- inputField Public
              y <- inputField Public
              return $ x * y + y * 2
        property $ \(x, y) -> do
          runAll program [x, y :: GF181] [] [x * y + y * 2]

      it "arithmetics 2" $ do
        let program = do
              x <- inputField Public
              y <- inputField Private
              z <- reuse $ x * y + y * 2
              return $ x * y - z
        property $ \(x, y) -> do
          runAll program [x :: GF181] [y] [-y * 2]

      it "arithmetics 3" $ do
        let program = do
              x <- inputField Private
              y <- inputField Public
              let z = 3
              return $ x * z + y * 2
        property $ \(x, y) -> do
          runAll program [y :: GF181] [x] [x * 3 + y * 2]

      it "summation" $ do
        let program = do
              arr <- inputList Public 4
              reduce 0 [0 .. 3] $ \accum i -> do
                let x = arr !! i
                return (accum + x :: Field)

        forAll (vector 4) $ \xs -> do
          runAll program (xs :: [GF181]) [] [sum xs]

      it "eq 1" $ do
        -- takes an input and see if its equal to 3
        let program = do
              x <- inputField Public
              return $ x `eq` 3

        property $ \x -> do
          let expectedOutput = if x == 3 then [1] else [0]
          runAll program [x :: GF181] [] expectedOutput

      it "conditional" $ do
        let program = do
              x <- inputField Public
              return $ cond (x `eq` 3) 4 (5 :: Field)
        property $ \x -> do
          let expectedOutput = if x == 3 then [4] else [5]
          runAll program [x :: GF181] [] expectedOutput

    describe "Unsigned Integers" $ do
      it "arithmetics 1" $ do
        let program = do
              f <- inputField Public
              u4 <- inputUInt @4 Public
              b <- inputBool Public
              return $
                cond
                  (b .&. (u4 !!! 0))
                  (f + 1)
                  (f + 2)

        runAll program [100, 1, 1 :: GF181] [] [101]
        runAll program [100, 0, 1 :: GF181] [] [102]

      it "add 1" $ do
        let program = do
              x <- inputUInt @4 Public
              y <- inputUInt @4 Public
              return $ x + y

        runAll program [5, 6 :: GF181] [] [11]
        runAll program [2, 5 :: GF181] [] [7]
        runAll program [15, 1 :: GF181] [] [0]

      it "add 2" $ do
        let program = do
              x <- inputUInt @4 Public
              y <- inputUInt @4 Public
              z <- inputUInt @4 Public
              w <- reuse $ x + y
              return $ x + y + z + w

        runAll program [5, 6, 7 :: GF181] [] [13]
        runAll program [2, 5, 3 :: GF181] [] [1]
        runAll program [0, 1, 2 :: GF181] [] [4]

      it "mul 3" $ do
        let program = do
              x <- inputUInt @4 Public
              y <- inputUInt @4 Public
              return $ x * y

        runAll program [2, 4 :: GF181] [] [8]
        runAll program [5, 6 :: GF181] [] [14]

      it "arithmetics 4" $ do
        let program = do
              x <- inputUInt @4 Public
              y <- inputUInt @4 Public
              return $ x * y + y

        runAll program [5, 6 :: GF181] [] [4]
        runAll program [2, 5 :: GF181] [] [15]
        runAll program [15, 1 :: GF181] [] [0]

      it "arithmetics 5" $ do
        let program = do
              x <- inputUInt @4 Public
              y <- reuse x
              return (x + y)

        runAllExceptForTheOldOptimizer program [5 :: GF181] [] [10]

      it "performDivMod (quotient & remainder unknown)" $ do
        let program = do
              dividend <- input Private :: Comp (UInt 4)
              divisor <- input Public
              performDivMod dividend divisor
        runAllExceptForTheOldOptimizer program [7 :: GF181] [20] [2, 6]
        runAllExceptForTheOldOptimizer program [4 :: GF181] [4] [1, 0]

      it "assertDivMod (multiple statements)" $ do
        let program = do
              a <- input Public :: Comp (UInt 5)
              b <- input Public
              c <- input Private
              d <- input Public
              (q0, r0) <- performDivMod a b
              (q1, r1) <- performDivMod c d
              return [q0, r0, q1, r1]
        runAllExceptForTheOldOptimizer program [20, 7, 8 :: GF181] [21] [2, 6, 2, 5]

      it "assertDivMod (multiple statements chained together)" $ do
        let program = do
              a <- input Public :: Comp (UInt 5)
              b <- input Public
              (q0, r0) <- performDivMod a b
              (q1, r1) <- performDivMod q0 b
              return [q0, r0, q1, r1]
        runAllExceptForTheOldOptimizer program [25, 3 :: GF181] [] [8, 1, 2, 2]

      it "performDivMod (before assertions)" $ do
        let program = do
              a <- input Public :: Comp (UInt 5)
              b <- input Public
              (q, r) <- performDivMod a b
              assert $ q `eq` r
        runAllExceptForTheOldOptimizer program [10, 4 :: GF181] [] []

      it "performDivMod (before reuse)" $ do
        let program = do
              a <- input Public :: Comp (UInt 5)
              b <- input Public
              (q, _) <- performDivMod a b
              reuse q
        runAllExceptForTheOldOptimizer program [10, 4 :: GF181] [] [2]

      it "performDivMod (after reuse)" $ do
        let program = do
              a <- reuse =<< input Public :: Comp (UInt 5)
              b <- input Public
              (q, r) <- performDivMod a b
              assert $ q `eq` r
        runAllExceptForTheOldOptimizer program [10, 4 :: GF181] [] []

      it "assertDivMod (dividend unknown)" $ do
        let program = do
              dividend <- freshVarUInt
              divisor <- input Public :: Comp (UInt 4)
              quotient <- input Public
              remainder <- input Private
              assertDivMod dividend divisor quotient remainder
              return dividend
        runAllExceptForTheOldOptimizer program [7, 2 :: GF181] [6] [20]

      it "assertDivMod (divisor & remainder unknown)" $ do
        let program = do
              dividend <- input Public :: Comp (UInt 4)
              divisor <- freshVarUInt
              quotient <- input Public
              remainder <- freshVarUInt
              assertDivMod dividend divisor quotient remainder
              return (divisor, remainder)
        runAllExceptForTheOldOptimizer program [7, 2 :: GF181] [] [3, 1]

      it "assertDivMod (quotient & remainder unknown)" $ do
        let program = do
              dividend <- input Public :: Comp (UInt 4)
              divisor <- input Public
              quotient <- freshVarUInt
              remainder <- freshVarUInt
              assertDivMod dividend divisor quotient remainder
              return (quotient, remainder)
        runAllExceptForTheOldOptimizer program [34, 6 :: GF181] [] [5, 4]

      it "eq" $ do
        let program = do
              x <- inputUInt @4 Public
              y <- inputUInt @4 Public
              return (x `eq` y)
        runAllExceptForTheOldOptimizer program [5, 6 :: GF181] [] [0]
        runAllExceptForTheOldOptimizer program [4, 4 :: GF181] [] [1]

      it "neq 1" $ do
        let program = do
              x <- inputUInt @4 Public
              y <- inputUInt @4 Public
              return (x `neq` y)
        runAllExceptForTheOldOptimizer program [5, 6 :: GF181] [] [1]
        runAllExceptForTheOldOptimizer program [4, 4 :: GF181] [] [0]

      it "neq 2" $ do
        let program = do
              x <- inputUInt @4 Public
              return (x `neq` 3)
        runAllExceptForTheOldOptimizer program [5 :: GF181] [] [1]
        runAllExceptForTheOldOptimizer program [3 :: GF181] [] [0]

      it "rotate" $ do
        let program = do
              x <- inputUInt @4 Public
              return [rotate x (-4), rotate x (-3), rotate x (-2), rotate x (-1), rotate x 0, rotate x 1, rotate x 2, rotate x 3, rotate x 4]

        runAll program [0 :: GF181] [] [0, 0, 0, 0, 0, 0, 0, 0, 0]
        runAll program [1 :: GF181] [] [1, 2, 4, 8, 1, 2, 4, 8, 1]
        runAll program [3 :: GF181] [] [3, 6, 12, 9, 3, 6, 12, 9, 3]
        runAll program [5 :: GF181] [] [5, 10, 5, 10, 5, 10, 5, 10, 5]

      it "shift" $ do
        let program = do
              x <- inputUInt @4 Public
              return [shift x (-4), shift x (-3), shift x (-2), shift x (-1), shift x 0, shift x 1, shift x 2, shift x 3, shift x 4]

        runAll program [0 :: GF181] [] [0, 0, 0, 0, 0, 0, 0, 0, 0]
        runAll program [1 :: GF181] [] [0, 0, 0, 0, 1, 2, 4, 8, 0]
        runAll program [3 :: GF181] [] [0, 0, 0, 1, 3, 6, 12, 8, 0]
        runAll program [5 :: GF181] [] [0, 0, 1, 2, 5, 10, 4, 8, 0]

      it "Bit test / literal" $ do
        -- 0011
        let program = do
              let c = 3 :: UInt 4
              return [c !!! (-1), c !!! 0, c !!! 1, c !!! 2, c !!! 3, c !!! 4]

        runAllExceptForTheOldOptimizer program [] [] [0, 1, 1, 0, 0, 1 :: GF181]

      it "Bit test / input var" $ do
        let program = do
              c <- input Private :: Comp (UInt 4)
              return [c !!! (-1), c !!! 0, c !!! 1, c !!! 2, c !!! 3, c !!! 4]
        runAllExceptForTheOldOptimizer program [] [3] [0, 1, 1, 0, 0, 1 :: GF181]
        runAllExceptForTheOldOptimizer program [] [5] [0, 1, 0, 1, 0, 1 :: GF181]

      it "Bit test / and 1" $ do
        let program = do
              x <- inputUInt @4 Public
              y <- inputUInt @4 Private
              return $ (x .&. y) !!! 0
        runAllExceptForTheOldOptimizer program [2] [3] [0 :: GF181]
        runAllExceptForTheOldOptimizer program [3] [5] [1 :: GF181]

      it "Bit test / and 2" $ do
        let program = do
              x <- inputUInt @4 Public
              y <- inputUInt @4 Private
              z <- inputUInt @4 Public
              return $ (x .&. y .&. z) !!! 0
        runAllExceptForTheOldOptimizer program [2, 4] [3] [0 :: GF181]
        runAllExceptForTheOldOptimizer program [3, 7] [5] [1 :: GF181]

      it "Bit test / or 1" $ do
        let program = do
              x <- inputUInt @4 Public
              y <- inputUInt @4 Private
              return $ (x .|. y) !!! 1
        runAllExceptForTheOldOptimizer program [2] [3] [1 :: GF181]
        runAllExceptForTheOldOptimizer program [3] [5] [1 :: GF181]
        runAllExceptForTheOldOptimizer program [5] [9] [0 :: GF181]

      it "Bit test / or 2" $ do
        let program = do
              x <- inputUInt @4 Public
              return $ (x .|. 3) !!! 2
        runAllExceptForTheOldOptimizer program [2] [] [0 :: GF181]
        runAllExceptForTheOldOptimizer program [3] [] [0 :: GF181]
        runAllExceptForTheOldOptimizer program [5] [] [1 :: GF181]

      it "Bit test / xor 1" $ do
        let program = do
              x <- inputUInt @4 Public
              y <- inputUInt @4 Private
              z <- inputUInt @4 Public
              w <- reuse $ x .^. y .^. z
              return [w !!! 0, w !!! 1, w !!! 2, w !!! 3]
        runAllExceptForTheOldOptimizer program [2, 4] [3] [1, 0, 1, 0 :: GF181]
        runAllExceptForTheOldOptimizer program [3, 7] [5] [1, 0, 0, 0 :: GF181]

      it "Bit test / BtoU" $ do
        let program = do
              x <- input Public
              let u = BtoU x :: UInt 4
              return [u !!! 0, u !!! 1, u !!! 2, u !!! 3]
        runAllExceptForTheOldOptimizer program [0] [] [0, 0, 0, 0 :: GF181]
        runAllExceptForTheOldOptimizer program [1] [] [1, 0, 0, 0 :: GF181]

      it "Bit test / rotate 1" $ do
        let program = do
              x <- inputUInt @4 Public
              return $ (x `rotate` 0) !!! 0
        runAllExceptForTheOldOptimizer program [2] [] [0 :: GF181]

      it "Bit test / rotate 2" $ do
        -- 0011 0100211003
        let program = do
              x <- inputUInt @4 Public
              y <- inputUInt @4 Public
              return
                [ (x `rotate` 0) !!! 0,
                  (x `rotate` 1) !!! 1,
                  (x `rotate` (-1)) !!! 0,
                  ((x .^. y) `rotate` 1) !!! 1
                ]
        runAllExceptForTheOldOptimizer program [2, 3] [] [0, 0, 1, 1 :: GF181]

    describe "Statements" $ do
      it "assert 1" $ do
        let program = do
              x <- inputField Public
              assert (x `eq` 3)
        runAll program [3 :: GF181] [] []

      it "Basic.summation2" $
        forAll (vector 4) $ \inp -> do
          let expectedOutput = []
          runAll Basic.summation2 (inp :: [GF181]) [] expectedOutput

      it "Basic.assertArraysEqual" $
        runAll Basic.assertArraysEqual [0, 2, 4, 8, 0, 2, 4, 8 :: GF181] [] []

      it "Basic.assertArraysEqual2" $
        runAll Basic.assertArraysEqual2 [0, 2, 4, 8, 0, 2, 4, 8 :: GF181] [] []

      it "Basic.array1D" $
        runAll (Basic.array1D 1) [2, 4 :: GF181] [] []

      it "Basic.array2D 1" $
        runAll (Basic.array2D 1 1) [2, 4 :: GF181] [] []

      it "Basic.array2D 2" $
        runAll (Basic.array2D 2 2) [0, 1, 2, 3, 0, 1, 4, 9 :: GF181] [] []

      it "Basic.toArray1" $
        runAll Basic.toArray1 [0 .. 7 :: GF181] [] []

      describe "AggCheck" $ do
        it "dim:1 sig:1" $
          runAggCheck 1 1 []
        it "dim:1 sig:10" $
          runAggCheck 1 10 []
        it "dim:10 sig:1" $
          runAggCheck 10 1 []
        it "dim:10 sig:10" $
          runAggCheck 10 10 []

      describe "LT12289" $ do
        it "dim:1 sig:1" $
          runLT12289 1 1 []
        it "dim:1 sig:10" $
          runLT12289 1 10 []
        it "dim:10 sig:1" $
          runLT12289 10 1 []
        it "dim:10 sig:10" $
          runLT12289 10 10 []

      describe "LenCheck" $ do
        it "dim:1 sig:1" $
          runLenCheck 1 1 []
        it "dim:1 sig:10" $
          runLenCheck 1 10 []
        it "dim:10 sig:1" $
          runLenCheck 10 1 []
        it "dim:10 sig:10" $
          runLenCheck 10 10 []

      describe "Poseidon" $ do
        it "[0]" $ do
          runAll (Poseidon.hash [0]) [] [] [969784935791658820122994814042437418105599415561111385 :: GF181]

    describe "Tests on the optimizer" $ do
      it "Multiplicative 0" $ do
        let program msg = do
              msg0 <- reuse msg
              msg1 <- reuse (msg0 + 1)
              reuse ((msg1 + 1) * (msg1 + 1))
        runAndCompare True (program 0 :: Comp Field) [0 :: N GF181] []
      it "Multiplicative 1" $ do
        let program = do
              let initState = (2, 3)
              let round' (a, b) = (a + b, a * a + b * 2)
              state1 <- reuse (round' initState) -- (5, 10)
              state2 <- reuse (round' state1) -- (15, 45)
              state3 <- reuse (round' state2) -- (60, 2025)
              return $ fst state3
        runAndCompare True (program :: Comp Field) [0 :: N GF181] []
  where
    runAggCheck :: Int -> Int -> [GF181] -> IO ()
    runAggCheck dimension numberOfSignatures outputs =
      let settings =
            AggSig.Settings
              { AggSig.enableAggChecking = True,
                AggSig.enableSizeChecking = False,
                AggSig.enableLengthChecking = False
              }
          param = AggSig.makeParam dimension numberOfSignatures 42 settings :: AggSig.Param GF181
       in runAll
            (AggSig.checkAgg param :: Comp ())
            (AggSig.genInputFromParam param)
            []
            outputs

    runLT12289 :: Int -> Int -> [GF181] -> IO ()
    runLT12289 dimension numberOfSignatures outputs =
      let settings =
            AggSig.Settings
              { AggSig.enableAggChecking = False,
                AggSig.enableSizeChecking = True,
                AggSig.enableLengthChecking = False
              }
          param = AggSig.makeParam dimension numberOfSignatures 42 settings :: AggSig.Param GF181
       in runAll
            (AggSig.checkSize param :: Comp ())
            (AggSig.genInputFromParam param)
            []
            outputs

    runLenCheck :: Int -> Int -> [GF181] -> IO ()
    runLenCheck dimension numberOfSignatures outputs =
      let settings =
            AggSig.Settings
              { AggSig.enableAggChecking = False,
                AggSig.enableSizeChecking = False,
                AggSig.enableLengthChecking = True
              }
          param = AggSig.makeParam dimension numberOfSignatures 42 settings :: AggSig.Param GF181
       in runAll
            (AggSig.checkLength param :: Comp ())
            (AggSig.genInputFromParam param)
            []
            outputs
-- program :: Comp ()
-- program = do
--   a <- input Public
--   assert $ a `neq` (0 :: UInt 3)
-- program :: Comp (UInt 4, UInt 4)
-- program = do
--   dividend <- input Public
--   divisor <- input Public
--   performDivMod dividend divisor

-- go :: (Encode t, Interpret t GF181) => Comp t -> [GF181] -> [GF181] -> Either (Error GF181) [GF181]
-- go prog rawPublicInputs rawPrivateInputs = do
--   elab <- left LangError (elaborate prog)
--   let inputs = Inputs.deserialize (compCounters (elabComp elab)) rawPublicInputs rawPrivateInputs
--   left InterpretError (Kinded.run elab inputs)
