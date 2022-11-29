{-# LANGUAGE DataKinds #-}

module Main where

import qualified AggregateSignature.Program as AggSig
import AggregateSignature.Util
import qualified Basic
-- import Control.Arrow (ArrowChoice (right), left)
import qualified Data.Set as Set
import Keelung
import Keelung.Compiler
import qualified Keelung.Compiler as Compiler
import Keelung.Compiler.Constraint (cadd)
import Keelung.Compiler.Interpret (InterpretError (..))
import Keelung.Constraint.Polynomial (Poly)
import qualified Keelung.Constraint.Polynomial as Poly
-- import Keelung.Constraint.R1CS (R1CS)
import qualified Keelung.Syntax.BinRep as BinRep
import qualified Keelung.Syntax.Typed as C
import Test.Hspec
import qualified Test.Interpreter as Interpreter
import qualified Test.Optimization as Optimization
import qualified Test.VarLayout as VarBookkeep
import Keelung.Syntax.Counters

runKeelungAggSig :: Int -> Int -> Either (Error GF181) [GF181]
runKeelungAggSig dimension numberOfSignatures =
  let settings =
        Settings
          { enableAggChecking = True,
            enableSizeChecking = True,
            enableLengthChecking = True
          }
      param = makeParam dimension numberOfSignatures 42 settings :: Param GF181
   in execute
        (AggSig.aggregateSignature param :: Comp ())
        (genInputFromParam param)

main :: IO ()
main = hspec $ do
  describe "Interpreter" Interpreter.tests

  describe "Optimization" Optimization.tests

  describe "Variable Bookkeeping" VarBookkeep.tests

  describe "Execution" $ do
    describe "Aggregate Signature" $ do
      it "dim:1 sig:1" $
        runKeelungAggSig 1 1 `shouldBe` Right []
      it "dim:1 sig:10" $
        runKeelungAggSig 1 10 `shouldBe` Right []
      it "dim:10 sig:1" $
        runKeelungAggSig 10 1 `shouldBe` Right []
      it "dim:10 sig:10" $
        runKeelungAggSig 10 10 `shouldBe` Right []
    it "identity (Num)" $
      execute Basic.identity [42] `shouldBe` Right [42 :: GF181]
    it "identity (Bool)" $
      execute Basic.identityB [1] `shouldBe` Right [1 :: GF181]
    it "identity (Bool)" $
      execute Basic.identityB [0] `shouldBe` Right [0 :: GF181]
    it "add3" $
      execute Basic.add3 [0] `shouldBe` Right [3 :: GF181]
    it "eq1 1" $
      execute Basic.eq1 [0] `shouldBe` Right [0 :: GF181]
    it "eq1 2" $
      execute Basic.eq1 [3] `shouldBe` Right [1 :: GF181]
    it "cond 1" $
      execute Basic.cond' [0] `shouldBe` Right [789 :: GF181]
    it "assert fail" $
      execute Basic.assert1 [0 :: GF181]
        `shouldBe` Left
          ( InterpretError $
              InterpretAssertionError
                (C.Boolean $ C.EqN (C.InputVarN 0) (C.ValN 3))
                [("$N0", 0)]
          )
    it "assert success" $
      execute Basic.assert1 [3] `shouldBe` Right [3 :: GF181]
    it "toArrayM" $
      execute Basic.toArrayM1 [] `shouldBe` Right ([0] :: [GF181])
    it "summation" $
      execute Basic.summation [0, 2, 4, 8 :: GF181] `shouldBe` Right [14]
    it "summation2" $
      execute Basic.summation2 [0, 2, 4, 8 :: GF181] `shouldBe` Right []
    it "assertArraysEqual" $
      execute Basic.assertArraysEqual [0, 2, 4, 8, 0, 2, 4, 8 :: GF181] `shouldBe` Right []
    it "assertArraysEqual2" $
      execute Basic.assertArraysEqual2 [0, 2, 4, 8, 0, 2, 4, 8 :: GF181] `shouldBe` Right []
    it "array1D" $
      execute (Basic.array1D 1) [2, 4 :: GF181] `shouldBe` Right []

    it "array2D 1" $
      execute (Basic.array2D 1 1) [2, 4 :: GF181] `shouldBe` Right []

    it "array2D 2" $
      execute (Basic.array2D 2 2) [0, 1, 2, 3, 0, 1, 4, 9 :: GF181] `shouldBe` Right []

    it "toArray1" $
      execute Basic.toArray1 [0 .. 7 :: GF181] `shouldBe` Right []

    it "xorLists" $
      execute Basic.xorLists [] `shouldBe` Right [1 :: GF181]

    it "dupArray" $
      execute Basic.dupArray [1] `shouldBe` Right [1 :: GF181]

    it "returnArray2" $
      execute Basic.returnArray2 [2] `shouldBe` Right [2, 4 :: GF181]

  describe "Poly" $ do
    it "instance Eq 1" $ Poly.buildEither 42 [(1, 1)] `shouldBe` (Poly.buildEither 42 [(1, 1)] :: Either GF181 (Poly GF181))
    it "instance Eq 2" $ Poly.buildEither 42 [(1, 1)] `shouldBe` (Poly.buildEither (-42) [(1, -1)] :: Either GF181 (Poly GF181))

  describe "Constraint Generation" $ do
    it "assertToBe42" $
      let cs =
            ConstraintSystem
              { csConstraints =
                  Set.fromList $
                    cadd (-42 :: GF181) [(0, 1)],
                csNumBinReps = mempty,
                csCustomBinReps = mempty,
                csCounters = addCount OfInput OfField 1 mempty
              }
       in Compiler.compileOnly Basic.assertToBe42 `shouldBe` Right cs

-- it "Bit value query 0" $
--   let cs =
--         ConstraintSystem
--           { csConstraints =
--               Set.fromList $
--                 concat
--                   [ -- value of outputs
--                     cadd (0 :: GF181) [(0, 1), (7, -1)],
--                     cadd 0 [(1, 1), (8, -1)],
--                     cadd 0 [(2, 1), (9, -1)],
--                     cadd (-1) [(3, 1)],
--                     cadd 1 [(4, -1)],
--                     cadd 0 [(5, 1)]
--                   ],
--             csVarCounters = makeVarCounters 181 6 1 0 0 [NumInput 0] [],
--             csNumBinReps = BinRep.fromList [BinRep.fromNumBinRep 181 (6, 7)],
--             csCustomBinReps = mempty
--           }
--    in Compiler.compileOnly Basic.bits0 `shouldBe` Right cs

-- it "Bit value query 1" $
--   let cs =
--         ConstraintSystem
--           { csConstraints =
--               Set.fromList $ -- value of outputs
--                 cmul [(364, 1)] [(3, 1)] (0 :: GF181, [(0, 1)]),
--             csVarCounters = makeVarCounters 181 1 2 0 0 [NumInput 0, NumInput 1] [],
--             csNumBinReps = BinRep.fromList [BinRep.fromNumBinRep 181 (1, 3), BinRep.fromNumBinRep 181 (2, 184)],
--             csCustomBinReps = mempty
--           }
--    in Compiler.compileOnly Basic.bits1 `shouldBe` Right cs

-- describe "Keelung `compile`" $ do
--   it "Program that throws ElabError.IndexOutOfBoundsError" $ do
--     let expected = left show ((toR1CS :: ConstraintSystem GF181 -> R1CS GF181) <$> Compiler.compile Basic.outOfBound)
--     actual <- right (fmap fromInteger) . left show <$> Keelung.compile GF181 Basic.outOfBound
--     actual `shouldBe` expected

--   it "Program that throws ElabError.EmptyArrayError" $ do
--     let expected = left show ((toR1CS :: ConstraintSystem GF181 -> R1CS GF181) <$> Compiler.compile Basic.emptyArray)
--     actual <- right (fmap fromInteger) . left show <$> Keelung.compile GF181 Basic.emptyArray
--     actual `shouldBe` expected

--   it "Program that compiles successfully" $ do
--     let expected = left show ((toR1CS :: ConstraintSystem GF181 -> R1CS GF181) <$> Compiler.compile Basic.identity)
--     actual <- right (fmap fromInteger) . left show <$> Keelung.compile GF181 Basic.identity
--     actual `shouldBe` expected

-- describe "Keelung `interpret`" $ do
--   it "Program that throws ElabError.IndexOutOfBoundsError" $ do
--     let expected = left show (Compiler.interpret Basic.outOfBound ([] :: [GF181]))
--     actual <- left show <$> Keelung.interpret_ GF181 Basic.outOfBound []
--     actual `shouldBe` expected

--   it "Program that throws ElabError.EmptyArrayError" $ do
--     let expected = left show (Compiler.interpret Basic.emptyArray ([] :: [GF181]))
--     actual <- left show <$> Keelung.interpret_ GF181 Basic.emptyArray []
--     actual `shouldBe` expected

--   it "Basic.eq1 1" $ do
--     let expected = left show (Compiler.interpret Basic.eq1 ([0] :: [GF181]))
--     actual <- left show <$> Keelung.interpret_ GF181 Basic.eq1 [0]
--     actual `shouldBe` expected

--   it "Basic.eq1 2" $ do
--     let expected = left show (Compiler.interpret Basic.eq1 ([3] :: [GF181]))
--     actual <- left show <$> Keelung.interpret_ GF181 Basic.eq1 [3]
--     actual `shouldBe` expected
