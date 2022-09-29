{-# LANGUAGE DataKinds #-}

module Main where

import qualified AggregateSignature.Program as AggSig
import AggregateSignature.Util
import qualified Basic
import Control.Arrow (ArrowChoice (right), left)
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import qualified Data.Set as Set
import Keelung
import Keelung.Compiler
import qualified Keelung.Compiler as Compiler
import Keelung.Compiler.Constraint (cadd, cmul)
import Keelung.Compiler.Interpret (InterpretError (..))
import qualified Keelung.Compiler.Optimize as Optimse
import qualified Keelung.Compiler.Optimize.MinimizeConstraints as Optimize
import qualified Keelung.Compiler.Optimize.Monad as Optimize
import Keelung.Constraint.Polynomial (Poly)
import qualified Keelung.Constraint.Polynomial as Poly
import Keelung.Constraint.R1CS (R1CS)
import qualified Keelung.Syntax.Typed as C
import Test.Hspec
import qualified Test.Interpreter as Interpreter

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

    it "Basic.identity" $
      execute Basic.identity [42 :: GF181] `shouldBe` Right [42]
    it "Basic.summation" $
      execute Basic.summation [0, 2, 4, 8 :: GF181] `shouldBe` Right [14]
    it "Basic.summation2" $
      execute Basic.summation2 [0, 2, 4, 8 :: GF181] `shouldBe` Right []
    it "Basic.assertArraysEqual" $
      execute Basic.assertArraysEqual [0, 2, 4, 8, 0, 2, 4, 8 :: GF181] `shouldBe` Right []
    it "Basic.assertArraysEqual2" $
      execute Basic.assertArraysEqual2 [0, 2, 4, 8, 0, 2, 4, 8 :: GF181] `shouldBe` Right []

    it "Basic.array1D" $
      execute (Basic.array1D 1) [2, 4 :: GF181] `shouldBe` Right []

    it "Basic.array2D 1" $
      execute (Basic.array2D 1 1) [2, 4 :: GF181] `shouldBe` Right []

    it "Basic.array2D 2" $
      execute (Basic.array2D 2 2) [0, 1, 2, 3, 0, 1, 4, 9 :: GF181] `shouldBe` Right []

    it "Basic.toArray1" $
      execute Basic.toArray1 [0 .. 7 :: GF181] `shouldBe` Right []

    it "Basic.xorLists" $
      execute Basic.xorLists [] `shouldBe` Right [1 :: GF181]

    it "Basic.dupArray" $
      execute Basic.dupArray [1] `shouldBe` Right [1 :: GF181]

    it "Basic.returnArray2" $
      execute Basic.returnArray2 [2] `shouldBe` Right [2, 4 :: GF181]

  describe "Type Erasure" $ do
    describe "Boolean input variables" $ do
      it "Basic.identity" $
        let erased = erase Basic.identity :: Either (Error GF181) (TypeErased GF181)
            result = IntSet.toList . erasedBoolInputVars <$> erased
         in result `shouldBe` Right []

      it "Basic.identityB" $
        let erased = erase Basic.identityB :: Either (Error GF181) (TypeErased GF181)
            result = IntSet.toList . erasedBoolInputVars <$> erased
         in result `shouldBe` Right [0]

      it "Basic.every" $
        let erased = erase Basic.every :: Either (Error GF181) (TypeErased GF181)
            result = IntSet.toList . erasedBoolInputVars <$> erased
         in result `shouldBe` Right [0 .. 3]

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
                csBooleanInputVars = mempty,
                csVars = IntSet.fromList [0],
                csInputVarSize = 1,
                csOutputVarSize = 0
              }
       in Compiler.compile Basic.assertToBe42 `shouldBe` Right cs

  describe "Compilation" $ do
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
                (C.Eq (C.Var (C.NumInputVar 0)) (C.Val (C.Integer 3)))
                mempty
                [0]
          )
    it "assert success" $
      execute Basic.assert1 [3] `shouldBe` Right [3 :: GF181]

    it "toArrayM" $
      execute Basic.toArrayM1 [] `shouldBe` Right ([0] :: [GF181])

  -- NOTE:
  --    some variables are of "don't care"
  --    they get thrown away and won't be in the witness
  -- it "cond 2" $
  --   execute Basic.cond [3] `shouldBe` Right 12

  describe "Optimisation" $ do
    -- describe "Constant Propagation" $ do
    --   it "1 + 1" $
    --     erasedExpr <$> Basic.elab Basic.constant1 `shouldBe` Right 2

    describe "Constraint Set Reduction" $ do
      it "$0 = $1" $
        let constraint = head $ cadd 0 [(0, 1), (1, -1)]
            links = IntMap.fromList [(1, 0)]
            sizes = IntMap.fromList [(0, 2)]
            run :: Optimize.OptiM GF181 a -> a
            run = Optimize.runOptiM' links sizes mempty
         in run (Optimize.substConstraint constraint)
              `shouldBe` Nothing

      it "should work 1" $
        let cs =
              ConstraintSystem
                { csConstraints =
                    Set.fromList $
                      concat
                        [ cadd 0 [(0, 4972), (1, 10582), (16, -1)],
                          cadd 0 [(0, 10582), (1, 7317), (17, -1)],
                          cadd 0 [(2, 3853), (3, 4216), (15, -1)],
                          cadd 0 [(2, 8073), (3, 3853), (14, -1)],
                          cadd 0 [(4, 1), (8, 12289), (17, -1)],
                          cadd 0 [(5, 1), (9, 12289), (16, -1)],
                          cadd 0 [(6, 1), (10, 12289), (15, -1)],
                          cadd 0 [(7, 1), (11, 12289), (14, -1)],
                          cadd 0 [(4, 1), (6, 1), (13, -1)],
                          cadd 0 [(5, 1), (7, 1), (12, -1)],
                          cadd 10623 [(13, -1)],
                          cadd 11179 [(12, -1)]
                        ],
                  csBooleanInputVars = mempty,
                  csVars = IntSet.fromList [0 .. 17],
                  csInputVarSize = 12,
                  csOutputVarSize = 0
                }
         in Optimse.optimize1 (cs :: ConstraintSystem GF181) `shouldNotBe` cs

    describe "Constraint merging" $ do
      it "CAdd & CAdd" $
        let cs =
              ConstraintSystem
                { csConstraints =
                    Set.fromList $
                      cadd 0 [(0, 1), (1, 1), (4, 1)]
                        ++ cadd 0 [(2, 1), (3, 1), (4, 1)],
                  csBooleanInputVars = mempty,
                  csVars = IntSet.fromList [0 .. 4],
                  csInputVarSize = 4,
                  csOutputVarSize = 0
                }
            cs' =
              ConstraintSystem
                { csConstraints =
                    Set.fromList $
                      cadd 0 [(0, 1), (1, 1), (2, -1), (3, -1)],
                  csBooleanInputVars = mempty,
                  csVars = IntSet.fromList [0 .. 3],
                  csInputVarSize = 4,
                  csOutputVarSize = 0
                }
         in Optimse.optimize2 (cs :: ConstraintSystem GF181) `shouldBe` cs'

      it "CAdd & CMul 1" $
        let cs =
              ConstraintSystem
                { csConstraints =
                    Set.fromList $
                      cmul [(3, 1)] [(2, 1)] (42, []) --- $3 * $2 = 42
                        ++ cadd 0 [(3, 1), (0, 1), (1, 1)], --- 0 = $3 + $0 + $1
                  csBooleanInputVars = mempty,
                  csVars = IntSet.fromList [0 .. 3],
                  csInputVarSize = 3,
                  csOutputVarSize = 0
                }
            cs' =
              ConstraintSystem
                { csConstraints =
                    Set.fromList (cmul [(0, -1), (1, -1)] [(2, 1)] (42, [])), -- (- $0 - $1) * $2 = 42
                  csBooleanInputVars = mempty,
                  csVars = IntSet.fromList [0 .. 2],
                  csInputVarSize = 3,
                  csOutputVarSize = 0
                }
         in Optimse.optimize2 (cs :: ConstraintSystem GF181) `shouldBe` cs'

      it "CAdd & CMul 2" $
        let cs =
              ConstraintSystem
                { csConstraints =
                    Set.fromList $
                      cadd 0 [(3, 1), (0, 1), (1, 1)] --- 0 = $3 + $0 + $1
                        ++ cmul [(2, 1)] [(3, 1)] (42, []), --- $2 * $3 = 42
                  csBooleanInputVars = mempty,
                  csVars = IntSet.fromList [0 .. 3],
                  csInputVarSize = 3,
                  csOutputVarSize = 0
                }
            cs' =
              ConstraintSystem
                { csConstraints =
                    Set.fromList (cmul [(0, -1), (1, -1)] [(2, 1)] (42, [])), -- (- $0 - $1) * $2 = 42
                  csBooleanInputVars = mempty,
                  csVars = IntSet.fromList [0 .. 2],
                  csInputVarSize = 3,
                  csOutputVarSize = 0
                }
         in Optimse.optimize2 (cs :: ConstraintSystem GF181) `shouldBe` cs'

      it "CAdd & CMul 3" $
        let cs =
              ConstraintSystem
                { csConstraints =
                    Set.fromList $
                      cadd 0 [(4, 1), (0, 1), (1, 1)] --- 0 = $4 + $0 + $1
                        ++ cmul [(2, 1)] [(3, 1)] (0, [(4, 1)]), --- $2 * $3 = $4
                  csBooleanInputVars = mempty,
                  csVars = IntSet.fromList [0 .. 4],
                  csInputVarSize = 4,
                  csOutputVarSize = 0
                }
            cs' =
              ConstraintSystem
                { csConstraints =
                    Set.fromList $
                      cmul [(2, 1)] [(3, 1)] (0, [(0, -1), (1, -1)]), --- $2 * $3 = - $0 - $1
                  csBooleanInputVars = mempty,
                  csVars = IntSet.fromList [0 .. 3],
                  csInputVarSize = 4,
                  csOutputVarSize = 0
                }
         in Optimse.optimize2 (cs :: ConstraintSystem GF181) `shouldBe` cs'

  describe "Compile" $ do
    it "Program that throws ElabError.IndexOutOfBoundsError" $ do
      let expected = left show ((toR1CS :: ConstraintSystem GF181 -> R1CS GF181) <$> Compiler.optimize1 Basic.outOfBound)
      actual <- right (fmap fromInteger) . left show <$> Keelung.compile GF181 Basic.outOfBound
      actual `shouldBe` expected

    it "Program that throws ElabError.EmptyArrayError" $ do
      let expected = left show ((toR1CS :: ConstraintSystem GF181 -> R1CS GF181) <$> Compiler.optimize1 Basic.emptyArray)
      actual <- right (fmap fromInteger) . left show <$> Keelung.compile GF181 Basic.emptyArray
      actual `shouldBe` expected

    it "Program that compiles successfully" $ do
      let expected = left show ((toR1CS :: ConstraintSystem GF181 -> R1CS GF181) <$> Compiler.optimize1 Basic.identity)
      actual <- right (fmap fromInteger) . left show <$> Keelung.compile GF181 Basic.identity
      actual `shouldBe` expected

  describe "Interpret" $ do
    it "Program that throws ElabError.IndexOutOfBoundsError" $ do
      let expected = left show (Compiler.interpret Basic.outOfBound ([] :: [GF181]))
      actual <- left show <$> Keelung.interpret_ GF181 Basic.outOfBound []
      actual `shouldBe` expected

    it "Program that throws ElabError.EmptyArrayError" $ do
      let expected = left show (Compiler.interpret Basic.emptyArray ([] :: [GF181]))
      actual <- left show <$> Keelung.interpret_ GF181 Basic.emptyArray []
      actual `shouldBe` expected

    it "Basic.eq1 1" $ do
      let expected = left show (Compiler.interpret Basic.eq1 ([0] :: [GF181]))
      actual <- left show <$> Keelung.interpret_ GF181 Basic.eq1 [0]
      actual `shouldBe` expected

    it "Basic.eq1 2" $ do
      let expected = left show (Compiler.interpret Basic.eq1 ([3] :: [GF181]))
      actual <- left show <$> Keelung.interpret_ GF181 Basic.eq1 [3]
      actual `shouldBe` expected
