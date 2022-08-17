{-# LANGUAGE DataKinds #-}

module Main where

import qualified AggregateSignature.Program as AggSig
import AggregateSignature.Util
import qualified Basic
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import qualified Data.Set as Set
import Keelung
import Keelung.Compiler
import Keelung.Compiler.Constraint (cadd, cmul)
import Keelung.Constraint.Polynomial (Poly)
import qualified Keelung.Constraint.Polynomial as Poly
import Keelung.Compiler.Interpret (InterpretError (..))
import qualified Keelung.Compiler.Optimize as Optimse
import qualified Keelung.Compiler as Compiler
import qualified Keelung.Compiler.Optimize.MinimizeConstraints as Optimize
import qualified Keelung.Compiler.Optimize.Monad as Optimize
import qualified Keelung.Syntax.Concrete as C
import Test.Hspec
import Control.Arrow (left)

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
        (AggSig.aggregateSignature param :: Comp GF181 (Val 'Unit GF181))
        (genInputFromParam param)

main :: IO ()
main = hspec $ do
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
      execute Basic.identity [42] `shouldBe` Right [42]
    it "Basic.summation" $
      execute Basic.summation [0, 2, 4, 8] `shouldBe` Right [14]
    it "Basic.summation2" $
      execute Basic.summation2 [0, 2, 4, 8] `shouldBe` Right []
    it "Basic.assertArraysEqual" $
      execute Basic.assertArraysEqual [0, 2, 4, 8, 0, 2, 4, 8] `shouldBe` Right []
    it "Basic.assertArraysEqual2" $
      execute Basic.assertArraysEqual2 [0, 2, 4, 8, 0, 2, 4, 8] `shouldBe` Right []

    it "Basic.array1D" $
      execute (Basic.array1D 1) [2, 4] `shouldBe` Right []

    it "Basic.array2D 1" $
      execute (Basic.array2D 1 1) [2, 4] `shouldBe` Right []

    it "Basic.array2D 2" $
      execute (Basic.array2D 2 2) [0, 1, 2, 3, 0, 1, 4, 9] `shouldBe` Right []

    it "Basic.toArray1" $
      execute Basic.toArray1 [0 .. 7] `shouldBe` Right []

    it "Basic.xorLists" $
      execute Basic.xorLists [] `shouldBe` Right [1]

    it "Basic.dupArray" $
      execute Basic.dupArray [1] `shouldBe` Right [1]

    it "Basic.returnArray2" $
      execute Basic.returnArray2 [2] `shouldBe` Right [2, 4]

  describe "Type Erasure" $ do
    describe "Boolean variables" $ do
      it "Basic.identity" $
        let erased = erase Basic.identity
            result = IntSet.toList . erasedBooleanVars <$> erased
         in result `shouldBe` Right []

      it "Basic.identityB" $
        let erased = erase Basic.identityB
            result = IntSet.toList . erasedBooleanVars <$> erased
         in result `shouldBe` Right [0]

      it "Basic.every" $
        let erased = erase Basic.every
            result = IntSet.toList . erasedBooleanVars <$> erased
         in result `shouldBe` Right [0 .. 7]

      -- it "Aggregate Signature" $
      --   let settings =
      --         Settings
      --           { enableAggChecking = True,
      --             enableSizeChecking = True,
      --             enableLengthChecking = True
      --           }
      --       setup = makeParam 1 1 42 settings :: Param GF181
      --       erased = erase (AggSig.aggregateSignature setup :: Comp GF181 (Val 'Unit GF181))
      --       result = IntSet.toList . erasedBooleanVars <$> erased
      --   in result `shouldBe` Right [3 .. 16]

  describe "Poly" $ do
    it "instance Eq 1" $ Poly.buildEither 42 [(1, 1)] `shouldBe` (Poly.buildEither 42 [(1, 1)] :: Either GF181 (Poly GF181))
    it "instance Eq 2" $ Poly.buildEither 42 [(1, 1)] `shouldBe` (Poly.buildEither (-42) [(1, -1)] :: Either GF181 (Poly GF181))

  describe "Constraint Generation" $ do
    it "assertToBe42" $
      let cs =
            ConstraintSystem
              { csConstraints =
                  Set.fromList $
                    cadd (-42) [(0, 1)],
                csBooleanInputVars = mempty,
                csVars = IntSet.fromList [0],
                csInputVars = IntSet.fromList [0],
                csOutputVars = IntSet.empty 
              }
       in optimize Basic.assertToBe42 `shouldBe` Right cs

  describe "Compilation" $ do
    it "identity (Num)" $
      execute Basic.identity [42] `shouldBe` Right [42]
    it "identity (Bool)" $
      execute Basic.identityB [1] `shouldBe` Right [1]
    it "identity (Bool)" $
      execute Basic.identityB [0] `shouldBe` Right [0]
    it "add3" $
      execute Basic.add3 [0] `shouldBe` Right [3]
    it "eq1 1" $
      execute Basic.eq1 [0] `shouldBe` Right [0]
    it "eq1 2" $
      execute Basic.eq1 [3] `shouldBe` Right [1]
    it "cond 1" $
      execute Basic.cond' [0] `shouldBe` Right [789]
    it "assert fail" $
      execute Basic.assert1 [0]
        `shouldBe` Left
          ( InterpretError $
              InterpretAssertionError
                (C.Eq (C.Var (C.NumVar 0)) (C.Val (C.Number 3)))
                (IntMap.fromList [(0, 0)])
          )
    it "assert success" $
      execute Basic.assert1 [3] `shouldBe` Right [3]

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
                  csInputVars = IntSet.fromList [0 .. 11],
                  csOutputVars = IntSet.empty 
                }
         in Optimse.optimize (cs :: ConstraintSystem GF181) `shouldNotBe` cs

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
                  csInputVars = IntSet.fromList [0 .. 3],
                  csOutputVars = IntSet.empty 
                }
            cs' =
              ConstraintSystem
                { csConstraints =
                    Set.fromList $
                      cadd 0 [(0, 1), (1, 1), (2, -1), (3, -1)],
                  csBooleanInputVars = mempty,
                  csVars = IntSet.fromList [0 .. 3],
                  csInputVars = IntSet.fromList [0 .. 3],
                  csOutputVars = IntSet.empty 
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
                  csInputVars = IntSet.fromList [0 .. 2],
                  csOutputVars = IntSet.empty 
                }
            cs' =
              ConstraintSystem
                { csConstraints =
                    Set.fromList (cmul [(0, -1), (1, -1)] [(2, 1)] (42, [])), -- (- $0 - $1) * $2 = 42
                  csBooleanInputVars = mempty,
                  csVars = IntSet.fromList [0 .. 2],
                  csInputVars = IntSet.fromList [0 .. 2],
                  csOutputVars = IntSet.empty 
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
                  csInputVars = IntSet.fromList [0 .. 2],
                  csOutputVars = IntSet.empty 
                }
            cs' =
              ConstraintSystem
                { csConstraints =
                    Set.fromList (cmul [(0, -1), (1, -1)] [(2, 1)] (42, [])), -- (- $0 - $1) * $2 = 42
                  csBooleanInputVars = mempty,
                  csVars = IntSet.fromList [0 .. 2],
                  csInputVars = IntSet.fromList [0 .. 2],
                  csOutputVars = IntSet.empty 
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
                  csInputVars = IntSet.fromList [0 .. 3],
                  csOutputVars = IntSet.empty 
                }
            cs' =
              ConstraintSystem
                { csConstraints =
                    Set.fromList $
                      cmul [(2, 1)] [(3, 1)] (0, [(0, -1), (1, -1)]), --- $2 * $3 = - $0 - $1
                  csBooleanInputVars = mempty,
                  csVars = IntSet.fromList [0 .. 3],
                  csInputVars = IntSet.fromList [0 .. 3],
                  csOutputVars = IntSet.empty 
                }
         in Optimse.optimize2 (cs :: ConstraintSystem GF181) `shouldBe` cs'

  describe "Compile" $ do
    it "Program that throws ElabError.IndexOutOfBoundsError" $ do
      let expected = left show (toR1CS <$> Compiler.compile Basic.outOfBound)
      actual <- left show <$> Keelung.compile Basic.outOfBound
      actual `shouldBe` expected

    it "Program that throws ElabError.EmptyArrayError" $ do
      let expected = left show (toR1CS <$> Compiler.compile Basic.emptyArray)
      actual <- left show <$> Keelung.compile Basic.emptyArray
      actual `shouldBe` expected

  describe "Interpret" $ do
    it "Basic.eq1 1" $ do
      let expected = left show (Compiler.interpret Basic.eq1 [0])
      actual <- left show <$> Keelung.interpret Basic.eq1 [0]
      actual `shouldBe` expected

    it "Basic.eq1 2" $ do
      let expected = left show (Compiler.interpret Basic.eq1 [3])
      actual <- left show <$> Keelung.interpret Basic.eq1 [3]
      actual `shouldBe` expected
