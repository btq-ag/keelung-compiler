{-# LANGUAGE DataKinds #-}

module Main where

import qualified AggregateSignature.Program as AggSig
import AggregateSignature.Util
import qualified Basic
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import qualified Data.Set as Set
import Keelung.Compiler
import Keelung.Compiler.Constraint (Constraint (..), cadd)
import qualified Keelung.Compiler.Constraint.Polynomial as Poly
import Keelung.Compiler.Interpret (InterpretError (..))
import qualified Keelung.Compiler.Optimise as Optimse
import qualified Keelung.Compiler.Optimise.MinimiseConstraints as Optimise
import qualified Keelung.Compiler.Optimise.Monad as Optimise
import Test.Hspec

runKeelungAggSig :: Int -> Int -> Either (Error GF181) (Maybe GF181)
runKeelungAggSig dimension numberOfSignatures =
  let settings =
        Settings
          { enableAggChecking = True,
            enableSizeChecking = True,
            enableLengthChecking = True
          }
      param = makeParam dimension numberOfSignatures 42 settings :: Param GF181
   in execute
        (AggSig.aggregateSignature param :: Comp GF181 ())
        (genInputFromParam param)

main :: IO ()
main = hspec $ do
  describe "Aggregate Signature" $ do
    it "dim:1 sig:1" $
      runKeelungAggSig 1 1 `shouldBe` Right Nothing
    it "dim:1 sig:10" $
      runKeelungAggSig 1 10 `shouldBe` Right Nothing
    it "dim:10 sig:1" $
      runKeelungAggSig 10 1 `shouldBe` Right Nothing
    it "dim:10 sig:10" $
      runKeelungAggSig 10 10 `shouldBe` Right Nothing

  describe "Type Erasure" $ do
    it "boolean variables in Aggregate Signature" $
      let settings =
            Settings
              { enableAggChecking = True,
                enableSizeChecking = True,
                enableLengthChecking = True
              }
          setup = makeParam 1 1 42 settings :: Param GF181
          erased = erase (AggSig.aggregateSignature setup :: Comp GF181 ())
          result = IntSet.toList . erasedBooleanVars <$> erased
       in result `shouldBe` Right [3 .. 16]

  describe "Compilation" $ do
    it "identity (Num)" $
      execute Basic.identity [42] `shouldBe` Right (Just 42)
    it "identity (Bool)" $
      execute Basic.identityB [1] `shouldBe` Right (Just 1)
    it "identity (Bool)" $
      execute Basic.identityB [0] `shouldBe` Right (Just 0)
    it "add3" $
      execute Basic.add3 [0] `shouldBe` Right (Just 3)
    it "eq1 1" $
      execute Basic.eq1 [0] `shouldBe` Right (Just 0)
    it "eq1 2" $
      execute Basic.eq1 [3] `shouldBe` Right (Just 1)
    it "cond 1" $
      execute Basic.cond [0] `shouldBe` Right (Just 789)
    it "assert fail" $
      execute Basic.assert1 [0]
        `shouldBe` Left
          ( InterpretError $
              InterpretAssertionError
                (Eq (Var (Variable 0)) (Val (Number 3)))
                (IntMap.fromList [(0, 0)])
          )
    it "assert success" $
      execute Basic.assert1 [3] `shouldBe` Right (Just 3)

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
        let constraint = cadd 0 [(0, 1), (1, -1)]
            links = IntMap.fromList [(1, 0)]
            sizes = IntMap.fromList [(0, 2)]
            run :: Optimise.OptiM GF181 a -> a
            run = Optimise.runOptiM' links sizes mempty
         in run (Optimise.substConstraint constraint)
              `shouldBe` Nothing

      it "should work 1" $
        let cs =
              ConstraintSystem
                { csConstraints =
                    Set.fromList
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
                  csBooleanInputVarConstraints = mempty,
                  csVars = IntSet.fromList [0 .. 17],
                  csInputVars = IntSet.fromList [0 .. 11],
                  csOutputVar = Nothing
                }
         in Optimse.optimise (cs :: ConstraintSystem GF181) `shouldNotBe` cs

    describe "Constraint merging" $ do
      it "CAdd & CAdd" $
        let cs =
              ConstraintSystem
                { csConstraints =
                    Set.fromList
                      [ cadd 0 [(0, 1), (1, 1), (4, 1)],
                        cadd 0 [(2, 1), (3, 1), (4, 1)]
                      ],
                  csBooleanInputVarConstraints = mempty,
                  csVars = IntSet.fromList [0 .. 4],
                  csInputVars = IntSet.fromList [0 .. 3],
                  csOutputVar = Nothing
                }
            cs' =
              ConstraintSystem
                { csConstraints =
                    Set.fromList
                      [ cadd 0 [(0, 1), (1, 1), (2, -1), (3, -1)]
                      ],
                  csBooleanInputVarConstraints = mempty,
                  csVars = IntSet.fromList [0 .. 3],
                  csInputVars = IntSet.fromList [0 .. 3],
                  csOutputVar = Nothing
                }
         in Optimse.optimise2 (cs :: ConstraintSystem GF181) `shouldBe` cs'

      it "CAdd & CMul 1" $
        let cs =
              ConstraintSystem
                { csConstraints =
                    Set.fromList
                      [ cadd 0 [(3, 1), (0, 1), (1, 1)], --- 0 = $3 + $0 + $1
                        CMul2 (Poly.build 0 [(3, 1)]) (Poly.build 0 [(2, 1)]) (Left 42) --- $3 * $2 = 42
                      ],
                  csBooleanInputVarConstraints = mempty,
                  csVars = IntSet.fromList [0 .. 3],
                  csInputVars = IntSet.fromList [0 .. 2],
                  csOutputVar = Nothing
                }
            cs' =
              ConstraintSystem
                { csConstraints =
                    Set.fromList
                      [ CMul2 (Poly.build 0 [(0, -1), (1, -1)]) (Poly.build 0 [(2, 1)]) (Left 42) --- (- $0 - $1) * $2 = 42
                      ],
                  csBooleanInputVarConstraints = mempty,
                  csVars = IntSet.fromList [0 .. 2],
                  csInputVars = IntSet.fromList [0 .. 2],
                  csOutputVar = Nothing
                }
         in Optimse.optimise2 (cs :: ConstraintSystem GF181) `shouldBe` cs'

      it "CAdd & CMul 2" $
        let cs =
              ConstraintSystem
                { csConstraints =
                    Set.fromList
                      [ cadd 0 [(3, 1), (0, 1), (1, 1)], --- 0 = $3 + $0 + $1
                        CMul2 (Poly.build 0 [(2, 1)]) (Poly.build 0 [(3, 1)]) (Left 42) --- $2 * $3 = 42
                      ],
                  csBooleanInputVarConstraints = mempty,
                  csVars = IntSet.fromList [0 .. 3],
                  csInputVars = IntSet.fromList [0 .. 2],
                  csOutputVar = Nothing
                }
            cs' =
              ConstraintSystem
                { csConstraints =
                    Set.fromList
                      [ CMul2 (Poly.build 0 [(2, 1)]) (Poly.build 0 [(0, -1), (1, -1)]) (Left 42) --- $2 * (- $0 - $1) = 42
                      ],
                  csBooleanInputVarConstraints = mempty,
                  csVars = IntSet.fromList [0 .. 2],
                  csInputVars = IntSet.fromList [0 .. 2],
                  csOutputVar = Nothing
                }
         in Optimse.optimise2 (cs :: ConstraintSystem GF181) `shouldBe` cs'

      it "CAdd & CMul 3" $
        let cs =
              ConstraintSystem
                { csConstraints =
                    Set.fromList
                      [ cadd 0 [(4, 1), (0, 1), (1, 1)], --- 0 = $4 + $0 + $1
                        CMul2 (Poly.build 0 [(2, 1)]) (Poly.build 0 [(3, 1)]) (Right (Poly.build 0 [(4, 1)])) --- $2 * $3 = $4
                      ],
                  csBooleanInputVarConstraints = mempty,
                  csVars = IntSet.fromList [0 .. 4],
                  csInputVars = IntSet.fromList [0 .. 3],
                  csOutputVar = Nothing
                }
            cs' =
              ConstraintSystem
                { csConstraints =
                    Set.fromList
                      [ CMul2 (Poly.build 0 [(2, 1)]) (Poly.build 0 [(3, 1)]) (Right (Poly.build 0 [(0, -1), (1, -1)])) --- $2 * $3 = - $0 - $1
                      ],
                  csBooleanInputVarConstraints = mempty,
                  csVars = IntSet.fromList [0 .. 3],
                  csInputVars = IntSet.fromList [0 .. 3],
                  csOutputVar = Nothing
                }
         in Optimse.optimise2 (cs :: ConstraintSystem GF181) `shouldBe` cs'

-- it "CAdd & CMul 2" $
--   let cs =
--         ConstraintSystem
--           { csConstraints =
--               Set.fromList
--                 [ cadd 0 [(4, 1), (0, 1), (1, 1)], --- 0 = $4 + $0 + $1
--                   CMul2 (Poly.build 0 [(4, 1)]) (Poly.build 0 [(2, 1)]) (Left 42) --- $4 * $2 = 42
--                 ],
--             csBooleanInputVarConstraints = mempty,
--             csVars = IntSet.fromList [0 .. 4],
--             csInputVars = IntSet.fromList [0 .. 3],
--             csOutputVar = Nothing
--           }
--       cs' =
--         ConstraintSystem
--           { csConstraints =
--               Set.fromList
--                 [ CMul2 (Poly.build 0 [(0, -1), (1, -1)]) (Poly.build 0 [(2, 1)]) (Left 42) --- (- $0 - $1) * $2 = 42
--                 ],
--             csBooleanInputVarConstraints = mempty,
--             csVars = IntSet.fromList [0 .. 2],
--             csInputVars = IntSet.fromList [0 .. 2],
--             csOutputVar = Nothing
--           }
--    in Optimse.optimise2 (cs :: ConstraintSystem GF181) `shouldBe` cs'
