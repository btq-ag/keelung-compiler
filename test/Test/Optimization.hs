module Test.Optimization (tests) where

import qualified Basic
import qualified Data.IntMap as IntMap
import qualified Data.Set as Set
import Keelung (Comp, Encode, GF181)
import Keelung.Compiler (asGF181, toR1CS)
import qualified Keelung.Compiler as Compiler
import Keelung.Compiler.Constraint
import Keelung.Compiler.Error (Error)
import Keelung.Compiler.Optimize
import qualified Keelung.Compiler.Optimize.MinimizeConstraints as O1
import Keelung.Compiler.Optimize.Monad
import Keelung.Constraint.R1CS (toR1Cs)
import Test.Hspec

tests :: SpecWith ()
tests = do
  describe "Constraint set reduction (O1)" $ do
    it "$0 = $1" $
      let constraint = head $ cadd 0 [(0, 1), (1, -1)]
          links = IntMap.fromList [(1, 0)]
          sizes = IntMap.fromList [(0, 2)]
          go :: OptiM GF181 a -> a
          go = runOptiM' links sizes mempty
       in go (O1.substConstraint constraint)
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
                csNumBinReps = mempty,
                csCustomBinReps = mempty,
                csCounters = mempty
              }
       in optimize1 (cs :: ConstraintSystem GF181) `shouldNotBe` cs

  describe "Constraint merging (O2)" $ do
    it "CAdd & CAdd" $
      let cs =
            ConstraintSystem
              { csConstraints =
                  Set.fromList $
                    cadd 0 [(0, 1), (1, 1), (4, 1)]
                      ++ cadd 0 [(2, 1), (3, 1), (4, 1)],
                csNumBinReps = mempty,
                csCustomBinReps = mempty,
                csCounters = mempty
              }
          cs' =
            ConstraintSystem
              { csConstraints =
                  Set.fromList $
                    cadd 0 [(0, -1), (1, -1), (2, 1), (3, 1)],
                csNumBinReps = mempty,
                csCustomBinReps = mempty,
                csCounters = mempty
              }
       in optimize2 (cs :: ConstraintSystem GF181) `shouldBe` cs'

    it "CAdd & CMul 1" $
      let cs =
            ConstraintSystem
              { csConstraints =
                  Set.fromList $
                    cmul [(3, 1)] [(2, 1)] (42, []) --- $3 * $2 = 42
                      ++ cadd 0 [(3, 1), (0, 1), (1, 1)], --- 0 = $3 + $0 + $1
                csNumBinReps = mempty,
                csCustomBinReps = mempty,
                csCounters = mempty
              }
          cs' =
            ConstraintSystem
              { csConstraints =
                  Set.fromList (cmul [(0, -1), (1, -1)] [(2, 1)] (42, [])), -- (- $0 - $1) * $2 = 42
                csNumBinReps = mempty,
                csCustomBinReps = mempty,
                csCounters = mempty
              }
       in optimize2 (cs :: ConstraintSystem GF181) `shouldBe` cs'

    it "CAdd & CMul 2" $
      let cs =
            ConstraintSystem
              { csConstraints =
                  Set.fromList $
                    cadd 0 [(3, 1), (0, 1), (1, 1)] --- 0 = $3 + $0 + $1
                      ++ cmul [(2, 1)] [(3, 1)] (42, []), --- $2 * $3 = 42
                csNumBinReps = mempty,
                csCustomBinReps = mempty,
                csCounters = mempty
              }
          cs' =
            ConstraintSystem
              { csConstraints =
                  Set.fromList (cmul [(2, 1)] [(0, -1), (1, -1)] (42, [])), -- (- $0 - $1) * $2 = 42
                csNumBinReps = mempty,
                csCustomBinReps = mempty,
                csCounters = mempty
              }
       in optimize2 (cs :: ConstraintSystem GF181) `shouldBe` cs'

    it "CAdd & CMul 3" $
      let cs =
            ConstraintSystem
              { csConstraints =
                  Set.fromList $
                    cadd 0 [(4, 1), (0, 1), (1, 1)] --- 0 = $4 + $0 + $1
                      ++ cmul [(2, 1)] [(3, 1)] (0, [(4, 1)]), --- $2 * $3 = $4
                csNumBinReps = mempty,
                csCustomBinReps = mempty,
                csCounters = mempty
              }
          cs' =
            ConstraintSystem
              { csConstraints =
                  Set.fromList $
                    cmul [(2, 1)] [(3, 1)] (0, [(0, -1), (1, -1)]), --- $2 * $3 = - $0 - $1
                csNumBinReps = mempty,
                csCustomBinReps = mempty,
                csCounters = mempty
              }
       in optimize2 (cs :: ConstraintSystem GF181) `shouldBe` cs'

  describe "Constraint number counting" $ do
    describe "AND Chaining" $ do
      it "1 variable" $ count (Basic.chainingAND 1) `shouldBe` Right (1 + 1)
      it "2 variables" $ count (Basic.chainingAND 2) `shouldBe` Right (2 + 1)
      it "3 variables" $ count (Basic.chainingAND 3) `shouldBe` Right (3 + 2)
      it "4 variables" $ count (Basic.chainingAND 4) `shouldBe` Right (4 + 2)
      it "5 variables" $ count (Basic.chainingAND 5) `shouldBe` Right (5 + 2)

    describe "OR Chaining" $ do
      it "1 variable" $ count (Basic.chainingOR 1) `shouldBe` Right 2
      it "2 variables" $ count (Basic.chainingOR 2) `shouldBe` Right 3
      it "3 variables" $ count (Basic.chainingOR 3) `shouldBe` Right (3 + 3)
      it "4 variables" $ count (Basic.chainingOR 4) `shouldBe` Right (4 + 3)
      it "5 variables" $ count (Basic.chainingOR 5) `shouldBe` Right (5 + 3)
      it "6 variables" $ count (Basic.chainingOR 6) `shouldBe` Right (6 + 3)
      it "7 variables" $ count (Basic.chainingOR 7) `shouldBe` Right (7 + 3)
  where
    count :: Encode t => Comp t -> Either (Error GF181) Int
    count program = do
      cs <- asGF181 (Compiler.compile program)
      return $ length $ toR1Cs $ toR1CS cs