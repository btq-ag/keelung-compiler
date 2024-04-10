module Test.Solver (run, tests) where

import Data.Vector qualified as Vec
import Keelung
import Keelung.Compiler (ConstraintSystem (..), generateWitness)
import Keelung.Compiler qualified as Compiler
import Test.Hspec
import Test.Solver.BinRep qualified as Solver.BinRep

run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = do
  describe "Witness Solver" $ do
    Solver.BinRep.tests

    describe "`generateWitness" $ do
      it "`generateWitness` 1" $ do
        let program = do
              x <- inputField Public
              y <- inputField Private
              return [x, y]
        let actual = generateWitness gf181 program [1] [2]
        let expected = do
              cs <- Compiler.asGF181N $ Compiler.compile gf181 program >>= Compiler.link
              return (csCounters cs, Vec.fromList [1, 2], Vec.fromList [1, 2, 1, 2])
        actual `shouldBe` expected

      it "`generateWitness` 2" $ do
        let program = do
              x <- inputField Public
              y <- inputField Private
              return [x * y]
        let actual = generateWitness gf181 program [2] [3]
        let expected = do
              cs <- Compiler.asGF181N $ Compiler.compile gf181 program >>= Compiler.link
              return (csCounters cs, Vec.fromList [6], Vec.fromList [6, 2, 3])
        actual `shouldBe` expected

      it "`generateWitness` 3" $ do
        let program = do
              x1 <- inputField Public
              x2 <- inputField Public
              y1 <- inputField Private
              return [x1 * y1, y1, x2 * y1]
        let actual = generateWitness gf181 program [2, 3] [4]
        let expected = do
              cs <- Compiler.asGF181N $ Compiler.compile gf181 program >>= Compiler.link
              return (csCounters cs, Vec.fromList [8, 4, 12], Vec.fromList [8, 4, 12, 2, 3, 4])
        actual `shouldBe` expected

      it "`generateWitness` 4" $ do
        let program = do
              p <- input Private
              x <- inputField Public
              y <- inputField Private
              return $ cond p x y
        let actual = generateWitness gf181 program [3] [1, 2]
        let expected = do
              cs <- Compiler.asGF181N $ Compiler.compile gf181 program >>= Compiler.link
              return (csCounters cs, Vec.fromList [3], Vec.fromList [3, 3, 2, 1])
        actual `shouldBe` expected

      it "`generateWitness` 5" $ do
        let program = do
              list <- inputList Private 4 :: Comp [Field]
              return (head list)
        let actual = generateWitness gf181 program [] [0, 1, 2, 3]
        let expected = do
              cs <- Compiler.asGF181N $ Compiler.compile gf181 program >>= Compiler.link
              return (csCounters cs, Vec.fromList [0], Vec.fromList [0, 0, 1, 2, 3])
        actual `shouldBe` expected
