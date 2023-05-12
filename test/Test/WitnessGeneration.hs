module Test.WitnessGeneration (run, tests) where

-- import Data.Vector qualified as Vector

-- import Keelung.Data.VarGroup (VarGroup (..), VarGroups (VarGroups))

-- import Data.Foldable (Foldable(toList))
import Data.Vector qualified as Vec
import Keelung
import Keelung.Compiler (RelocatedConstraintSystem (..), generateWitness)
import Keelung.Compiler qualified as Compiler
import Test.Hspec
import Test.Interpreter.Util (gf181Info)

run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = do
  describe "Witness Generation" $ do
    it "`generateWitness` 1" $ do
      let program = do
            x <- inputField Public
            y <- inputField Private
            return [x, y]
      let actual = generateWitness gf181Info program [1 :: GF181] [2]
      let expected = do
            cs <- Compiler.compile gf181Info program
            return (csCounters cs, [1, 2], Vec.fromList [1, 2, 1, 2])
      actual `shouldBe` expected

    it "`generateWitness` 2" $ do
      let program = do
            x <- inputField Public
            y <- inputField Private
            return [x * y]
      let actual = generateWitness gf181Info program [2 :: GF181] [3]
      let expected = do
            cs <- Compiler.compile gf181Info program
            return (csCounters cs, [6], Vec.fromList [6, 2, 3])
      actual `shouldBe` expected

    it "`generateWitness` 3" $ do
      let program = do
            x1 <- inputField Public
            x2 <- inputField Public
            y1 <- inputField Private
            return [x1 * y1, y1, x2 * y1]
      let actual = generateWitness gf181Info program [2, 3 :: GF181] [4]
      let expected = do
            cs <- Compiler.compile gf181Info program
            return (csCounters cs, [8, 4, 12], Vec.fromList [8, 4, 12, 2, 3, 4])
      actual `shouldBe` expected

    it "`generateWitness` 4" $ do
      let program = do
            p <- input Private
            x <- inputField Public
            y <- inputField Private
            return $ cond p x y
      let actual = generateWitness gf181Info program [3 :: GF181] [1, 2]
      let expected = do
            cs <- Compiler.compile gf181Info program
            return (csCounters cs, [3], Vec.fromList [3, 3, 2, 1])
      actual `shouldBe` expected

    it "`generateWitness` 5" $ do
      let program = do
            list <- inputList Private 4 :: Comp [Field]
            return (head list)
      let actual = generateWitness gf181Info program [] [0, 1, 2, 3 :: GF181]
      let expected = do
            cs <- Compiler.compile gf181Info program
            return (csCounters cs, [0], Vec.fromList [0, 0, 1, 2, 3])
      actual `shouldBe` expected
