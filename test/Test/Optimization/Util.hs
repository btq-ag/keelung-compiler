module Test.Optimization.Util (debug, execute, shouldHaveSize) where

import Keelung hiding (compileO0)
import Keelung.Compiler qualified as Compiler
import Keelung.Compiler.ConstraintSystem (ConstraintSystem (..), relocateConstraintSystem)
import Keelung.Compiler.Optimize qualified as Optimizer
import Keelung.Compiler.Relocated qualified as Relocated
import Test.HUnit (assertFailure)
import Test.Hspec
import Test.Interpreter.Util (gf181Info)

--------------------------------------------------------------------------------

-- | Returns the original and optimized constraint system
execute :: Encode t => Comp t -> IO (ConstraintSystem (N GF181), ConstraintSystem (N GF181))
execute program = do
  cs <- case Compiler.compileO0 gf181Info program of
    Left err -> assertFailure $ show err
    Right result -> return result

  case Optimizer.run cs of
    Left err -> assertFailure $ show err
    Right cs' -> do
      -- var counters should remain the same
      csCounters cs `shouldBe` csCounters cs'
      return (cs, cs')

shouldHaveSize :: ConstraintSystem (N GF181) -> Int -> IO ()
shouldHaveSize cs expectedBeforeSize = do
  -- compare the number of constraints
  let actualBeforeSize = Relocated.numberOfConstraints (relocateConstraintSystem cs)
  actualBeforeSize `shouldBe` expectedBeforeSize

debug :: ConstraintSystem (N GF181) -> IO ()
debug cs = do
  print cs
  print (relocateConstraintSystem cs)