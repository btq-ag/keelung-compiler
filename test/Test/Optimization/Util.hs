module Test.Optimization.Util (debug, execute, shouldHaveSize) where

import Keelung hiding (compileO0)
import Keelung.Compiler qualified as Compiler
import Keelung.Compiler.ConstraintModule (ConstraintModule (..))
import Keelung.Compiler.Optimize qualified as Optimizer
import Keelung.Compiler.ConstraintSystem qualified as ConstraintSystem
import Test.HUnit (assertFailure)
import Test.Hspec
import Test.Interpreter.Util (gf181Info)
import qualified Keelung.Compiler.Linker as Linker

--------------------------------------------------------------------------------

-- | Returns the original and optimized constraint system
execute :: Encode t => Comp t -> IO (ConstraintModule (N GF181), ConstraintModule (N GF181))
execute program = do
  cm <- case Compiler.compileO0 gf181Info program of
    Left err -> assertFailure $ show err
    Right result -> return result

  case Optimizer.run cm of
    Left err -> assertFailure $ show err
    Right cm' -> do
      -- var counters should remain the same
      cmCounters cm `shouldBe` cmCounters cm'
      return (cm, cm')

shouldHaveSize :: ConstraintModule (N GF181) -> Int -> IO ()
shouldHaveSize cm expectedBeforeSize = do
  -- compare the number of constraints
  let actualBeforeSize = ConstraintSystem.numberOfConstraints (Linker.linkConstraintModule cm)
  actualBeforeSize `shouldBe` expectedBeforeSize

debug :: ConstraintModule (N GF181) -> IO ()
debug cm = do
  print cm
  print (Linker.linkConstraintModule cm)