module Test.Solver.BinRep (tests, run) where

-- import Control.Monad
-- import Keelung hiding (compile)
import Test.Hspec

-- import Test.Interpreter.Util
-- import Test.QuickCheck

run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = describe "BinRep Detection" $ do
  return ()