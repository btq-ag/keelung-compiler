module Main where

import AggregateSignature.Program.Keelung (aggregateSignature)
import AggregateSignature.Util
import Control.Monad
import Keelung

main :: IO ()
main = do
  forM_ [2 :: Int .. 7] $ \i -> run (2 ^ i) 4
  where
    settings :: Settings
    settings =
      Settings
        { enableAggSigChecking = True,
          enableSigSizeChecking = True,
          enableSigLengthChecking = True
        }

    run :: Int -> Int -> IO ()
    run dimension numberOfSignatures = do
      let setup = makeSetup dimension numberOfSignatures 42 settings :: Setup GF181

      let result = elaborate (aggregateSignature setup)
      case result of
        Left err -> print err
        Right elaborated -> do
          print (sizeOfExpr (elabExpr elaborated), length (elabNumAssignments elaborated), length (elabBoolAssignments elaborated), elabNumOfVars elaborated)
