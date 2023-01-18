module Main where

import qualified Poseidon
-- import qualified Merkle
import Criterion.Main
import Criterion.Types

main :: IO ()
main =
  defaultMainWith
    config
    [ 
      Poseidon.run
      -- ,
      -- Merkle.run
    ]
  where
    config :: Config
    config =
      defaultConfig
        { reportFile = Just "benchmark/Criterion reports/benchmark.html",
          csvFile = Just "benchmark/Criterion reports/benchmark.csv"
        }
