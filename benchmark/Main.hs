module Main where

import qualified AggSig
import qualified Array
import Criterion.Main
import Criterion.Types

main :: IO ()
main =
  defaultMainWith
    config
    [ AggSig.run,
      Array.fromString,
      Array.fullAdder,
      Array.multiplier
    ]
  where
    config :: Config
    config =
      defaultConfig
        { reportFile = Just "benchmark/Criterion reports/benchmark.html",
          csvFile = Just "benchmark/Criterion reports/benchmark.csv"
        }
