module Main where

-- import qualified AggSig
import qualified Array
import Criterion.Main (defaultMain)

main :: IO ()
main =
  defaultMain
    [ -- AggSig.run
      Array.benchmark
    ]
