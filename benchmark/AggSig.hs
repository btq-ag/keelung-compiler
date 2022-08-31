{-# LANGUAGE DataKinds #-}

module AggSig (benchmark) where

import qualified AggregateSignature.Program as AggSig
import AggregateSignature.Util
import Benchmark.Util
import Criterion.Main
import Keelung hiding (input)

_benchmarks1 :: Param GF181 -> [Benchmark]
_benchmarks1 param =
  let keelung = AggSig.aggregateSignature param
      input = genInputFromParam param
   in [ bgroup
          "Elaboration"
          [ bench "Keelung" $ nf benchElaborate keelung
          ],
        bgroup
          "Interpretation"
          [ bench "Keelung" $ nf (benchInterpret keelung) input
          ],
        bgroup
          "Type Erasure"
          [ bench "Keelung" $ nf benchEraseType keelung
          ],
        bgroup
          "Compilation"
          [ bench "Keelung (only Constant Propagation)" $ nf benchPropogateConstant keelung,
            bench "Keelung (only Compilation)" $ nf benchCompile keelung
          ],
        bgroup
          "Optimisation"
          [ bench "Keelung" $ nf benchOptimize keelung,
            bench "Keelung (partial evaluation)" $ nf (benchOptimizeWithInput keelung) input
          ]
      ]

benchmarks2 :: Param GF181 -> [Benchmark]
benchmarks2 setup =
  let keelung = AggSig.aggregateSignature setup
      input = genInputFromParam setup
   in [ bench "Elaboration" $ nf benchElaborate keelung,
        bench "Rewriting" $ nf benchRewrite keelung,
        -- bench "Interpretation" $ nf (benchInterpret keelung) input,
        bench "Type Erasure" $ nf benchEraseType keelung,
        bench "Constant Propagation" $ nf benchPropogateConstant keelung,
        bench "Compilation" $ nf benchCompile keelung,
        bench "Optimisation I" $ nf benchOptimize keelung,
        bench "Optimisation II" $ nf benchOptimize2 keelung,
        bench "Partial Evaluation" $ nf (benchOptimizeWithInput keelung) input
      ]

_complexityOfElaboration :: [Benchmark]
_complexityOfElaboration =
  [ bench "Elaboration" $ nf benchElaborate (makeKeelung 8 4),
    bench "Elaboration" $ nf benchElaborate (makeKeelung 16 4),
    bench "Elaboration" $ nf benchElaborate (makeKeelung 32 4),
    bench "Elaboration" $ nf benchElaborate (makeKeelung 64 4),
    bench "Elaboration" $ nf benchElaborate (makeKeelung 128 4),
    bench "Elaboration" $ nf benchElaborate (makeKeelung 256 4)
  ]
  where
    makeKeelung :: Int -> Int -> Comp (Val 'Unit)
    makeKeelung dimension numberOfSignatures =
      let settings =
            Settings
              { enableAggChecking = True,
                enableSizeChecking = True,
                enableLengthChecking = True
              }
          setup = makeParam dimension numberOfSignatures 42 settings :: Param GF181
       in AggSig.aggregateSignature setup

benchmark :: Benchmark
benchmark =
  let dimension = 128
      numberOfSignatures = 4
      settings =
        Settings
          { enableAggChecking = True,
            enableSizeChecking = True,
            enableLengthChecking = True
          }
      setup = makeParam dimension numberOfSignatures 42 settings :: Param GF181
   in -- defaultMain complexityOfElaboration

      bgroup
        "Aggregate Signature"
        (benchmarks2 setup)
