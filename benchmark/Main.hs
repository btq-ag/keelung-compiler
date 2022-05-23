{-# LANGUAGE DataKinds #-}
module Main where

import qualified AggregateSignature.Program as AggSig
import AggregateSignature.Util
import Criterion.Main
import Keelung.Monad 
import Benchmark.Keelung
import Keelung.Field (GF181)

benchmarks :: Param GF181 -> [Benchmark]
benchmarks param =
  let keelung = AggSig.aggregateSignature param
      input = genInputFromParam param
   in [ 
        bgroup
          "Elaboration"
          [ bench "Keelung" $ nf benchElaborate_ keelung
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
          [ bench "Keelung" $ nf benchOptimise keelung,
            bench "Keelung (partial evaluation)" $ nf (benchOptimiseWithInput keelung) input
          ]
      ]

compileAndOptimise :: Param GF181 -> [Benchmark]
compileAndOptimise setup =
  let 
      -- snarkl = Snarkl.aggregateSignature setup
      keelung = AggSig.aggregateSignature setup
      -- input = genInputFromParam setup
   in [ bgroup
          "Optimisation"
          [ 
            -- bench "Snarkl" $ nf Snarkl.benchOptimise snarkl,
            bench "Keelung" $ nf benchOptimise keelung
            -- ,
            -- bench "Keelung (partial evaluation)" $ nf (benchOptimiseWithInput keelung) input
          ]
      ]

keelungOnly :: Param GF181 -> [Benchmark]
keelungOnly setup =
  let keelung = AggSig.aggregateSignature setup
      input = genInputFromParam setup
   in [ 
        bench "Elaboration" $ nf benchElaborate_ keelung,
        bench "Rewriting" $ nf benchRewrite' keelung,
        -- bench "Interpretation" $ nf (benchInterpret keelung) input,
        bench "Type Erasure" $ nf benchEraseType keelung,
        bench "Constant Propagation" $ nf benchPropogateConstant keelung,
        bench "Compilation" $ nf benchCompile keelung,
        bench "Optimisation I" $ nf benchOptimise keelung,
        bench "Optimisation II" $ nf benchOptimise2 keelung,
        bench "Partial Evaluation" $ nf (benchOptimiseWithInput keelung) input
      ]

complexityOfElaboration :: [Benchmark]
complexityOfElaboration =
      [ 
        bench "Elaboration" $ nf benchElaborate_ (makeKeelung 8 4),
        bench "Elaboration" $ nf benchElaborate_ (makeKeelung 16 4),
        bench "Elaboration" $ nf benchElaborate_ (makeKeelung 32 4),
        bench "Elaboration" $ nf benchElaborate_ (makeKeelung 64 4),
        bench "Elaboration" $ nf benchElaborate_ (makeKeelung 128 4),
        bench "Elaboration" $ nf benchElaborate_ (makeKeelung 256 4)
      ]

  where 
    makeKeelung :: Int -> Int -> Comp GF181 ()
    makeKeelung dimension numberOfSignatures = 
      let settings =
            Settings
              { enableAggChecking = True,
                enableSizeChecking = True,
                enableLengthChecking = True
              }
          setup = makeParam dimension numberOfSignatures 42 settings :: Param GF181
          -- input = genInputFromParam setup
      in  AggSig.aggregateSignature setup

run :: IO ()
run = do
  let dimension = 512
  let numberOfSignatures = 2
  let settings =
        Settings
          { enableAggChecking = True,
            enableSizeChecking = True,
            enableLengthChecking = True
          }
  let setup = makeParam dimension numberOfSignatures 42 settings :: Param GF181

  -- defaultMain complexityOfElaboration
  defaultMain (keelungOnly setup)
  -- defaultMain (benchmarks setup)
  -- defaultMain (compileAndOptimise setup)

main :: IO ()
main = run 
