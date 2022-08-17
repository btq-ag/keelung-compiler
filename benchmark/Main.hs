{-# LANGUAGE DataKinds #-}
module Main where

import qualified AggregateSignature.Program as AggSig
import AggregateSignature.Util
import Criterion.Main
import Keelung.Monad 
import Benchmark.Keelung
import Keelung

benchmarks :: Param GF181 -> [Benchmark]
benchmarks param =
  let keelung = AggSig.aggregateSignature param
      input = genInputFromParam param
   in [ 
        bgroup
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

compileAndOptimize :: Param GF181 -> [Benchmark]
compileAndOptimize setup =
  let 
      -- snarkl = Snarkl.aggregateSignature setup
      keelung = AggSig.aggregateSignature setup
      -- input = genInputFromParam setup
   in [ bgroup
          "Optimisation"
          [ 
            -- bench "Snarkl" $ nf Snarkl.benchOptimize snarkl,
            bench "Keelung" $ nf benchOptimize keelung
            -- ,
            -- bench "Keelung (partial evaluation)" $ nf (benchOptimizeWithInput keelung) input
          ]
      ]

keelungOnly :: Param GF181 -> [Benchmark]
keelungOnly setup =
  let keelung = AggSig.aggregateSignature setup
      input = genInputFromParam setup
   in [ 
        bench "Elaboration" $ nf benchElaborate keelung,
        bench "Rewriting" $ nf benchRewrite keelung,
        -- bench "Interpretation" $ nf (benchInterpret keelung) input,
        bench "Type Erasure" $ nf benchEraseType keelung,
        bench "Constant Propagation" $ nf benchPropogateConstant keelung,
        bench "Compilation" $ nf benchCompile keelung,
        bench "Optimisation I" $ nf benchOptimize keelung,
        bench "Optimisation II" $ nf benchOptimize2 keelung,
        bench "Partial Evaluation" $ nf (benchOptimizeWithInput keelung) input
      ]

complexityOfElaboration :: [Benchmark]
complexityOfElaboration =
      [ 
        bench "Elaboration" $ nf benchElaborate (makeKeelung 8 4),
        bench "Elaboration" $ nf benchElaborate (makeKeelung 16 4),
        bench "Elaboration" $ nf benchElaborate (makeKeelung 32 4),
        bench "Elaboration" $ nf benchElaborate (makeKeelung 64 4),
        bench "Elaboration" $ nf benchElaborate (makeKeelung 128 4),
        bench "Elaboration" $ nf benchElaborate (makeKeelung 256 4)
      ]

  where 
    makeKeelung :: Int -> Int -> Comp GF181 (Expr 'Unit GF181)
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
  -- defaultMain (compileAndOptimize setup)

main :: IO ()
main = run 
