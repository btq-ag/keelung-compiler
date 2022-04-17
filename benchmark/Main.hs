{-# LANGUAGE DataKinds #-}
module Main where

import qualified AggregateSignature.Program.Keelung as Keelung

import qualified AggregateSignature.Program.Snarkl as Snarkl
import AggregateSignature.Util
import qualified Benchmark.Keelung as Keelung
import qualified Benchmark.Snarkl as Snarkl
import Criterion.Main
import Keelung (GF181, Comp)
import qualified Snarkl

-- oldBenchmarks :: [Benchmark]
-- oldBenchmarks =
--   [ snarkl "keccak800" (Keccak.keccak1 22) (map fromIntegral Keccak.input_vals) 1,
--     snarkl "map-list" List.test_listN (90 : take 100 [0 ..]) 90,
--     snarkl "fixed-matrix600" (Matrix.test1 600) [0 .. 599] 754740000,
--     snarkl
--       "input-matrix70"
--       (Matrix.test2 70)
--       (Matrix.t2_m0 4900 ++ Matrix.t2_m1 4900)
--       2048215153250
--   ]

benchmarks :: Setup GF181 -> [Benchmark]
benchmarks setup =
  let snarkl = Snarkl.aggregateSignature setup
      keelung = Keelung.aggregateSignature setup
      input = genInputFromSetup setup
   in [ 
        bgroup
          "Elaboration"
          [ bench "Snarkl" $ nf Snarkl.benchElaborate snarkl,
            bench "Keelung" $ nf Keelung.benchElaborate' keelung
          ],
        bgroup
          "Interpretation"
          [ bench "Snarkl" $ nf (Snarkl.interpret snarkl) input,
            bench "Keelung" $ nf (Keelung.benchInterpret keelung) input
          ],
        bgroup
          "Type Erasure"
          [ bench "Snarkl" $ nf Snarkl.benchEraseType snarkl,
            bench "Keelung" $ nf Keelung.benchEraseType keelung
          ],
        bgroup
          "Compilation"
          [ bench "Snarkl (with Constant Propagation)" $ nf Snarkl.benchCompile snarkl,
            bench "Keelung (only Constant Propagation)" $ nf Keelung.benchPropogateConstant keelung,
            bench "Keelung (only Compilation)" $ nf Keelung.benchCompile keelung
          ],
        bgroup
          "Optimisation"
          [ bench "Snarkl" $ nf Snarkl.benchOptimise snarkl,
            bench "Keelung" $ nf Keelung.benchOptimise keelung,
            bench "Keelung (partial evaluation)" $ nf (Keelung.benchOptimiseWithInput keelung) input
          ]
      ]

compileAndOptimise :: Setup GF181 -> [Benchmark]
compileAndOptimise setup =
  let 
      -- snarkl = Snarkl.aggregateSignature setup
      keelung = Keelung.aggregateSignature setup
      -- input = genInputFromSetup setup
   in [ bgroup
          "Optimisation"
          [ 
            -- bench "Snarkl" $ nf Snarkl.benchOptimise snarkl,
            bench "Keelung" $ nf Keelung.benchOptimise keelung
            -- ,
            -- bench "Keelung (partial evaluation)" $ nf (Keelung.benchOptimiseWithInput keelung) input
          ]
      ]

keelungOnly :: Setup GF181 -> [Benchmark]
keelungOnly setup =
  let keelung = Keelung.aggregateSignature setup
   in [ 
        -- bench "Elaboration" $ nf Keelung.benchElaborate' keelung,
        -- bench "Rewriting" $ nf Keelung.benchRewrite' keelung,
        -- bench "Interpretation" $ nf (Keelung.benchInterpret keelung) input,
        -- bench "Type Erasure" $ nf Keelung.benchEraseType keelung,
        -- bench "Constant Propagation" $ nf Keelung.benchPropogateConstant keelung,
        bench "Compilation" $ nf Keelung.benchCompile keelung
        -- bench "Optimisation" $ nf Keelung.benchOptimise keelung,
        -- bench "Partial Evaluation" $ nf (Keelung.benchOptimiseWithInput keelung) input
      ]

complexityOfElaboration :: [Benchmark]
complexityOfElaboration =
      [ 
        bench "Elaboration" $ nf Keelung.benchElaborate' (makeKeelung 8 4),
        bench "Elaboration" $ nf Keelung.benchElaborate' (makeKeelung 16 4),
        bench "Elaboration" $ nf Keelung.benchElaborate' (makeKeelung 32 4),
        bench "Elaboration" $ nf Keelung.benchElaborate' (makeKeelung 64 4),
        bench "Elaboration" $ nf Keelung.benchElaborate' (makeKeelung 128 4),
        bench "Elaboration" $ nf Keelung.benchElaborate' (makeKeelung 256 4)
      ]

  where 
    makeKeelung :: Int -> Int -> Keelung.Comp GF181 ()
    makeKeelung dimension numberOfSignatures = 
      let settings =
            Settings
              { enableAggSigChecking = True,
                enableSigSizeChecking = True,
                enableSigLengthChecking = True
              }
          setup = makeSetup dimension numberOfSignatures 42 settings :: Setup GF181
          -- input = genInputFromSetup setup
      in  Keelung.aggregateSignature setup

run :: IO ()
run = do
  let dimension = 512
  let numberOfSignatures = 1
  let settings =
        Settings
          { enableAggSigChecking = True,
            enableSigSizeChecking = True,
            enableSigLengthChecking = True
          }
  let setup = makeSetup dimension numberOfSignatures 42 settings :: Setup GF181

  -- defaultMain complexityOfElaboration
  defaultMain (keelungOnly setup)
  -- defaultMain (benchmarks setup)
  -- defaultMain (compileAndOptimise setup)

main :: IO ()
main = run 
