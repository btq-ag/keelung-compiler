{-# LANGUAGE DataKinds #-}
module Main where

import qualified AggregateSignature.Program as AggSig
import AggregateSignature.Util
import Criterion.Main
import Keelung (GF181, Comp)
import Benchmark.Keelung

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

benchmarks :: Param GF181 -> [Benchmark]
benchmarks param =
  let keelung = AggSig.aggregateSignature param
      input = genInputFromParam param
   in [ 
        bgroup
          "Elaboration"
          [ bench "Keelung" $ nf benchElaborate' keelung
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
        bench "Elaboration" $ nf benchElaborate' keelung,
        bench "Rewriting" $ nf benchRewrite' keelung,
        -- bench "Interpretation" $ nf (benchInterpret keelung) input,
        bench "Type Erasure" $ nf benchEraseType keelung,
        bench "Constant Propagation" $ nf benchPropogateConstant keelung,
        bench "Compilation" $ nf benchCompile keelung,
        bench "Optimisation" $ nf benchOptimise keelung,
        bench "Partial Evaluation" $ nf (benchOptimiseWithInput keelung) input
      ]

complexityOfElaboration :: [Benchmark]
complexityOfElaboration =
      [ 
        bench "Elaboration" $ nf benchElaborate' (makeKeelung 8 4),
        bench "Elaboration" $ nf benchElaborate' (makeKeelung 16 4),
        bench "Elaboration" $ nf benchElaborate' (makeKeelung 32 4),
        bench "Elaboration" $ nf benchElaborate' (makeKeelung 64 4),
        bench "Elaboration" $ nf benchElaborate' (makeKeelung 128 4),
        bench "Elaboration" $ nf benchElaborate' (makeKeelung 256 4)
      ]

  where 
    makeKeelung :: Int -> Int -> Comp GF181 ()
    makeKeelung dimension numberOfSignatures = 
      let settings =
            Settings
              { enableAggSigChecking = True,
                enableSigSizeChecking = True,
                enableSigLengthChecking = True
              }
          setup = makeParam dimension numberOfSignatures 42 settings :: Param GF181
          -- input = genInputFromParam setup
      in  AggSig.aggregateSignature setup

run :: IO ()
run = do
  let dimension = 512
  let numberOfSignatures = 8
  let settings =
        Settings
          { enableAggSigChecking = True,
            enableSigSizeChecking = True,
            enableSigLengthChecking = True
          }
  let setup = makeParam dimension numberOfSignatures 42 settings :: Param GF181

  -- defaultMain complexityOfElaboration
  defaultMain (keelungOnly setup)
  -- defaultMain (benchmarks setup)
  -- defaultMain (compileAndOptimise setup)

main :: IO ()
main = run 
