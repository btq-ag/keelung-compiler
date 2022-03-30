module Main where

import qualified AggregateSignature.Program.Keelung as Keelung
-- -- import qualified Benchmark.Keelung as Keelung
-- -- import qualified Benchmark.Snarkl as Snarkl

-- import Data.Data (Typeable)
-- import qualified Example.Snarkl.Keccak as Keccak
-- import qualified Example.Snarkl.List as List
-- import qualified Example.Snarkl.Matrix as Matrix

import qualified AggregateSignature.Program.Snarkl as Snarkl
import AggregateSignature.Util
import qualified Benchmark.Keelung as Keelung
import qualified Benchmark.Snarkl as Snarkl
import Criterion.Main
import Keelung (GF181)
import qualified Snarkl

-- import qualified Snarkl
-- import Snarkl.Common (GF181)
-- import Snarkl.Compile (SimplParam (..))

-- snarkl ::
--   (Typeable ty) =>
--   String ->
--   Snarkl.Comp ty GF181 ->
--   [GF181] ->
--   GF181 ->
--   Benchmark
-- snarkl name prog inputs result =
--   bgroup
--     name
--     [ bench (name ++ " interpret") $ nf Snarkl.interpret prog,
--       bench (name ++ " elaborate") $ nf Snarkl.benchElaborate prog,
--       bench (name ++ "-constraints") $ nfIO $ Snarkl.benchCompile prog
--       -- bench (name ++ "-simplify") $ nf Snarkl.simplify prog,
--       -- bench (name ++ "-r1cs") $ nf (Snarkl.serialize . Snarkl.compileToR1CS Simplify) prog,
--       -- bench (name ++ "-witgen") $ nf (Snarkl.witgen Simplify prog) inputs,
--       -- bench (name ++ "-full") $ nf (Snarkl.compareWithResult Simplify prog inputs) result
--     ]

-- keelung ::
--   (Typeable ty) =>
--   String ->
--   Keelung.Comp ty GF181 ->
--   [GF181] ->
--   GF181 ->
--   Benchmark
-- keelung name prog inputs result =
--   bgroup
--     name
--     [ bench (name ++ " interpret") $ nf Keelung.interpret prog,
--       bench (name ++ " elaborate") $ nf Keelung.benchElaborate prog,
--       bench (name ++ "-constraints") $ nfIO $ Keelung.benchCompile prog
--       -- bench (name ++ "-simplify") $ nf Keelung.simplify prog,
--       -- bench (name ++ "-r1cs") $ nf (Snarkl.serialize . Keelung.compileToR1CS Simplify) prog,
--       -- bench (name ++ "-witgen") $ nf (Keelung.witgen Simplify prog) inputs,
--       -- bench (name ++ "-full") $ nf (Keelung.compareWithResult Simplify prog inputs) result
--     ]

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
            bench "Keelung" $ nf Keelung.benchElaborate keelung
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
      input = genInputFromSetup setup
   in [ 
        bench "Elaboration" $ nf Keelung.benchElaborate keelung,
        bench "Interpretation" $ nf (Keelung.benchInterpret keelung) input,
        bench "Type Erasure" $ nf Keelung.benchEraseType keelung,
        bench "Constant Propagation" $ nf Keelung.benchPropogateConstant keelung,
        bench "Compilation" $ nf Keelung.benchCompile keelung,
        bench "Optimisation" $ nf Keelung.benchOptimise keelung,
        bench "Partial Evaluation" $ nf (Keelung.benchOptimiseWithInput keelung) input
      ]

run :: IO ()
run = do
  let dimension = 128
  let numberOfSignatures = 4
  let settings =
        Settings
          { enableAggSigChecking = True,
            enableSigSizeChecking = True,
            enableSigLengthChecking = True
          }
  let setup = makeSetup dimension numberOfSignatures 42 settings :: Setup GF181

  defaultMain (keelungOnly setup)
  -- defaultMain (benchmarks setup)
  -- defaultMain (compileAndOptimise setup)

main :: IO ()
main = run
