{-# LANGUAGE DataKinds #-}

module AggSig (run) where

import qualified AggregateSignature.Program as AggSig
import AggregateSignature.Util
import Benchmark.Util
import Criterion
import Keelung (GF181, Comp)

run :: Benchmark
run =
  bgroup
    "Aggregate Signature"
    [ elaboration,
      compilation,
      constantPropagation,
      optimization1
    ]
  where
    program :: Int -> Comp ()
    program n = 
        let dimension = 128
            numberOfSignatures = n 
            settings =
              Settings
                { enableAggChecking = True,
                  enableSizeChecking = True,
                  enableLengthChecking = True
                }
            setup = makeParam dimension numberOfSignatures 42 settings :: Param GF181
        in AggSig.aggregateSignature setup

    elaboration :: Benchmark
    elaboration =
      bgroup
        "Elaboration"
        $ map (\i -> bench (show i) $ nf elaborate $ program i) [1, 2, 4, 8]

    compilation :: Benchmark
    compilation =
      bgroup
        "Compilation"
        $ map (\i -> bench (show i) $ nf compile $ program i) [1, 2, 4, 8]

    constantPropagation :: Benchmark
    constantPropagation =
      bgroup
        "Constant Propagation"
        $ map (\i -> bench (show i) $ nf optimize0 $ program i) [1, 2, 4, 8]

    optimization1 :: Benchmark
    optimization1 =
      bgroup
        "Optimization I"
        $ map (\i -> bench (show i) $ nf optimize1 $ program i) [1, 2, 4, 8]
