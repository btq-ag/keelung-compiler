{-# LANGUAGE DataKinds #-}

module AggSig (run) where

import qualified AggregateSignature.Program as AggSig
import AggregateSignature.Util
import Criterion
import Keelung (Comp, GF181, elaborate)
import Keelung.Compiler hiding (elaborate)

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
        $ map (\i -> bench (show i) $ nf (asGF181 . compileOnly) $ program i) [1, 2, 4, 8]

    constantPropagation :: Benchmark
    constantPropagation =
      bgroup
        "Constant Propagation"
        $ map (\i -> bench (show i) $ nf (asGF181 . compileO0) $ program i) [1, 2, 4, 8]

    optimization1 :: Benchmark
    optimization1 =
      bgroup
        "Optimization I"
        $ map (\i -> bench (show i) $ nf (asGF181 . compileO1) $ program i) [1, 2, 4, 8]
