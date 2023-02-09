{-# LANGUAGE DataKinds #-}

module Array (fromString, fullAdder, multiplier) where

import Array.Immutable qualified as I
import Criterion
import Keelung (Boolean, Comp, elaborateAndEncode)
import Keelung.Compiler hiding (elaborateAndEncode)

fromString :: Benchmark
fromString =
  bgroup
    "fromString"
    [ elaborationAndEncoding,
      compilation,
      constantPropagation,
      optimization1
    ]
  where
    program :: Int -> Comp [[Boolean]]
    program n = return $ I.fromString (concat $ replicate (n * 100) "Hello world")

    elaborationAndEncoding :: Benchmark
    elaborationAndEncoding =
      bgroup
        "Elaboration + Encoding"
        $ map (\i -> bench (show (i * 1000)) $ nf elaborateAndEncode $ program i) [1, 2, 4, 8]

    compilation :: Benchmark
    compilation =
      bgroup
        "Compilation"
        $ map (\i -> bench (show (i * 1000)) $ nf (asGF181 . compileOnly) $ program i) [1, 2, 4, 8]

    constantPropagation :: Benchmark
    constantPropagation =
      bgroup
        "Constant Propagation"
        $ map (\i -> bench (show (i * 1000)) $ nf (asGF181 . compileO0) $ program i) [1, 2, 4, 8]

    optimization1 :: Benchmark
    optimization1 =
      bgroup
        "Optimization I"
        $ map (\i -> bench (show (i * 1000)) $ nf (asGF181 . compileO1) $ program i) [1, 2, 4, 8]

fullAdder :: Benchmark
fullAdder =
  bgroup
    "fullAdder"
    [ elaborationAndEncoding,
      compilation,
      constantPropagation,
      optimization1
    ]
  where
    program :: Int -> Comp [Boolean]
    program n = I.fullAdderT (n * 10)

    elaborationAndEncoding :: Benchmark
    elaborationAndEncoding =
      bgroup
        "Elaboration + Encoding"
        $ map (\i -> bench (show (i * 10)) $ nf elaborateAndEncode $ program i) [1, 2, 4, 8]

    compilation :: Benchmark
    compilation =
      bgroup
        "Compilation"
        $ map (\i -> bench (show (i * 10)) $ nf (asGF181 . compileOnly) $ program i) [1, 2, 4, 8]

    constantPropagation :: Benchmark
    constantPropagation =
      bgroup
        "Constant Propagation"
        $ map (\i -> bench (show (i * 10)) $ nf (asGF181 . compileO0) $ program i) [1, 2, 4, 8]

    optimization1 :: Benchmark
    optimization1 =
      bgroup
        "Optimization I"
        $ map (\i -> bench (show (i * 10)) $ nf (asGF181 . compileO1) $ program i) [1, 2, 4, 8]

multiplier :: Benchmark
multiplier =
  bgroup
    "multiplier"
    [ elaborationAndEncoding,
      compilation,
      constantPropagation,
      optimization1
    ]
  where
    program :: Int -> Comp [Boolean]
    program n = I.multiplierT n 4

    elaborationAndEncoding :: Benchmark
    elaborationAndEncoding =
      bgroup
        "Elaboration + Encoding"
        $ map (\i -> bench (show i) $ nf elaborateAndEncode $ program i) [1, 2, 4, 8]

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

-- optimization3 :: Benchmark
-- optimization3 =
--   bgroup
--     "Optimization II"
--     $ map (\i -> bench (show (i * 1000)) $ nf optimize3 $ program i) [1, 2, 4, 8]
