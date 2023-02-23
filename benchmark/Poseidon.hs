{-# LANGUAGE DataKinds #-}

module Poseidon (run) where

import Control.Monad (replicateM)
import Criterion
import Data.Foldable (toList)
import Hash.Poseidon qualified as Poseidon
import Keelung hiding (compileO0, run)
import Keelung.Compiler
import Keelung.Compiler.Constraint (relocateConstraintSystem)

run :: Benchmark
run =
  bgroup
    "Poseidon"
    [ compilation,
      optimizationOld,
      optimizationNew
    ]
  where
    program :: Int -> Comp [Field]
    program n = replicateM n $ do
      xs <- inputList Public 1
      Poseidon.hash (toList xs)

    compilation :: Benchmark
    compilation =
      bgroup
        "Compile"
        $ map (\i -> bench ("iteration " <> show i) $ nf (asGF181 . compileO0) $ program i) [1, 2, 4, 8]

    optimizationOld :: Benchmark
    optimizationOld =
      bgroup
        "Optimize (Old)"
        $ map (\i -> bench ("iteration " <> show i) $ nf (asGF181 . compileO1) $ program i) [1, 2, 4, 8]

    optimizationNew :: Benchmark
    optimizationNew =
      bgroup
        "Optimize (New)"
        $ map (\i -> bench ("iteration " <> show i) $ nf (asGF181 . fmap relocateConstraintSystem . compileO1') $ program i) [1, 2, 4, 8]
