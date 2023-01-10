{-# LANGUAGE DataKinds #-}

module Merkle (run) where

import Criterion
import Keelung hiding (compileO0, run)
import Keelung.Compiler hiding (elaborate)
import qualified MerkleTree

run :: Benchmark
run =
  bgroup
    "MerkleTree"
    [ 
      compilation,
      optimizationOld
      -- optimizationNew
    ]
  where
    program :: Int -> Comp Field
    program = MerkleTree.getMerkleProof'

    compilation :: Benchmark
    compilation =
      bgroup
        "Compile"
        $ map (\i -> bench ("msg len " <> show i) $ nf (asGF181 . compileO0) $ program i) [1, 2, 4, 8]

    optimizationOld :: Benchmark
    optimizationOld =
      bgroup
        "Optimize (Old)"
        $ map (\i -> bench ("msg len " <> show i) $ nf (asGF181 . compileO1) $ program i) [1, 2]

-- optimizationNew :: Benchmark
-- optimizationNew =
--   bgroup
--     "Optimize (New)"
--     $ map (\i -> bench ("msg len " <> show i) $ nf (asGF181 . compileO1) $ program i) iteration
