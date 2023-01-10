{-# LANGUAGE DataKinds #-}

module Poseidon (run) where

import Control.Monad (replicateM)
import Criterion
import qualified Hash.Poseidon as Poseidon
import Keelung hiding (run, compileO0)
import Keelung.Compiler hiding (elaborate)
import Data.Foldable (toList)

run :: Benchmark
run =
  bgroup
    "Poseidon"
    [ compilation,
      optimizationOld
    ]
  where
    program :: Int -> Comp [Field]
    program n = replicateM n $ do 
      xs <- inputs 4 
      Poseidon.hash (toList xs)

    compilation :: Benchmark
    compilation =
      bgroup
        "Compile"
        $ map (\i -> bench ("msg len " <> show i) $ nf (asGF181 . compileO0) $ program i) [1, 2, 4, 8]

    optimizationOld :: Benchmark
    optimizationOld =
      bgroup
        "Optimize (Old)"
        $ map (\i -> bench ("msg len " <> show i) $ nf (asGF181 . compileO1) $ program i) [1, 2, 4]

-- optimizationNew :: Benchmark
-- optimizationNew =
--   bgroup
--     "Optimize (New)"
--     $ map (\i -> bench ("msg len " <> show i) $ nf (asGF181 . compileO1) $ program i) iteration
