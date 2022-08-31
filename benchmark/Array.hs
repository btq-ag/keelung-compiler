module Array where

import Criterion
import Keelung (Comp, GF181, Val, elaborate)
import Keelung.Compiler (optimize)
import qualified Keelung.Compiler as Compiler
import qualified Keelung.Error as Language
import Keelung.Syntax.Typed (Elaborated)
-- import qualified Lib.W8

benchmark :: Benchmark
benchmark =
  bgroup
    "Mutable vs Immutable array"
    [ 
      -- bgroup
      --   "Elaboration"
      --   [ bench "Mutable" $ nf elaborate' (Lib.W8.fromString input),
      --     bench "Immutable" $ nf elaborate' (return $ Lib.W8.fromString' input)
      --   ],
      -- bgroup
      --   "Complilation"
      --   [ bench "Mutable" $ nf compile' (Lib.W8.fromString input),
      --     bench "Immutable" $ nf compile' (return $ Lib.W8.fromString' input)
      --   ]
    ]
  -- where
  --   input :: String
  --   input = concat $ replicate 100 "Hello world"

  --   elaborate' :: Comp (Val t GF181) -> Either Language.ElabError Elaborated
  --   elaborate' = elaborate

  --   compile' :: Comp (Val t GF181) -> Either (Compiler.Error GF181) (Compiler.ConstraintSystem GF181)
  --   compile' = optimize