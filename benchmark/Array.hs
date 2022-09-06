module Array where

import qualified Array.Immutable as I
import qualified Array.Mutable as M
import Criterion
import Keelung (Comp, GF181, Val, elaborate)
import Keelung.Compiler (compile)
import qualified Keelung.Compiler as Compiler
import qualified Keelung.Error as Language
import Keelung.Syntax.Typed (Elaborated)

benchmark :: Benchmark
benchmark = compilation
  where
    _elaboration :: Benchmark
    _elaboration =
      bgroup
        "Mutable vs Immutable Array Elaboration"
        [ bench "Mutable" $ nf elaborate' (M.fromString input),
          bench "Immutable" $ nf elaborate' (return $ I.fromString input)
        ]

    compilation :: Benchmark
    compilation =
      bgroup
        "Mutable vs Immutable Array Complilation"
        [ bench "M.fromString" $ nf compile' (M.fromString input),
          bench "I.fromString" $ nf compile' (return $ I.fromString input),
          bench "M.multiply" $ nf compile' (M.multiplyT 8 2),
          bench "I.multiply" $ nf compile' (I.multiplierT 8 2)
        ]

    input :: String
    input = concat $ replicate 100 "Hello world"

    elaborate' :: Comp (Val t) -> Either Language.ElabError Elaborated
    elaborate' = elaborate

    compile' :: Comp (Val t) -> Either (Compiler.Error GF181) (Compiler.ConstraintSystem GF181)
    compile' = compile
