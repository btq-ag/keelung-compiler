module Array where

import qualified Array.Immutable as I
import qualified Array.Mutable as M
import Criterion
import Keelung (Comp, GF181, Val, elaborate)
import qualified Keelung.Compiler as Compiler
import qualified Keelung.Error as Language
import Keelung.Syntax.Typed (Elaborated)

benchmark :: Benchmark
benchmark = fromStringOptimization1
  where
    _elaboration :: Benchmark
    _elaboration =
      bgroup
        "Mutable vs Immutable Array Elaboration"
        [ bench "Mutable" $ nf elaborate' (M.fromString input),
          bench "Immutable" $ nf elaborate' (return $ I.fromString input)
        ]

    _compilation :: Benchmark
    _compilation =
      bgroup
        "Mutable vs Immutable Array Complilation"
        [ bench "M.fromString" $ nf compile (M.fromString input),
          bench "I.fromString" $ nf compile (return $ I.fromString input),
          bench "M.multiply" $ nf compile (M.multiplyT 8 2),
          bench "I.multiply" $ nf compile (I.multiplierT 8 2)
        ]

    _fromStringCompilation :: Benchmark
    _fromStringCompilation =
      bgroup
        "fromString: Complilation"
        [ bench "I.fromString 100" $ nf compileOnly (return $ I.fromString (concat $ replicate 10 "Helloworld")),
          bench "I.fromString 200" $ nf compileOnly (return $ I.fromString (concat $ replicate 20 "Helloworld")),
          bench "I.fromString 400" $ nf compileOnly (return $ I.fromString (concat $ replicate 40 "Helloworld")),
          bench "I.fromString 800" $ nf compileOnly (return $ I.fromString (concat $ replicate 80 "Helloworld"))
        ]

    fromStringOptimization1 :: Benchmark
    fromStringOptimization1 =
      bgroup
        "fromString: Optimization 1"
        [ bench "I.fromString 100" $ nf compile (return $ I.fromString (concat $ replicate 10 "Helloworld")),
          bench "I.fromString 200" $ nf compile (return $ I.fromString (concat $ replicate 20 "Helloworld")),
          bench "I.fromString 400" $ nf compile (return $ I.fromString (concat $ replicate 40 "Helloworld")),
          bench "I.fromString 800" $ nf compile (return $ I.fromString (concat $ replicate 80 "Helloworld"))
        ]

    input :: String
    input = concat $ replicate 100 "Hello world"

    elaborate' :: Comp (Val t) -> Either Language.ElabError Elaborated
    elaborate' = elaborate

    compile :: Comp (Val t) -> Either (Compiler.Error GF181) (Compiler.ConstraintSystem GF181)
    compile = Compiler.compile

    compileOnly :: Comp (Val t) -> Either (Compiler.Error GF181) (Compiler.ConstraintSystem GF181)
    compileOnly = Compiler.compileOnly
