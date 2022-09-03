module Array where

import Criterion

import Keelung (Comp, GF181, Val, elaborate)
import Keelung.Compiler (compile)
import qualified Keelung.Compiler as Compiler
import qualified Keelung.Error as Language
import Keelung.Syntax.Typed (Elaborated)

import qualified Array.Immutable as I 
import qualified Array.Mutable as M 

benchmark :: Benchmark
benchmark =
  bgroup
    "Mutable vs Immutable array"
    [ bgroup
        "Elaboration"
        [ bench "Mutable" $ nf elaborate' (M.fromString input),
          bench "Immutable" $ nf elaborate' (return $ I.fromString input)
        ],
      bgroup
        "Complilation"
        [ bench "Mutable" $ nf compile' (M.fromString input),
          bench "Immutable" $ nf compile' (return $ I.fromString input)
        ]
    ]
    where
      input :: String
      input = concat $ replicate 100 "Hello world"

      elaborate' :: Comp (Val t) -> Either Language.ElabError Elaborated
      elaborate' = elaborate

      compile' :: Comp (Val t) -> Either (Compiler.Error GF181) (Compiler.ConstraintSystem GF181)
      compile' = compile
