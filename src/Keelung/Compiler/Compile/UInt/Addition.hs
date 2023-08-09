module Keelung.Compiler.Compile.UInt.Addition where

-- | Metavariables
--  * N – arity, number of operands
--  * F – maximum bit width of unsigned integers allowed in some underlying field,
--          for example, `F = 180` in `GF181`
--  * W - bit width of unsigned integers
data Model
  = -- | N ≤ 1
    Trivial
  | -- | 2 < N ≤ 2^⌊F/2⌋
    Standard
  | -- | 2^⌊F/2⌋ < N
    Extended