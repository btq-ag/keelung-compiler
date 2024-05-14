{-# LANGUAGE TupleSections #-}

-- | Specialized solver for addative constraints on binary fields.
--   Intended to be qualified as `Binary`
module Keelung.Solver.Binary (run) where

import Data.Bits qualified
import Data.Field.Galois (GaloisField)
import Data.IntMap (IntMap)
import Data.IntMap qualified as IntMap
import Data.IntSet (IntSet)
import Data.IntSet qualified as IntSet
import Data.Maybe qualified as Maybe
import Data.Sequence (Seq)
import Data.Sequence qualified as Seq
import Keelung.Data.Polynomial (Poly)
import Keelung.Data.Polynomial qualified as Poly

-- | What this solver does:
--      Assume that all variables are Boolean:
--      1. break coefficients into sum of powers of 2
--      2. align coefficients of the same power of 2
--      3. solve the system of equations
--      4. return learned values and the rest of the equations
--
--   Example 1:
--      Given:  1 + 5A + B = 0
--          1. break it into: 1 + 4A + A + B = 0
--          2. align coefficients:
--              power   0   1   2
--              const   1   0   0
--                  A   1   0   1
--                  B   1   0   0
--          3. solve the system of equations:
--              1 + A + B = 0
--              A = 0
--          4. learned facts: A = 0, B = 1
--
--   Example 2:
--      Given:  A + B + 3C = 0
--          1. break it into: A + B + 2C + C = 0
--          2. align coefficients:
--              power   0   1   2
--              const   0   0   0
--                  A   1   0   0
--                  B   1   0   0
--                  C   1   0   1
--          3. solve the system of equations:
--              A + B + C = 0
--              C = 0
--          4. learned facts: A = B, C = 0
run :: (GaloisField n, Integral n) => Poly n -> Maybe (IntMap Bool, Seq (Poly n))
run polynomial =
  let initState =
        Solving
          (toInteger (Poly.constant polynomial))
          (fmap toInteger (Poly.coeffs polynomial))
          mempty
          mempty
          mempty
          (Poly.varSize polynomial)
   in case solve initState of
        Solving {} -> error "[ panic ] Solver: Impossible"
        Failed -> Nothing
        Solved assignments equations0 equations1 ->
          let toPoly c vars = case Poly.buildEither c (map (,1) (IntSet.toList vars)) of
                Left _ -> Nothing
                Right poly -> Just poly
              polynomials0 = Seq.fromList $ Maybe.mapMaybe (toPoly 0) equations0
              polynomials1 = Seq.fromList $ Maybe.mapMaybe (toPoly 1) equations1
           in Just (assignments, polynomials0 <> polynomials1)

-- | Coefficients are represented as a map from variable to Integer coefficient.
type Coefficients = IntMap Integer

-- | Return the set of variables with odd coefficients (i.e. LSB is 1)
--   and return the rest of the coefficients that remained non-zero after the LSB is shifted out.
shiftCoeffs :: Coefficients -> (Coefficients, IntSet)
shiftCoeffs =
  IntMap.foldrWithKey
    ( \var coeff (coeffs, oddVars) ->
        let shiftedCoeff = coeff `Data.Bits.shiftR` 1
            coeffs' = if shiftedCoeff == 0 then coeffs else IntMap.insert var shiftedCoeff coeffs
            oddVars' = if Data.Bits.testBit coeff 0 then IntSet.insert var oddVars else oddVars
         in (coeffs', oddVars')
    )
    (mempty, mempty)

-- | Like `shiftCoeffs`, but for a constant.
shiftConstant :: Integer -> (Integer, Bool)
shiftConstant constant =
  let (quotient, remainder) = constant `divMod` 2
   in (quotient, remainder == 1)

data State
  = Solving
      Integer -- constant part of the polynomial
      Coefficients -- coefficients of the polynomial
      (IntMap Bool) -- assignments of variables
      [IntSet] -- equations summed to 0
      [IntSet] -- equations summed to 1
      Int -- count of unsolved  variables
  | Failed
  | Solved
      (IntMap Bool) -- assignments of variables
      [IntSet] -- equations summed to 0
      [IntSet] -- equations summed to 1

solve :: State -> State
solve Failed = Failed
solve (Solved assignments equations0 equations1) = Solved assignments equations0 equations1
solve (Solving _ _ assignments equations0 equations1 0) = Solved assignments equations0 equations1
solve (Solving constant coeffs assignments equations0 equations1 remaining) =
  let (constant', remainder) = shiftConstant constant
      (coeffs', vars) = shiftCoeffs coeffs
   in case IntSet.toList vars of
        [] ->
          if remainder
            then Failed -- 1 = 0
            else solve $ Solving constant' coeffs' assignments equations0 equations1 remaining
        [var] -> solve $ Solving constant' coeffs' (IntMap.insert var remainder assignments) equations0 equations1 (remaining - 1) -- x == remainder
        _ ->
          if remainder
            then solve $ Solving constant' coeffs' assignments equations0 (vars : equations1) remaining
            else solve $ Solving constant' coeffs' assignments (vars : equations0) equations1 remaining
