-- | Specialized solver for addative constraints on binary fields.
--   Intended to be qualified as `Binary`
module Keelung.Solver.Binary (run) where

import Data.Bits qualified
import Data.Field.Galois (GaloisField)
import Data.IntMap (IntMap)
import Data.IntMap qualified as IntMap
import Data.IntSet (IntSet)
import Data.IntSet qualified as IntSet
import Data.Set (Set)
import Data.Set qualified as Set
import Keelung.Data.Polynomial (Poly)
import Keelung.Data.Polynomial qualified as Poly
import Keelung.Data.UnionFind.Boolean (UnionFind)
import Keelung.Data.UnionFind.Boolean qualified as UnionFind

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
--
--   TODO: return equivelent classes of variables instead of just polynomials
run :: (GaloisField n, Integral n) => Poly n -> Maybe (IntMap Bool, IntMap (IntSet, IntSet), Set IntSet)
run polynomial =
  let initState =
        Solving
          (toInteger (Poly.constant polynomial))
          (fmap toInteger (Poly.coeffs polynomial))
          UnionFind.empty
          mempty
          (Poly.varSize polynomial)
   in case solve initState of
        Solving {} -> error "[ panic ] Solver: Impossible"
        Failed -> Nothing
        Solved equations assignments eqClasses -> Just (assignments, eqClasses, equations)

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
      UnionFind
      (Set IntSet) -- equations with more than 2 variable
      Int -- count of unsolved  variables
  | Failed
  | Solved
      (Set IntSet) -- equations with more than 2 variable
      (IntMap Bool) -- assignments of variables
      (IntMap (IntSet, IntSet)) -- equivelent classes of variables

solve :: State -> State
solve Failed = Failed
solve (Solved equations assignments eqClasses) = Solved equations assignments eqClasses
solve (Solving _ _ state equations 0) = uncurry (Solved equations) (UnionFind.export state)
solve (Solving constant coeffs state equations remaining) =
  if IntMap.null coeffs
    then
      if constant == 0
        then uncurry (Solved equations) (UnionFind.export state)
        else Failed
    else
      let (constant', remainder) = shiftConstant constant
          (coeffs', vars) = shiftCoeffs coeffs
       in case IntSet.toList vars of
            [] ->
              if remainder
                then Failed -- 1 = 0
                else solve $ Solving constant' coeffs' state equations remaining
            [var] -> solve $ Solving constant' coeffs' (UnionFind.assign state var remainder) equations (remaining - 1) -- var == remainder
            [var1, var2] -> solve $ Solving constant' coeffs' (UnionFind.relate state var1 var2 (not remainder)) equations (remaining - 1) -- var1 + var2 == remainder
            _ -> solve $ Solving constant' coeffs' state (Set.insert vars equations) remaining