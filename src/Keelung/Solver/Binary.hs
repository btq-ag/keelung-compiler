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
import Keelung (Var)
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
run :: (GaloisField n, Integral n) => Poly n -> Maybe (IntMap Bool, IntMap (IntSet, IntSet), Set (Bool, IntSet))
run polynomial =
  let initStage =
        Solving
          (toInteger (Poly.constant polynomial))
          (fmap toInteger (Poly.coeffs polynomial))
          empty
   in case solve initStage of
        Solving {} -> error "[ panic ] Solver: Impossible"
        Failed -> Nothing
        Solved result -> Just result

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

data Stage
  = Solving
      Integer -- constant part of the polynomial
      Coefficients -- coefficients of the polynomial
      State
  | Failed
  | Solved
      ( IntMap Bool, -- assignments of variables
        IntMap (IntSet, IntSet), -- equivelent classes of variables
        Set (Bool, IntSet) -- relations with more than 2 variable (summed to 0 or 1)
      )

solve :: Stage -> Stage
solve Failed = Failed
solve (Solved result) = Solved result
solve (Solving constant coeffs state) =
  if IntMap.null coeffs
    then
      if constant == 0
        then Solved (export state)
        else Failed
    else
      let (constant', remainder) = shiftConstant constant
          (coeffs', vars) = shiftCoeffs coeffs
       in case IntSet.toList vars of
            [] ->
              if remainder
                then Failed -- 1 = 0
                else solve $ Solving constant' coeffs' state -- no-op
            [var] ->
              -- var == remainder
              solve $
                Solving constant' coeffs' (assign var remainder state)
            [var1, var2] ->
              -- var1 + var2 == remainder
              solve $
                Solving constant' coeffs' (relate var1 var2 (not remainder) state)
            _ -> solve $ solve $ Solving constant' coeffs' (addPolyB (PolyB vars remainder) state)

--------------------------------------------------------------------------------

data State
  = State
      UnionFind -- UnionFind: for unary relation (variable assignment) and binary relation (variable equivalence)
      (Set PolyB) -- other relations: for relations with more than 2 variables, summed to 0 or 1
  deriving (Eq, Show)

empty :: State
empty = State UnionFind.empty mempty

-- | Assign a variable to a value in the state
assign :: Var -> Bool -> State -> State
assign var val (State uf rels) = State (UnionFind.assign uf var val) (assignOnRelations var val rels)

-- | Assign a variable to a value in the relation pool
assignOnRelations :: Var -> Bool -> Set PolyB -> Set PolyB
assignOnRelations var val = Set.map $ \(PolyB vars parity) ->
  if var `IntSet.member` vars
    then PolyB (IntSet.delete var vars) (if val then not parity else parity)
    else PolyB vars parity

-- | Relate two variables in the state
relate :: Var -> Var -> Bool -> State -> State
relate var1 var2 sameSign (State uf rels) = State (UnionFind.relate uf var1 var2 sameSign) (relateOnRelations var1 var2 sameSign rels)

-- | Relate two variables in the relation pool
relateOnRelations :: Var -> Var -> Bool -> Set PolyB -> Set PolyB
relateOnRelations var1 var2 sameSign =
  if var1 == var2
    then id -- no-op
    else
      let (root, child) = (var1 `min` var2, var1 `max` var2)
       in Set.map $ \(PolyB vars parity) ->
            if child `IntSet.member` vars
              then
                if root `IntSet.member` vars
                  then
                    if sameSign
                      then -- child + root = 0
                        PolyB (IntSet.delete child $ IntSet.delete root vars) parity
                      else -- child + root = 1
                        PolyB (IntSet.delete child $ IntSet.delete root vars) (not parity)
                  else
                    if sameSign
                      then -- child = root
                        PolyB (IntSet.insert root $ IntSet.delete child vars) parity
                      else -- child = root + 1
                        PolyB (IntSet.insert root $ IntSet.delete child vars) (not parity)
              else PolyB vars parity -- no-op

addPolyB :: PolyB -> State -> State
addPolyB poly (State uf rels) =
  let PolyB vars parity = substPolyB uf poly
   in case IntSet.toList vars of
        [] -> State uf rels
        [var] -> assign var parity (State uf rels)
        [var1, var2] -> relate var1 var2 (not parity) (State uf rels)
        _ -> State uf $ Set.insert (PolyB vars parity) rels

-- Nothing -> IntSet.insert var equation

export ::
  State ->
  ( IntMap Bool, -- assignments of variables
    IntMap (IntSet, IntSet), -- equivelent classes of variables
    Set (Bool, IntSet) -- equations with more than 2 variable (summed to 0 or 1)
  )
export (State uf rels) =
  let (assignments, eqClasses) = UnionFind.export uf
   in (assignments, eqClasses, Set.map fromPolyB $ Set.filter ((> 2) . polyBSize) rels)

--------------------------------------------------------------------------------

-- | Binary field polynomial
data PolyB = PolyB IntSet Bool
  deriving (Eq, Ord, Show)

fromPolyB :: PolyB -> (Bool, IntSet)
fromPolyB (PolyB vars parity) = (parity, vars)

polyBSize :: PolyB -> Int
polyBSize (PolyB vars _) = IntSet.size vars

substPolyB :: UnionFind -> PolyB -> PolyB
substPolyB uf (PolyB e b) = IntSet.fold step (PolyB mempty b) e
  where
    step var (PolyB vars parity) =
      case UnionFind.lookup uf var of
        Nothing -> PolyB (IntSet.insert var vars) parity
        Just (UnionFind.Constant val) -> PolyB vars (if val then not parity else parity)
        Just UnionFind.Root ->
          if var `IntSet.member` vars
            then PolyB (IntSet.delete var vars) (not parity)
            else PolyB (IntSet.insert var vars) parity
        Just (UnionFind.ChildOf root sameSign) ->
          if root `IntSet.member` vars
            then PolyB (IntSet.delete root vars) (if sameSign then not parity else parity)
            else PolyB (IntSet.insert root vars) (if sameSign then parity else not parity)
