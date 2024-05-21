-- | Specialized solver for addative constraints on binary fields.
--   Intended to be qualified as `Binary`
module Keelung.Solver.Binary (run, Result (..)) where

import Data.Bits qualified
import Data.Either qualified as Either
import Data.Field.Galois (GaloisField)
import Data.IntMap (IntMap)
import Data.IntMap qualified as IntMap
import Data.IntSet (IntSet)
import Data.IntSet qualified as IntSet
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
run :: (GaloisField n, Integral n) => Poly n -> Maybe Result
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

data Result = Result
  { resultAssigmnet :: IntMap Bool,
    resultEquivClass :: IntMap (IntSet, IntSet),
    resultRelations :: [(Bool, IntSet)]
  }
  deriving (Eq, Show)

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
  | Solved Result

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
              -- trace ("\n$" <> show var <> " := " <> show remainder) $
              --   traceShow state $
              --     traceShow (assign var remainder state) $
              -- var == remainder
              solve $
                Solving constant' coeffs' (assign var remainder state)
            [var1, var2] ->
              -- trace ("\n$" <> show var1 <> " == " <> (if not remainder then "" else "-") <> "$" <> show var2) $
              --   traceShow state $
              --     traceShow (relate var1 var2 (not remainder) state) $
              -- var1 + var2 == remainder
              solve $
                Solving constant' coeffs' (relate var1 var2 (not remainder) state)
            _ ->
              -- trace ("\n+ " <> show (PolyB vars remainder)) $
              --   traceShow state $
              --   traceShow (insert (PolyB vars remainder) state) $
              solve $
                Solving constant' coeffs' (insert (PolyB vars remainder) state)

--------------------------------------------------------------------------------

data State
  = State
      UnionFind -- UnionFind: for unary relation (variable assignment) and binary relation (variable equivalence)
      [PolyB] -- other relations: for relations with more than 2 variables, summed to 0 or 1
  deriving (Eq, Show)

empty :: State
empty = State UnionFind.empty mempty

export :: State -> Result
export (State uf rels) =
  let (assignments, eqClasses) = UnionFind.export uf
   in Result assignments eqClasses (map fromPolyB $ filter ((> 0) . polyBSize) rels)

--------------------------------------------------------------------------------

-- | Binary field polynomial
data PolyB = PolyB IntSet Bool
  deriving (Eq, Ord, Show)

fromPolyB :: PolyB -> (Bool, IntSet)
fromPolyB (PolyB vars parity) = (parity, vars)

polyBSize :: PolyB -> Int
polyBSize (PolyB vars _) = IntSet.size vars

nullPoly :: PolyB -> Bool
nullPoly (PolyB vars _) = IntSet.null vars

substPolyB :: UnionFind -> PolyB -> PolyB
substPolyB uf (PolyB e b) =
  IntSet.fold step (PolyB mempty b) e
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

--------------------------------------------------------------------------------

data Action
  = Assign Var Bool -- variable assignment
  | Relate Var Var Bool -- variable equivalence
  deriving (Eq, Ord, Show)

-- | If a PolyB has only 1 variable, convert it to an assignment.
--   If a PolyB has 2 variables, convert it to a relation.
--   Otherwise, remain as is.
toAction :: PolyB -> Either PolyB Action
toAction (PolyB vars parity) =
  case IntSet.toList vars of
    [] -> error "[ panic ] Solver: Impossible"
    [var] -> Right (Assign var parity)
    [var1, var2] -> Right (Relate var1 var2 (not parity))
    _ -> Left (PolyB vars parity)

-- | Given a list of actions, update the UnionFind
updateUnionFind :: UnionFind -> [Action] -> UnionFind
updateUnionFind = foldr step
  where
    step (Assign var val) xs = UnionFind.assign xs var val
    step (Relate var1 var2 sameSign) xs = UnionFind.relate xs var1 var2 sameSign

-- | Given a pool of relations, derive actions from them.
updatePool :: UnionFind -> [PolyB] -> ([PolyB], [Action])
updatePool uf = foldr step (mempty, [])
  where
    step poly (pool, actions) =
      case toAction (substPolyB uf poly) of
        Left poly' -> (poly' : pool, actions)
        Right action -> (pool, action : actions)

-- | Apply actions on the relation pool until there is no more actions to apply.
--   Finds the fixed point of `updatePool . updateUnionFind`
applyActionsUntilThereIsNone :: UnionFind -> ([PolyB], [Action]) -> State
applyActionsUntilThereIsNone uf (pool, []) = State uf pool
applyActionsUntilThereIsNone uf (pool, actions) =
  let uf' = updateUnionFind uf actions
   in applyActionsUntilThereIsNone uf' (updatePool uf' pool)

-- | Relate two variables in the state
relate :: Var -> Var -> Bool -> State -> State
relate var1 var2 sameSign (State uf pool) =
  if var1 == var2
    then State uf pool -- no-op
    else -- decide which variable to be the root

      let (root, child) = (var1 `min` var2, var1 `max` var2)
          uf' = UnionFind.relate uf root child sameSign
          poolResult = Either.partitionEithers $ map (relatePolyB root child sameSign) pool
       in applyActionsUntilThereIsNone uf' poolResult

assign :: Var -> Bool -> State -> State
assign var val (State uf pool) =
  let uf' = UnionFind.assign uf var val
      poolResult = Either.partitionEithers $ map (assignPolyB var val) pool
   in applyActionsUntilThereIsNone uf' poolResult

insert :: PolyB -> State -> State
insert poly (State uf pool) =
  let poly' = insertPolyB poly
   in if nullPoly poly'
        then State uf pool -- no-op
        else case toAction poly' of
          Left poly'' -> State uf (poly'' : pool)
          Right action -> applyActionsUntilThereIsNone uf (pool, [action])
  where
    insertPolyB :: PolyB -> PolyB
    insertPolyB (PolyB e b) = IntSet.fold step (PolyB mempty b) e
      where
        step var (PolyB vars parity) =
          case UnionFind.lookup uf var of
            Nothing -> PolyB (IntSet.insert var vars) parity
            Just (UnionFind.Constant val) -> PolyB vars (if val then not parity else parity)
            Just UnionFind.Root ->
              if var `IntSet.member` vars
                then PolyB (IntSet.delete var vars) parity
                else PolyB (IntSet.insert var vars) parity
            Just (UnionFind.ChildOf root sameSign) ->
              if root `IntSet.member` vars
                then PolyB (IntSet.delete root vars) (if sameSign then parity else not parity)
                else PolyB (IntSet.insert root vars) (if sameSign then parity else not parity)

-- | Relate two variables in a binary polynomial, return either the updated polynomial or an action
relatePolyB :: Var -> Var -> Bool -> PolyB -> Either PolyB Action
relatePolyB root child sameSign (PolyB vars parity) =
  if child `IntSet.member` vars
    then
      if root `IntSet.member` vars
        then
          if sameSign
            then -- child + root = 0
              toAction $ PolyB (IntSet.delete child $ IntSet.delete root vars) parity
            else -- child + root = 1
              toAction $ PolyB (IntSet.delete child $ IntSet.delete root vars) (not parity)
        else
          if sameSign
            then -- child = root
              toAction $ PolyB (IntSet.insert root $ IntSet.delete child vars) parity
            else -- child = root + 1
              toAction $ PolyB (IntSet.insert root $ IntSet.delete child vars) (not parity)
    else Left (PolyB vars parity) -- no-op

-- | Assign a variable to a value in a binary polynomial, return either the updated polynomial or an action
assignPolyB :: Var -> Bool -> PolyB -> Either PolyB Action
assignPolyB var val (PolyB vars parity) =
  if var `IntSet.member` vars
    then toAction (PolyB (IntSet.delete var vars) (if val then not parity else parity))
    else Left (PolyB vars parity) -- no-op
