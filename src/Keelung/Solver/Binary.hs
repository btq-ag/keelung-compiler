-- | Specialized solver for addative constraints on binary fields.
--   Intended to be qualified as `Binary`
module Keelung.Solver.Binary (run, Result (..), PolyB (..)) where

import Data.Bits qualified
import Data.Either qualified as Either
import Data.Field.Galois (GaloisField)
import Data.IntMap (IntMap)
import Data.IntMap qualified as IntMap
import Data.IntSet (IntSet)
import Data.IntSet qualified as IntSet
import Data.List qualified as List
import Data.Maybe qualified as Maybe
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
  { resultAssigmnet :: IntMap Bool, -- learned variable assignments
    resultEquivClass :: [(IntSet, IntSet)], -- learned variable equivalence classes, variables of the same class but with different signs are placed in different part of the pair
    resultRelations :: Set PolyB -- boolean polynomials, [(parity, variables)]
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
              -- trace ("\ninsert " <> show (PolyB vars remainder)) $
              --   traceShow state $
              --     traceShow (insert (PolyB vars remainder) state) $
              solve $
                Solving constant' coeffs' (insert (PolyB vars remainder) state)

--------------------------------------------------------------------------------

data State
  = State
      UnionFind -- UnionFind: for unary relation (variable assignment) and binary relation (variable equivalence)
      Pool -- other relations: for relations with more than 2 variables, summed to 0 or 1
  deriving (Eq, Show)

empty :: State
empty = State UnionFind.empty mempty

export :: State -> Result
export (State uf pool) =
  let (assignments, eqClasses) = UnionFind.export uf
   in Result assignments eqClasses (exportPool pool)

--------------------------------------------------------------------------------

-- | Binary field polynomial
data PolyB = PolyB IntSet Bool
  deriving (Eq, Ord)

instance Show PolyB where
  show (PolyB vars parity) =
    if IntSet.null vars
      then if parity then "1" else "0"
      else List.intercalate " + " (map (("$" <>) . show) (IntSet.toList vars)) <> " = " <> (if parity then "1" else "0")

polyBSize :: PolyB -> Int
polyBSize (PolyB vars _) = IntSet.size vars

substPolyB :: UnionFind -> PolyB -> Either Action PolyB
substPolyB uf (PolyB e b) =
  -- trace (show uf) $
  -- trace (show (PolyB e b) <> " ==> " <> show (IntSet.fold step (PolyB mempty b) e)) $
  toAction $ IntSet.fold step (PolyB mempty b) e
  where
    step var (PolyB vars parity) =
      -- trace (show uf) $
      -- trace ("$" <> show var <> " <> " <> show (PolyB vars parity) <> " --> " <> show (UnionFind.lookup uf var)) $
      -- traceShowId $
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

--------------------------------------------------------------------------------

data Action
  = Assign Var Bool -- variable assignment
  | Relate Var Var Bool -- variable equivalence
  | NoOp -- no-op
  deriving (Eq, Ord, Show)

-- | If a PolyB has only 1 variable, convert it to an assignment.
--   If a PolyB has 2 variables, convert it to a relation.
--   Otherwise, remain as is.
toAction :: PolyB -> Either Action PolyB
toAction (PolyB vars parity) =
  case IntSet.toList vars of
    [] -> Left NoOp
    [var] -> Left (Assign var parity)
    [var1, var2] -> Left (Relate var1 var2 (not parity))
    _ -> Right (PolyB vars parity)

-- | Given a list of actions, update the UnionFind
updateUnionFind :: UnionFind -> [Action] -> UnionFind
updateUnionFind = foldr step
  where
    step (Assign var val) xs = UnionFind.assign xs var val
    step (Relate var1 var2 sameSign) xs = UnionFind.relate xs var1 var2 sameSign
    step NoOp xs = xs

-- | Given a pool of relations, derive actions from them.
updatePool :: UnionFind -> [PolyB] -> ([Action], [PolyB])
updatePool uf = Either.partitionEithers . map (substPolyB uf)

-- | Apply actions on the relation pool until there is no more actions to apply.
--   Finds the fixed point of `updatePool . updateUnionFind`
applyActionsUntilThereIsNone :: UnionFind -> ([Action], [PolyB]) -> State
applyActionsUntilThereIsNone uf ([], pool) = State uf (Set.fromList pool)
applyActionsUntilThereIsNone uf (actions, pool) =
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
          poolResult = Either.partitionEithers $ map (substPolyB uf') $ Set.toList pool
       in applyActionsUntilThereIsNone uf' poolResult

-- | Assign a variable to a value in the state
assign :: Var -> Bool -> State -> State
assign var val (State uf pool) =
  let uf' = UnionFind.assign uf var val
      poolResult = Either.partitionEithers $ map (substPolyB uf') $ Set.toList pool
   in applyActionsUntilThereIsNone uf' poolResult

-- | Insert a binary polynomial into the state
insert :: PolyB -> State -> State
insert poly (State uf pool) = applyActionsUntilThereIsNone uf $ case substPolyB uf poly of
  Right poly'' -> insertPool pool poly''
  Left action -> ([action], Set.toList pool)

--------------------------------------------------------------------------------

-- | For managing relations with more than 2 variables. (Relations with 1 or 2 variables are handled by the UnionFind)
type Pool = Set PolyB

-- | Insert a binary polynomial into the pool
--   Compare the polynomial with the existing ones, and derive actions from them.
--   Actions are generated when the inserted polynomial has a edit distance of 1 or 2 with the existing ones.
insertPool :: Pool -> PolyB -> ([Action], [PolyB])
insertPool pool poly = (Maybe.mapMaybe (calculateAction poly) (Set.toList pool), poly : Set.toList pool)
  where
    calculateAction :: PolyB -> PolyB -> Maybe Action
    calculateAction (PolyB vars1 parity1) (PolyB vars2 parity2) =
      let diff = IntSet.difference vars1 vars2 <> IntSet.difference vars2 vars1
       in case IntSet.toList diff of
            [] -> Nothing -- `poly` already exists in the pool
            [var] -> Just $ Assign var (parity1 /= parity2)
            [var1, var2] -> Just $ Relate var1 var2 (parity1 == parity2)
            _ -> Nothing

exportPool :: Pool -> Set PolyB
exportPool = Set.filter ((> 2) . polyBSize)