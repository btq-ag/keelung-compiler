module Keelung.Constraint.Vector
  ( Vector,
    build,
    build',
    empty,
    singleton,
    vars,
    coeffs,
    mergeCoeffs,
    constant,
    view,
    isConstant,
    constantOnly,
    mapVars,
    evaluate,
  )
where

import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.IntSet (IntSet)
import Data.Semiring (Semiring (..))
import Keelung.Syntax.Common (Var)
import Keelung.Util (DebugGF (DebugGF))

-- A Vector is a polynomial of the form "c + c₀x₀ + c₁x₁ ... cₙxₙ = 0"
-- where c is a constant, c₀, c₁, ..., cₙ are coefficients, and x₀, x₁, ..., xₙ are variables.
data Vector n = Vector !n !(IntMap n)
  deriving (Eq)

instance Ord n => Ord (Vector n) where
  compare (Vector c x) (Vector d y) =
    compare (IntMap.size x, x, c) (IntMap.size y, y, d)

instance (Show n, Bounded n, Integral n, Fractional n) => Show (Vector n) where
  --   show (Vector 0 xs) = IntMap.toList go xs
  show (Vector n xs)
    | IntMap.null xs = show (DebugGF n)
    | n == 0 = go (IntMap.toList xs)
    | otherwise = show (DebugGF n) <> " + " <> go (IntMap.toList xs)
    where
      go [] = "<empty>"
      go [term] = printTerm term
      go (term : terms) = printTerm term ++ " + " ++ go terms
      printTerm (_, 0) = error "printTerm: coefficient of 0"
      printTerm (x, 1) = "$" ++ show x
      printTerm (x, -1) = "-$" ++ show x
      printTerm (x, c) = show (toInteger c) ++ "$" ++ show x

-- | Create a vector from a constant and a list of coefficients.
--   Coefficients of 0 are discarded.
build :: (Eq n, Num n) => n -> [(Var, n)] -> Vector n
build c = Vector c . IntMap.filter (0 /=) . IntMap.fromListWith (+)

-- | IntMap version of 'build'.
build' :: (Eq n, Num n) => n -> IntMap n -> Vector n
build' c = Vector c . IntMap.filter (0 /=)

empty :: Num n => Vector n
empty = Vector 0 mempty

-- | Create a vector from a single variable and its coefficient.
singleton :: (Eq n, Num n) => Var -> n -> Vector n
singleton x c = build 0 [(x, c)]

-- | Return the set of variables.
vars :: Vector n -> IntSet
vars = IntMap.keysSet . coeffs

-- | Return the mapping of variables to coefficients.
coeffs :: Vector n -> IntMap n
coeffs (Vector _ xs) = xs

-- | Merge coefficients of the same variable by adding them up
mergeCoeffs :: (Eq n, Num n) => IntMap n -> IntMap n -> IntMap n
mergeCoeffs xs ys = IntMap.filter (0 /=) $ IntMap.unionWith (+) xs ys

-- | Return the constant.
constant :: Vector n -> n
constant (Vector c _) = c

-- | View pattern for Vector
view :: Vector n -> Either n (n, IntMap n)
view (Vector c xs) = if IntMap.null xs then Left c else Right (c, xs)

-- | See if the polynomial has no variables.
isConstant :: Vector n -> Bool
isConstant = IntMap.null . coeffs

-- | See if the polynomial has no variables and return the constant.
constantOnly :: Vector n -> Maybe n
constantOnly (Vector c xs) = if IntMap.null xs then Just c else Nothing

-- | For renumbering the variables.
mapVars :: (Var -> Var) -> Vector n -> Vector n
mapVars f (Vector c xs) = Vector c (IntMap.mapKeys f xs)

-- | Given an assignment of variables, return the value of the polynomial.
evaluate :: Semiring n => Vector n -> IntMap n -> n
evaluate (Vector c xs) assignment =
  IntMap.foldlWithKey
    (\acc k v -> (v `times` IntMap.findWithDefault zero k assignment) `plus` acc)
    c
    xs
