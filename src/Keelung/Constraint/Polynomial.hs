module Keelung.Constraint.Polynomial
  ( Poly,
    build,
    build',
    buildEither,
    buildEither',
    buildMaybe',
    singleton,
    vars,
    coeffs,
    mergeCoeffs,
    constant,
    view,
    mapVars,
    evaluate,
    --
    delete,
    merge,
    negate,
  )
where

import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.IntSet (IntSet)
import Data.Semiring (Semiring (..))
import Keelung.Syntax.Common (Var)
import Keelung.Util (DebugGF (DebugGF))
import Prelude hiding (negate)
import qualified Prelude

-- A Poly is a polynomial of the form "c + c₀x₀ + c₁x₁ ... cₙxₙ = 0"
--   Invariances:
--      * The coefficients are non-zone
--      * The degree of the polynomial is 1 (there's at least one variable)
data Poly n = Poly !n !(IntMap n)
  deriving (Eq)

instance Ord n => Ord (Poly n) where
  compare (Poly c x) (Poly d y) =
    compare (IntMap.size x, x, c) (IntMap.size y, y, d)

instance (Show n, Bounded n, Integral n, Fractional n) => Show (Poly n) where
  show (Poly n xs)
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

-- | Create a polynomial from a constant and a list of coefficients.
--   Coefficients of 0 are discarded.
build :: (Eq n, Num n) => n -> [(Var, n)] -> Poly n
build c = build' c . IntMap.filter (0 /=) . IntMap.fromListWith (+)

-- | IntMap version of 'build'.
build' :: (Eq n, Num n) => n -> IntMap n -> Poly n
build' c xs =
  if IntMap.null xs
    then error "error: build': no variables in polynomial"
    else Poly c xs

-- | Type-safe version of 'build''
buildEither :: (Eq n, Num n) => n -> [(Var, n)] -> Either n (Poly n)
buildEither c xs =
  let xs' = IntMap.filter (0 /=) $ IntMap.fromListWith (+) xs
   in if IntMap.null xs'
        then Left c
        else Right $ build' c xs'

buildEither' :: (Eq n, Num n) => n -> IntMap n -> Either n (Poly n)
buildEither' c xs =
  if IntMap.null xs
    then Left c
    else Right $ build' c xs

buildMaybe' :: (Eq n, Num n) => n -> IntMap n -> Maybe (Poly n)
buildMaybe' c xs =
  if IntMap.null xs
    then Nothing
    else Just $ build' c xs

-- | Create a polynomial from a single variable and its coefficient.
singleton :: (Eq n, Num n) => Var -> n -> Poly n
singleton x c = build 0 [(x, c)]

-- | Return the set of variables.
vars :: Poly n -> IntSet
vars = IntMap.keysSet . coeffs

-- | Return the mapping of variables to coefficients.
coeffs :: Poly n -> IntMap n
coeffs (Poly _ xs) = xs

-- | Merge coefficients of the same variable by adding them up
mergeCoeffs :: (Eq n, Num n) => IntMap n -> IntMap n -> IntMap n
mergeCoeffs xs ys = IntMap.filter (0 /=) $ IntMap.unionWith (+) xs ys

-- | Return the constant.
constant :: Poly n -> n
constant (Poly c _) = c

-- | View pattern for Poly
view :: Poly n -> (n, IntMap n)
view (Poly c xs) = (c, xs)

-- | For renumbering the variables.
mapVars :: (Var -> Var) -> Poly n -> Poly n
mapVars f (Poly c xs) = Poly c (IntMap.mapKeys f xs)

-- | Given an assignment of variables, return the value of the polynomial.
evaluate :: Semiring n => Poly n -> IntMap n -> n
evaluate (Poly c xs) assignment =
  IntMap.foldlWithKey
    (\acc k v -> (v `times` IntMap.findWithDefault zero k assignment) `plus` acc)
    c
    xs

-- | Delete a variable from the polynomial.
delete :: (Eq n, Num n) => Var -> Poly n -> Maybe (Poly n)
delete x (Poly c xs) = buildMaybe' c (IntMap.delete x xs)

-- | Merge two polynomials.
merge :: (Eq n, Num n) => Poly n -> Poly n -> Maybe (Poly n)
merge (Poly c xs) (Poly d ys) = buildMaybe' (c + d) (mergeCoeffs xs ys)

-- | Negate a polynomial.
negate :: (Eq n, Num n) => Poly n -> Poly n
negate (Poly c xs) = Poly (- c) (fmap Prelude.negate xs)