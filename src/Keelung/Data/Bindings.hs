{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Keelung.Data.Bindings where

import Control.DeepSeq (NFData)
import Data.Field.Galois (GaloisField)
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import qualified Data.List as List
import Data.Maybe (isNothing)
import Data.Serialize (Serialize)
import Data.Vector (Vector)
import qualified Data.Vector as Vector
import GHC.Generics (Generic)
import Keelung.Field.N (N (N))
import Keelung.Types

--------------------------------------------------------------------------------
type Total n = Bindings (Binding (Vector n)) (Binding (Vector n)) (Binding (Vector n))

type Partial n = Bindings (Binding (Vector (Maybe n))) (Binding (Vector (Maybe n))) (Binding (Vector (Maybe n)))

type Sparse n = Bindings (Binding (IntMap n)) (Binding (IntMap n)) (Binding (IntMap n))

type Vars n = Bindings (Binding IntSet) (Binding IntSet) (Binding IntSet)

-- | Convert a partial binding to a total binding, or return the variables that are not bound
toTotal :: Partial n -> Either (Vars n) (Total n)
toTotal (Bindings f b u) =
  let -- 1. convert the partial binding to a total binding
      -- 2. collect the variables that are not bound
      (fK, fV) = splitPair $ fmap collectNothings f
      (bK, bV) = splitPair $ fmap collectNothings b
      (uK, uV) = splitIntMap $ fmap (splitPair . fmap collectNothings) u
      -- tally the number of variables that are not bound
      fKSize = varsSize fK
      bKSize = varsSize bK
      uKSize = sum $ fmap varsSize uK
   in if fKSize + bKSize + uKSize == 0
        then Right $ Bindings fV bV uV
        else Left $ Bindings fK bK uK
  where
    collectNothings :: Vector (Maybe n) -> (IntSet, Vector n)
    collectNothings xs = (IntSet.fromList $ Vector.toList $ Vector.findIndices isNothing xs, Vector.mapMaybe id xs)

    splitIntMap :: IntMap (a, b) -> (IntMap a, IntMap b)
    splitIntMap m = (IntMap.map fst m, IntMap.map snd m)

    -- NOTE: should take output variables into account
    --       and restore this to "IntSet.size o + IntSet.size i + IntSet.size x"
    varsSize :: Binding IntSet -> Int
    varsSize (Binding _ i x) = IntSet.size i + IntSet.size x

--------------------------------------------------------------------------------

-- | Binding of a single datatype
data Binding n = Binding
  { ofO :: n,
    ofI :: n,
    ofX :: n
  }
  deriving (Eq, Show, NFData, Generic)

instance Semigroup n => Semigroup (Binding n) where
  Binding o1 i1 x1 <> Binding o2 i2 x2 = Binding (o1 <> o2) (i1 <> i2) (x1 <> x2)

instance Monoid n => Monoid (Binding n) where
  mempty = Binding mempty mempty mempty

instance Foldable Binding where
  foldMap f (Binding o i x) = f o <> f i <> f x

instance Functor Binding where
  fmap f (Binding o i x) = Binding (f o) (f i) (f x)

instance Traversable Binding where
  traverse f (Binding o i x) = Binding <$> f o <*> f i <*> f x

instance Serialize n => Serialize (Binding n)

instance {-# OVERLAPPING #-} (GaloisField n, Integral n) => Show (Binding (Vector (Maybe n))) where
  show (Binding o i x) = "output: " <> showVec o <> ", input: " <> showVec i <> ", intermediate: " <> showVec x
    where
      showVec = showList' . Vector.toList . fmap (\(index, value) -> case value of
                Nothing -> "(" <> show index <> ",?)"
                Just value' -> show (index, N value')
            ) . Vector.indexed

      showList' :: [String] -> String
      showList' xs = "[" <> List.intercalate ", " xs <> "]"

      

updateX :: (n -> n) -> Binding n -> Binding n
updateX f (Binding o i x) = Binding o i (f x)

updateO :: (n -> n) -> Binding n -> Binding n
updateO f (Binding o i x) = Binding (f o) i x

updateI :: (n -> n) -> Binding n -> Binding n
updateI f (Binding o i x) = Binding o (f i) x

splitPair :: Binding (a, b) -> (Binding a, Binding b)
splitPair (Binding (o1, o2) (i1, i2) (x1, x2)) = (Binding o1 i1 x1, Binding o2 i2 x2)

--------------------------------------------------------------------------------

-- | Bindings of different datatypes
data Bindings f b u = Bindings
  { ofF :: f,
    ofB :: b,
    ofU :: IntMap u
  }
  deriving (Eq, Show, NFData, Generic)

instance (Semigroup f, Semigroup b, Semigroup u) => Semigroup (Bindings f b u) where
  Bindings f1 b1 u1 <> Bindings f2 b2 u2 = Bindings (f1 <> f2) (b1 <> b2) (u1 <> u2)

instance (Monoid f, Monoid b, Monoid u) => Monoid (Bindings f b u) where
  mempty = Bindings mempty mempty mempty

instance (Serialize f, Serialize b, Serialize u) => Serialize (Bindings f b u)

updateF :: (f -> f) -> Bindings f b u -> Bindings f b u
updateF f (Bindings f' b u) = Bindings (f f') b u

updateB :: (b -> b) -> Bindings f b u -> Bindings f b u
updateB f (Bindings f' b u) = Bindings f' (f b) u

updateU :: Width -> (u -> u) -> Bindings f b u -> Bindings f b u
updateU w f (Bindings f' b u) = Bindings f' b $ IntMap.adjust f w u

--------------------------------------------------------------------------------

instance {-# OVERLAPPING #-} Show (Vars n) where
  show (Bindings f b u) =
    showList' $
      showBinding "F" f <> showBinding "B" b
        <> concatMap (\(width, xs) -> showBinding ("U" <> toSubscript width) xs) (IntMap.toList u)
    where
      showList' :: [String] -> String
      showList' xs = "[" <> List.intercalate ", " xs <> "]"

      showBinding :: String -> Binding IntSet -> [String]
      showBinding prefix (Binding o i x) =
        map (\var -> "$" <> prefix <> "O" <> show var) (IntSet.toList o)
          <> map (\var -> "$" <> prefix <> "I" <> show var) (IntSet.toList i)
          <> map (\var -> "$" <> prefix <> show var) (IntSet.toList x)

      toSubscript :: Int -> String
      toSubscript = map go . show
        where
          go c = case c of
            '0' -> '₀'
            '1' -> '₁'
            '2' -> '₂'
            '3' -> '₃'
            '4' -> '₄'
            '5' -> '₅'
            '6' -> '₆'
            '7' -> '₇'
            '8' -> '₈'
            '9' -> '₉'
            _ -> c