module Keelung.Data.Bindings where

import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.Vector (Vector)
import Keelung.Types (Width)

--------------------------------------------------------------------------------
type Total n = Bindings (Binding (Vector n)) (Binding (Vector n)) (Binding (Vector n))

type Partial n = Bindings (Binding (Vector (Maybe n))) (Binding (Vector (Maybe n))) (Binding (Vector (Maybe n)))

type Sparse n = Bindings (Binding (IntMap n)) (Binding (IntMap n)) (Binding (IntMap n))

--------------------------------------------------------------------------------

-- | Binding of a single datatype
data Binding n = Binding
  { ofI :: n,
    ofO :: n,
    ofX :: n
  }

instance Semigroup n => Semigroup (Binding n) where
  Binding i1 o1 x1 <> Binding i2 o2 x2 = Binding (i1 <> i2) (o1 <> o2) (x1 <> x2)

instance Monoid n => Monoid (Binding n) where
  mempty = Binding mempty mempty mempty

updateX :: (n -> n) -> Binding n -> Binding n
updateX f (Binding i o x) = Binding i o (f x)

updateO :: (n -> n) -> Binding n -> Binding n
updateO f (Binding i o x) = Binding i (f o) x

updateI :: (n -> n) -> Binding n -> Binding n
updateI f (Binding i o x) = Binding (f i) o x

--------------------------------------------------------------------------------

-- | Bindings of different datatypes
data Bindings f b u = Bindings
  { ofF :: f,
    ofB :: b,
    ofU :: IntMap u
  }

instance (Semigroup f, Semigroup b, Semigroup u) => Semigroup (Bindings f b u) where
  Bindings f1 b1 u1 <> Bindings f2 b2 u2 = Bindings (f1 <> f2) (b1 <> b2) (u1 <> u2)

instance (Monoid f, Monoid b, Monoid u) => Monoid (Bindings f b u) where
  mempty = Bindings mempty mempty mempty

updateF :: (f -> f) -> Bindings f b u -> Bindings f b u
updateF f (Bindings f' b u) = Bindings (f f') b u

updateB :: (b -> b) -> Bindings f b u -> Bindings f b u
updateB f (Bindings f' b u) = Bindings f' (f b) u

updateU :: Width -> (u -> u) -> Bindings f b u -> Bindings f b u
updateU w f (Bindings f' b u) = Bindings f' b $ IntMap.adjust f w u