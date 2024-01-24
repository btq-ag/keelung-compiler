module Keelung.Data.Constraint
  ( Constraint (..),
    pinnedRef,
    pinnedRefB,
    pinnedRefU,
  )
where

import Data.Field.Galois (GaloisField)
import Keelung.Data.Limb (Limb)
import Keelung.Data.PolyL (PolyL)
import Keelung.Data.Reference
import Keelung.Data.Slice (Slice)

--------------------------------------------------------------------------------

pinnedRef :: Ref -> Bool
pinnedRef (B ref) = pinnedRefB ref
pinnedRef (F ref) = pinnedRefF ref

pinnedRefF :: RefF -> Bool
pinnedRefF (RefFO _) = True
pinnedRefF (RefFI _) = True
pinnedRefF (RefFP _) = True
pinnedRefF (RefFX _) = False

pinnedRefB :: RefB -> Bool
pinnedRefB (RefBI _) = True
pinnedRefB (RefBP _) = True
pinnedRefB (RefBO _) = True
pinnedRefB (RefUBit ref _) = pinnedRefU ref
pinnedRefB (RefBX _) = False

pinnedRefU :: RefU -> Bool
pinnedRefU (RefUI _ _) = True
pinnedRefU (RefUP _ _) = True
pinnedRefU (RefUO _ _) = True
pinnedRefU (RefUX _ _) = False

--------------------------------------------------------------------------------

-- | Specialized constraints
data Constraint n
  = CAddL !(PolyL n) -- additive constraint
  | CMulL !(PolyL n) !(PolyL n) !(Either n (PolyL n)) -- multiplicative constraint
  | CRefEq Ref Ref -- Ref equality
  | CLimbEq Limb Limb -- Limb equality
  | CRefUEq RefU RefU -- RefU equality
  | CSliceEq Slice Slice -- Slice equality
  | CRefBNEq RefB RefB -- RefB negation
  | CRefFVal Ref n -- x = val
  | CLimbVal Limb Integer -- x = val
  | CRefUVal RefU Integer -- x = val
  | CSliceVal Slice Integer -- x = val

instance GaloisField n => Eq (Constraint n) where
  xs == ys = case (xs, ys) of
    (CAddL x, CAddL y) -> x == y
    (CMulL x y z, CMulL u v w) ->
      (x == u && y == v || x == v && y == u) && z == w
    (CRefFVal x y, CRefFVal u v) -> x == u && y == v
    (CLimbVal x y, CLimbVal u v) -> x == u && y == v
    (CRefUVal x y, CRefUVal u v) -> x == u && y == v
    (CSliceVal x y, CSliceVal u v) -> x == u && y == v
    _ -> False

instance Functor Constraint where
  fmap f (CAddL x) = CAddL (fmap f x)
  fmap _ (CRefEq x y) = CRefEq x y
  fmap _ (CLimbEq x y) = CLimbEq x y
  fmap _ (CRefUEq x y) = CRefUEq x y
  fmap _ (CSliceEq x y) = CSliceEq x y
  fmap _ (CRefBNEq x y) = CRefBNEq x y
  fmap f (CRefFVal x y) = CRefFVal x (f y)
  fmap _ (CLimbVal x y) = CLimbVal x y
  fmap _ (CRefUVal x y) = CRefUVal x y
  fmap _ (CSliceVal x y) = CSliceVal x y
  fmap f (CMulL x y (Left z)) = CMulL (fmap f x) (fmap f y) (Left (f z))
  fmap f (CMulL x y (Right z)) = CMulL (fmap f x) (fmap f y) (Right (fmap f z))

instance (GaloisField n, Integral n) => Show (Constraint n) where
  show (CAddL xs) = "AL " <> show xs <> " = 0"
  show (CRefEq x y) = "EQ " <> show x <> " = " <> show y
  show (CLimbEq x y) = "EL " <> show x <> " = " <> show y
  show (CRefUEq x y) = "EU " <> show x <> " = " <> show y
  show (CSliceEq x y) = "ES " <> show x <> " = " <> show y
  show (CRefBNEq x y) = "NB " <> show x <> " = ¬ " <> show y
  show (CRefFVal x n) = "VF " <> show x <> " = " <> show n
  show (CLimbVal x n) = "VL " <> show x <> " = " <> show n
  show (CRefUVal x n) = "VU " <> show x <> " = " <> show n
  show (CSliceVal x n) = "VS " <> show x <> " = " <> show n
  show (CMulL aV bV cV) = "ML " <> show aV <> " * " <> show bV <> " = " <> show cV