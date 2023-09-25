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
pinnedRefB (RefUBit _ ref _) = pinnedRefU ref
pinnedRefB (RefBX _) = False

pinnedRefU :: RefU -> Bool
pinnedRefU (RefUI _ _) = True
pinnedRefU (RefUP _ _) = True
pinnedRefU (RefUO _ _) = True
pinnedRefU (RefUX _ _) = False

--------------------------------------------------------------------------------

-- | Constraint
--      CAdd: 0 = c + c₀x₀ + c₁x₁ ... cₙxₙ
--      CMul: ax * by = c or ax * by = cz
--      CNEq: if (x - y) == 0 then m = 0 else m = recip (x - y)
data Constraint n
  = CAddL !(PolyL n)
  | CMulL !(PolyL n) !(PolyL n) !(Either n (PolyL n))
  | CVarEq Ref Ref -- when x == y
  | CVarEqF RefF RefF -- when x == y
  | CVarEqB RefB RefB -- when x == y
  | CVarEqL Limb Limb -- when x == y
  | CVarEqU RefU RefU -- when x == y
  | CVarNEqB RefB RefB -- when x = ¬ y
  | CVarBindF Ref n -- when x = val
  | CVarBindB RefB Bool -- when x = val
  | CVarBindL Limb Integer -- when x = val
  | CVarBindU RefU Integer -- when x = val

instance GaloisField n => Eq (Constraint n) where
  xs == ys = case (xs, ys) of
    (CAddL x, CAddL y) -> x == y
    (CMulL x y z, CMulL u v w) ->
      (x == u && y == v || x == v && y == u) && z == w
    (CVarBindF x y, CVarBindF u v) -> x == u && y == v
    (CVarBindB x y, CVarBindB u v) -> x == u && y == v
    (CVarBindL x y, CVarBindL u v) -> x == u && y == v
    (CVarBindU x y, CVarBindU u v) -> x == u && y == v
    _ -> False

instance Functor Constraint where
  fmap f (CAddL x) = CAddL (fmap f x)
  fmap _ (CVarEq x y) = CVarEq x y
  fmap _ (CVarEqF x y) = CVarEqF x y
  fmap _ (CVarEqB x y) = CVarEqB x y
  fmap _ (CVarEqL x y) = CVarEqL x y
  fmap _ (CVarEqU x y) = CVarEqU x y
  fmap _ (CVarNEqB x y) = CVarNEqB x y
  fmap f (CVarBindF x y) = CVarBindF x (f y)
  fmap _ (CVarBindB x y) = CVarBindB x y
  fmap _ (CVarBindL x y) = CVarBindL x y
  fmap _ (CVarBindU x y) = CVarBindU x y
  fmap f (CMulL x y (Left z)) = CMulL (fmap f x) (fmap f y) (Left (f z))
  fmap f (CMulL x y (Right z)) = CMulL (fmap f x) (fmap f y) (Right (fmap f z))

instance (GaloisField n, Integral n) => Show (Constraint n) where
  show (CAddL xs) = "AL " <> show xs <> " = 0"
  show (CVarEq x y) = "EQ " <> show x <> " = " <> show y
  show (CVarEqF x y) = "EF " <> show x <> " = " <> show y
  show (CVarEqB x y) = "EB " <> show x <> " = " <> show y
  show (CVarEqL x y) = "EL " <> show x <> " = " <> show y
  show (CVarEqU x y) = "EU " <> show x <> " = " <> show y
  show (CVarNEqB x y) = "NB " <> show x <> " = ¬ " <> show y
  show (CVarBindF x n) = "VF " <> show x <> " = " <> show n
  show (CVarBindB x n) = "VB " <> show x <> " = " <> show n
  show (CVarBindL x n) = "VL " <> show x <> " = " <> show n
  show (CVarBindU x n) = "VU " <> show x <> " = " <> show n
  show (CMulL aV bV cV) = "ML " <> show aV <> " * " <> show bV <> " = " <> show cV