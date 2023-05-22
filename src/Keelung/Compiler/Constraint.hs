{-# LANGUAGE DeriveAnyClass #-}
{-# HLINT ignore "Use list comprehension" #-}
{-# LANGUAGE DeriveGeneric #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Keelung.Compiler.Constraint
  ( Ref (..),
    RefF (..),
    RefB (..),
    RefU (..),
    reindexRef,
    reindexRefF,
    reindexRefB,
    reindexRefU,
    Constraint (..),
    pinnedRef,
    pinnedRefB,
    pinnedRefU,
    fromConstraint,
    fromPoly_,
  )
where

import Control.DeepSeq (NFData)
import Data.Bifunctor (first)
import Data.Field.Galois (GaloisField)
import Data.Map.Strict qualified as Map
import GHC.Generics (Generic)
import Keelung.Compiler.ConstraintSystem qualified as Linked
import Keelung.Data.PolyG (PolyG)
import Keelung.Data.PolyG qualified as PolyG
import Keelung.Data.Polynomial (Poly)
import Keelung.Data.Polynomial qualified as Poly
import Keelung.Data.VarGroup (toSubscript)
import Keelung.Syntax
import Keelung.Syntax.Counters

fromConstraint :: (GaloisField n, Integral n) => Counters -> Constraint n -> Linked.Constraint n
fromConstraint counters (CAddF as) = Linked.CAdd (fromPoly_ counters as)
fromConstraint counters (CVarEq x y) =
  case Poly.buildEither 0 [(reindexRef counters x, 1), (reindexRef counters y, -1)] of
    Left _ -> error "CVarEq: two variables are the same"
    Right xs -> Linked.CAdd xs
fromConstraint counters (CVarEqF x y) =
  case Poly.buildEither 0 [(reindexRefF counters x, 1), (reindexRefF counters y, -1)] of
    Left _ -> error "CVarEqF: two variables are the same"
    Right xs -> Linked.CAdd xs
fromConstraint counters (CVarEqB x y) =
  case Poly.buildEither 0 [(reindexRefB counters x, 1), (reindexRefB counters y, -1)] of
    Left _ -> error $ "CVarEqB: two variables are the same" ++ show x ++ " " ++ show y
    Right xs -> Linked.CAdd xs
fromConstraint counters (CVarNEqB x y) =
  case Poly.buildEither 1 [(reindexRefB counters x, -1), (reindexRefB counters y, -1)] of
    Left _ -> error "CVarNEqB: two variables are the same"
    Right xs -> Linked.CAdd xs
fromConstraint counters (CVarEqU x y) =
  case Poly.buildEither 0 [(reindexRefU counters x, 1), (reindexRefU counters y, -1)] of
    Left _ -> error "CVarEqU: two variables are the same"
    Right xs -> Linked.CAdd xs
fromConstraint counters (CVarBindF x n) = Linked.CAdd (Poly.bind (reindexRef counters x) n)
fromConstraint counters (CVarBindB x True) = Linked.CAdd (Poly.bind (reindexRefB counters x) 1)
fromConstraint counters (CVarBindB x False) = Linked.CAdd (Poly.bind (reindexRefB counters x) 0)
fromConstraint counters (CVarBindU x n) = Linked.CAdd (Poly.bind (reindexRefU counters x) n)
fromConstraint counters (CMulF as bs cs) =
  Linked.CMul
    (fromPoly_ counters as)
    (fromPoly_ counters bs)
    ( case cs of
        Left n -> Left n
        Right xs -> fromPoly counters xs
    )

--------------------------------------------------------------------------------

-- | For representing mixed variables in constraints
data Ref
  = -- | Field variable
    F RefF
  | -- | Boolean variable
    B RefB
  | -- | UInt variable
    U RefU
  deriving (Eq, Ord, Generic, NFData)

instance Show Ref where
  show (F x) = show x
  show (B x) = show x
  show (U x) = show x

-- | For representing Boolean variables in constraints
data RefB
  = -- | Boolean output variable
    RefBO Var
  | -- | Boolean public input variable
    RefBI Var
  | -- | Boolean private input variable
    RefBP Var
  | -- | Boolean intermediate variable
    RefBX Var
  | -- | UInt bit variable
    RefUBit Width RefU Int
  deriving (Eq, Ord, Generic, NFData)

instance Show RefB where
  show (RefBO x) = "BO" ++ show x
  show (RefBI x) = "BI" ++ show x
  show (RefBP x) = "BP" ++ show x
  show (RefBX x) = "B" ++ show x
  show (RefUBit _ x i) = show x ++ "[" ++ show i ++ "]"

-- | For representing Field variables in constraints
data RefF
  = -- | Field output variable
    RefFO Var
  | -- | Field public input variable
    RefFI Var
  | -- | Field private input variable
    RefFP Var
  | -- | Field intermediate variable
    RefFX Var
  deriving (Eq, Ord, Generic, NFData)

instance Show RefF where
  show (RefFO x) = "FO" ++ show x
  show (RefFI x) = "FI" ++ show x
  show (RefFP x) = "FP" ++ show x
  show (RefFX x) = "F" ++ show x

-- | For representing UInt variables in constraints
data RefU
  = -- | UInt output variable
    RefUO Width Var
  | -- | UInt public input variable
    RefUI Width Var
  | -- | UInt private input variable
    RefUP Width Var
  | -- | UInt intermediate variable
    RefUX Width Var
  deriving (Eq, Ord, Generic, NFData)

instance Show RefU where
  show ref = case ref of
    RefUO w x -> "UO" ++ toSubscript w ++ show x
    RefUI w x -> "UI" ++ toSubscript w ++ show x
    RefUP w x -> "UP" ++ toSubscript w ++ show x
    RefUX w x -> "U" ++ toSubscript w ++ show x

instance HasWidth RefU where
  widthOf (RefUO width _) = width
  widthOf (RefUI width _) = width
  widthOf (RefUP width _) = width
  widthOf (RefUX width _) = width

--------------------------------------------------------------------------------

pinnedRef :: Ref -> Bool
pinnedRef (B ref) = pinnedRefB ref
pinnedRef (U ref) = pinnedRefU ref
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

reindexRef :: Counters -> Ref -> Var
reindexRef counters (F x) = reindexRefF counters x
reindexRef counters (B x) = reindexRefB counters x
reindexRef counters (U x) = reindexRefU counters x

reindexRefF :: Counters -> RefF -> Var
reindexRefF counters (RefFO x) = reindex counters Output ReadField x
reindexRefF counters (RefFI x) = reindex counters PublicInput ReadField x
reindexRefF counters (RefFP x) = reindex counters PrivateInput ReadField x
reindexRefF counters (RefFX x) = reindex counters Intermediate ReadField x

reindexRefB :: Counters -> RefB -> Var
reindexRefB counters (RefBO x) = reindex counters Output ReadBool x
reindexRefB counters (RefBI x) = reindex counters PublicInput ReadBool x
reindexRefB counters (RefBP x) = reindex counters PrivateInput ReadBool x
reindexRefB counters (RefBX x) = reindex counters Intermediate ReadBool x
reindexRefB counters (RefUBit _ x i) =
  case x of
    RefUO w x' -> reindex counters Output (ReadBits w) x' + (i `mod` w)
    RefUI w x' -> reindex counters PublicInput (ReadBits w) x' + (i `mod` w)
    RefUP w x' -> reindex counters PrivateInput (ReadBits w) x' + (i `mod` w)
    RefUX w x' -> reindex counters Intermediate (ReadBits w) x' + (i `mod` w)

reindexRefU :: Counters -> RefU -> Var
reindexRefU counters (RefUO w x) = reindex counters Output (ReadUInt w) x
reindexRefU counters (RefUI w x) = reindex counters PublicInput (ReadUInt w) x
reindexRefU counters (RefUP w x) = reindex counters PrivateInput (ReadUInt w) x
reindexRefU counters (RefUX w x) = reindex counters Intermediate (ReadUInt w) x

--------------------------------------------------------------------------------

fromPoly :: (Integral n, GaloisField n) => Counters -> PolyG Ref n -> Either n (Poly n)
fromPoly counters poly = case PolyG.view poly of
  PolyG.Monomial constant (var, coeff) -> Poly.buildEither constant [(reindexRef counters var, coeff)]
  PolyG.Binomial constant (var1, coeff1) (var2, coeff2) -> Poly.buildEither constant [(reindexRef counters var1, coeff1), (reindexRef counters var2, coeff2)]
  PolyG.Polynomial constant xs -> Poly.buildEither constant (map (first (reindexRef counters)) (Map.toList xs))

fromPoly_ :: (Integral n, GaloisField n) => Counters -> PolyG Ref n -> Poly n
fromPoly_ counters xs = case fromPoly counters xs of
  Left _ -> error "[ panic ] fromPoly_: Left"
  Right p -> p

--------------------------------------------------------------------------------

-- | Constraint
--      CAdd: 0 = c + c₀x₀ + c₁x₁ ... cₙxₙ
--      CMul: ax * by = c or ax * by = cz
--      CNEq: if (x - y) == 0 then m = 0 else m = recip (x - y)
data Constraint n
  = CAddF !(PolyG Ref n)
  | CVarEq Ref Ref -- when x == y
  | CVarEqF RefF RefF -- when x == y
  | CVarEqB RefB RefB -- when x == y
  | CVarNEqB RefB RefB -- when x = ¬ y
  | CVarEqU RefU RefU -- when x == y
  | CVarBindF Ref n -- when x = val
  | CVarBindB RefB Bool -- when x = val
  | CVarBindU RefU n -- when x = val
  | CMulF !(PolyG Ref n) !(PolyG Ref n) !(Either n (PolyG Ref n))

instance GaloisField n => Eq (Constraint n) where
  xs == ys = case (xs, ys) of
    (CAddF x, CAddF y) -> x == y
    -- (CAddB x, CAddB y) -> x == y
    (CVarEqU x y, CVarEqU u v) -> (x == u && y == v) || (x == v && y == u)
    (CVarBindU x y, CVarBindU u v) -> x == u && y == v
    (CVarBindF x y, CVarBindF u v) -> x == u && y == v
    (CMulF x y z, CMulF u v w) ->
      (x == u && y == v || x == v && y == u) && z == w
    _ -> False

instance Functor Constraint where
  fmap f (CAddF x) = CAddF (fmap f x)
  fmap _ (CVarEq x y) = CVarEq x y
  fmap _ (CVarEqF x y) = CVarEqF x y
  fmap _ (CVarNEqB x y) = CVarNEqB x y
  fmap _ (CVarEqB x y) = CVarEqB x y
  fmap _ (CVarEqU x y) = CVarEqU x y
  fmap f (CVarBindF x y) = CVarBindF x (f y)
  fmap _ (CVarBindB x y) = CVarBindB x y
  fmap f (CVarBindU x y) = CVarBindU x (f y)
  fmap f (CMulF x y (Left z)) = CMulF (fmap f x) (fmap f y) (Left (f z))
  fmap f (CMulF x y (Right z)) = CMulF (fmap f x) (fmap f y) (Right (fmap f z))

instance (GaloisField n, Integral n) => Show (Constraint n) where
  show (CAddF xs) = "AF " <> show xs <> " = 0"
  show (CVarEq x y) = "EQ " <> show x <> " = " <> show y
  show (CVarEqF x y) = "VF " <> show x <> " = " <> show y
  show (CVarEqB x y) = "VB " <> show x <> " = " <> show y
  show (CVarNEqB x y) = "VN " <> show x <> " = ¬ " <> show y
  show (CVarEqU x y) = "VU " <> show x <> " = " <> show y
  show (CVarBindF x n) = "BF " <> show x <> " = " <> show n
  show (CVarBindB x n) = "BB " <> show x <> " = " <> show n
  show (CVarBindU x n) = "BU " <> show x <> " = " <> show n
  show (CMulF aV bV cV) = "MF " <> show aV <> " * " <> show bV <> " = " <> show cV