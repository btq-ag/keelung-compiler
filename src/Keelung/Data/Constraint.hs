{-# LANGUAGE DeriveAnyClass #-}
{-# HLINT ignore "Use list comprehension" #-}
{-# LANGUAGE DeriveGeneric #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Keelung.Data.Constraint
  ( Ref (..),
    RefBin (..),
    toRefUBits,
    RefF (..),
    RefB (..),
    RefU (..),
    Constraint (..),
    pinnedRef,
    pinnedRefB,
    pinnedRefU,
  )
where

import Control.DeepSeq (NFData)
import Data.Field.Galois (GaloisField)
import GHC.Generics (Generic)
import Keelung.Data.PolyG (PolyG)
import Keelung.Data.VarGroup (toSubscript)
import Keelung.Syntax

--------------------------------------------------------------------------------

-- | For representing mixed variables in constraints
data Ref
  = -- | Field variable
    F RefF
  | -- | Boolean variable
    B RefB
  | -- | Sequence of coefficients of binary representation of UInt variable
    U RefBin
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

data RefBin = RefBin
  { refBinRefU :: RefU,
    refBinWidth :: Int,
    refBinStart :: Int,
    refBinPowerOffset :: Int,
    -- refBinMultiplier :: Integer,
    refBinSigns :: Either Bool [Bool]
  }
  deriving (Eq, Ord, Generic, NFData)

instance Show RefBin where
  show (RefBin _ 0 _ _ _) = "<Empty RefBin>"
  show (RefBin ref 1 i offset (Left sign)) = if sign then "" else "-" <> "2" <> toSuperscript offset <> "$" <> show (RefUBit 1 ref i)
  show (RefBin ref 1 i offset (Right signs)) = if head signs then "" else "-" <> "2" <> toSuperscript offset <> "$" <> show (RefUBit 1 ref i)
  show (RefBin ref 2 i offset (Left sign)) = if sign then "" else "-" <> "2" <> toSuperscript offset <> "$" <> show (RefUBit 1 ref i) <> " " <> if sign then "+" else "-" <> "2" <> toSuperscript (offset + 1) <> "$" <> show (RefUBit 1 ref (i + 1))
  show (RefBin ref 2 i offset (Right signs)) = if head signs then "" else "-" <> "2" <> toSuperscript offset <> "$" <> show (RefUBit 1 ref i) <> " " <> if last signs then "+" else "-" <> "2" <> toSuperscript (offset + 1) <> "$" <> show (RefUBit 1 ref (i + 1))
  show (RefBin ref width offset i (Left sign)) =
    if sign then "" else "-" <> "2" <> toSuperscript offset <> "$" <> show (RefUBit 1 ref i) <> " ... " <> if sign then "+" else "-" <> "2" <> toSuperscript (offset + width - 1) <> "$" <> show (RefUBit 1 ref (i + width - 1))
  show (RefBin ref width offset i (Right signs)) =
    if head signs then "" else "-" <> "2" <> toSuperscript offset <> "$" <> show (RefUBit 1 ref i) <> " ... " <> if last signs then "+" else "-" <> "2" <> toSuperscript (offset + width - 1) <> "$" <> show (RefUBit 1 ref (i + width - 1))

-- | Helper function for converting integers to superscript strings
toSuperscript :: Int -> String
toSuperscript = map convert . show
  where
    convert '0' = '⁰'
    convert '1' = '¹'
    convert '2' = '²'
    convert '3' = '³'
    convert '4' = '⁴'
    convert '5' = '⁵'
    convert '6' = '⁶'
    convert '7' = '⁷'
    convert '8' = '⁸'
    convert _ = '⁹'

toRefUBits :: RefBin -> [RefB]
toRefUBits refBin = [RefUBit (refBinWidth refBin) (refBinRefU refBin) (i + refBinStart refBin) | i <- [0 .. refBinWidth refBin - 1]]

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
pinnedRef (F ref) = pinnedRefF ref
pinnedRef (U ref) = pinnedRefBin ref

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

pinnedRefBin :: RefBin -> Bool
pinnedRefBin = pinnedRefU . refBinRefU

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
  | CVarBindF Ref n -- when x = val
  | CVarBindB RefB Bool -- when x = val
  | CMulF !(PolyG Ref n) !(PolyG Ref n) !(Either n (PolyG Ref n))

instance GaloisField n => Eq (Constraint n) where
  xs == ys = case (xs, ys) of
    (CAddF x, CAddF y) -> x == y
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
  fmap f (CVarBindF x y) = CVarBindF x (f y)
  fmap _ (CVarBindB x y) = CVarBindB x y
  fmap f (CMulF x y (Left z)) = CMulF (fmap f x) (fmap f y) (Left (f z))
  fmap f (CMulF x y (Right z)) = CMulF (fmap f x) (fmap f y) (Right (fmap f z))

instance (GaloisField n, Integral n) => Show (Constraint n) where
  show (CAddF xs) = "AF " <> show xs <> " = 0"
  show (CVarEq x y) = "EQ " <> show x <> " = " <> show y
  show (CVarEqF x y) = "VF " <> show x <> " = " <> show y
  show (CVarEqB x y) = "VB " <> show x <> " = " <> show y
  show (CVarNEqB x y) = "VN " <> show x <> " = ¬ " <> show y
  show (CVarBindF x n) = "BF " <> show x <> " = " <> show n
  show (CVarBindB x n) = "BB " <> show x <> " = " <> show n
  show (CMulF aV bV cV) = "MF " <> show aV <> " * " <> show bV <> " = " <> show cV