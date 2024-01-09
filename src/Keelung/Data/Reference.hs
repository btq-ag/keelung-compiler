{-# LANGUAGE DeriveAnyClass #-}
{-# HLINT ignore "Use list comprehension" #-}
{-# LANGUAGE DeriveGeneric #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Keelung.Data.Reference
  ( Ref (..),
    RefF (..),
    RefB (..),
    RefU (..),
    refUVar,
  )
where

import Control.DeepSeq (NFData)
import GHC.Generics (Generic)
import Keelung.Compiler.Util
import Keelung.Syntax

-- | For representing mixed variables in constraints
data Ref
  = -- | Field variable
    F RefF
  | -- | Boolean variable
    B RefB
  deriving (Eq, Ord, Generic, NFData)

instance Show Ref where
  show (F x) = show x
  show (B x) = show x

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
    RefUBit RefU Int
  deriving (Eq, Ord, Generic, NFData)

instance Show RefB where
  show (RefBO x) = "BO" ++ show x
  show (RefBI x) = "BI" ++ show x
  show (RefBP x) = "BP" ++ show x
  show (RefBX x) = "B" ++ show x
  show (RefUBit x i) = show x ++ "[" ++ show i ++ "]"

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
  deriving (Eq, Generic, NFData)

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

-- | "Larger" RefUs gets to be the root in UnionFind:
--    1. compare the kind of RefUs: RefUI = RefUP > RefUO > RefUX
--    2. compare the width of RefUs: larger width > smaller width
--    3. compare the var of RefUs: smaller var > larger var
instance Ord RefU where
  (RefUI width1 var1) `compare` (RefUI width2 var2) = compare width1 width2 <> compare var2 var1
  (RefUI width1 var1) `compare` (RefUP width2 var2) = compare width1 width2 <> compare var2 var1 <> GT
  (RefUI _ _) `compare` _ = GT
  (RefUP width1 var1) `compare` (RefUI width2 var2) = compare width1 width2 <> compare var2 var1 <> LT
  (RefUP width1 var1) `compare` (RefUP width2 var2) = compare width1 width2 <> compare var2 var1
  (RefUP _ _) `compare` _ = GT
  (RefUO _ _) `compare` (RefUI _ _) = LT
  (RefUO _ _) `compare` (RefUP _ _) = LT
  (RefUO width1 var1) `compare` (RefUO width2 var2) = compare width1 width2 <> compare var2 var1
  (RefUO _ _) `compare` _ = GT
  (RefUX _ _) `compare` (RefUI _ _) = LT
  (RefUX _ _) `compare` (RefUP _ _) = LT
  (RefUX _ _) `compare` (RefUO _ _) = LT
  (RefUX width1 var1) `compare` (RefUX width2 var2) = compare width1 width2 <> compare var2 var1

refUVar :: RefU -> Var
refUVar (RefUO _ var) = var
refUVar (RefUI _ var) = var
refUVar (RefUP _ var) = var
refUVar (RefUX _ var) = var
