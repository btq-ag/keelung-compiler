{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}

module Keelung.Compiler.Constraint2
  ( RefF (..),
    RefB (..),
    RefU (..),
    reindexRefF,
    reindexRefB,
    reindexRefU,
    Constraint,
    cadd,
    cmul,
    cmulSimple,
    cneq,
    ConstraintSystem,
    fromConstraint,
  )
where

import Control.DeepSeq (NFData)
import Data.Bifunctor (first)
import Data.Field.Galois (GaloisField)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import GHC.Generics (Generic)
import qualified Keelung.Compiler.Constraint as Constraint
import Keelung.Compiler.Syntax.Untyped (Width)
import Keelung.Constraint.Polynomial (Poly)
import qualified Keelung.Constraint.Polynomial as Poly
import Keelung.Constraint.R1C (R1C (..))
import qualified Keelung.Constraint.R1CS as Constraint
import Keelung.Field
import Keelung.Syntax.BinRep (BinReps)
import Keelung.Syntax.Counters
import Keelung.Syntax.VarCounters
import Keelung.Types

fromConstraint :: Integral n => Counters -> Constraint n -> Constraint.Constraint n
fromConstraint _ (CAdd p) = Constraint.CAdd p
fromConstraint _ (CMul p q r) = Constraint.CMul p q r
fromConstraint counters (CMulF as bs cs) =
  Constraint.CMul
    (fromPolyF_ counters as)
    (fromPolyF_ counters bs)
    ( case cs of
        Left n -> Left n
        Right xs -> fromPolyF counters xs
    )
fromConstraint counters (CMulB as bs cs) =
  Constraint.CMul
    (fromPolyB_ counters as)
    (fromPolyB_ counters bs)
    ( case cs of
        Left n -> Left n
        Right xs -> fromPolyB counters xs
    )
fromConstraint counters (CMulU as bs cs) =
  Constraint.CMul
    (fromPolyU_ counters as)
    (fromPolyU_ counters bs)
    ( case cs of
        Left n -> Left n
        Right xs -> fromPolyU counters xs
    )
fromConstraint counters (CNEq x y m) = Constraint.CNEq (Constraint.CNEQ (Left x) (Left y) (reindexRefF counters m))

--------------------------------------------------------------------------------

data RefB = RefBI Var | RefBO Var | RefB Var
  deriving (Generic, NFData, Eq, Ord)

instance Show RefB where
  show (RefBI x) = "$BI" ++ show x
  show (RefBO x) = "$BO" ++ show x
  show (RefB x) = "$B" ++ show x

data RefF = RefFI Var | RefFO Var | RefF Var | FromRefB RefB
  deriving (Generic, NFData, Eq, Ord)

instance Show RefF where
  show (RefFI x) = "$FI" ++ show x
  show (RefFO x) = "$FO" ++ show x
  show (RefF x) = "$F" ++ show x
  show (FromRefB x) = show x

data RefU = RefUI Width Var | RefUO Width Var | RefU Width Var
  deriving (Generic, NFData, Eq, Ord)

instance Show RefU where
  show (RefUI w x) = "$UI[" ++ show w ++ "]" ++ show x
  show (RefUO w x) = "$UO[" ++ show w ++ "]" ++ show x
  show (RefU w x) = "$U[" ++ show w ++ "]" ++ show x

reindexRefF :: Counters -> RefF -> Var
reindexRefF counters (RefFI x) = reindex counters OfInput OfField x
reindexRefF counters (RefFO x) = reindex counters OfOutput OfField x
reindexRefF counters (RefF x) = reindex counters OfIntermediate OfField x
reindexRefF counters (FromRefB x) = reindexRefB counters x

reindexRefB :: Counters -> RefB -> Var
reindexRefB counters (RefBI x) = reindex counters OfInput OfBoolean x
reindexRefB counters (RefBO x) = reindex counters OfOutput OfBoolean x
reindexRefB counters (RefB x) = reindex counters OfIntermediate OfBoolean x

reindexRefU :: Counters -> RefU -> Var
reindexRefU counters (RefUI w x) = reindex counters OfInput (OfUInt w) x
reindexRefU counters (RefUO w x) = reindex counters OfOutput (OfUInt w) x
reindexRefU counters (RefU w x) = reindex counters OfIntermediate (OfUInt w) x

--------------------------------------------------------------------------------

data Poly' ref n = Poly' n (Map ref n)
  deriving (Generic, NFData, Eq, Functor, Show, Ord)

fromPolyF :: Integral n => Counters -> Poly' RefF n -> Either n (Poly n)
fromPolyF counters (Poly' c xs) = Poly.buildEither c (map (first (reindexRefF counters)) (Map.toList xs))

fromPolyB :: Integral n => Counters -> Poly' RefB n -> Either n (Poly n)
fromPolyB counters (Poly' c xs) = Poly.buildEither c (map (first (reindexRefB counters)) (Map.toList xs))

fromPolyU :: Integral n => Counters -> Poly' RefU n -> Either n (Poly n)
fromPolyU counters (Poly' c xs) = Poly.buildEither c (map (first (reindexRefU counters)) (Map.toList xs))

fromPolyF_ :: Integral n => Counters -> Poly' RefF n -> Poly n
fromPolyF_ counters xs = case fromPolyF counters xs of
  Left _ -> error "[ panic ] fromPolyF_: Left"
  Right p -> p

fromPolyB_ :: Integral n => Counters -> Poly' RefB n -> Poly n
fromPolyB_ counters xs = case fromPolyB counters xs of
  Left _ -> error "[ panic ] fromPolyB_: Left"
  Right p -> p

fromPolyU_ :: Integral n => Counters -> Poly' RefU n -> Poly n
fromPolyU_ counters xs = case fromPolyU counters xs of
  Left _ -> error "[ panic ] fromPolyU_: Left"
  Right p -> p

--------------------------------------------------------------------------------

-- | Constraint
--      CAdd: 0 = c + c₀x₀ + c₁x₁ ... cₙxₙ
--      CMul: ax * by = c or ax * by = cz
--      CNEq: if (x - y) == 0 then m = 0 else m = recip (x - y)
data Constraint n
  = CAdd !(Poly n)
  | CMul !(Poly n) !(Poly n) !(Either n (Poly n))
  | CMulF !(Poly' RefF n) !(Poly' RefF n) !(Either n (Poly' RefF n))
  | CMulB !(Poly' RefB n) !(Poly' RefB n) !(Either n (Poly' RefB n))
  | CMulU !(Poly' RefU n) !(Poly' RefU n) !(Either n (Poly' RefU n))
  | CNEq Var Var RefF
  deriving (Generic, NFData)

instance GaloisField n => Eq (Constraint n) where
  xs == ys = case (xs, ys) of
    (CAdd x, CAdd y) -> x == y
    (CMul x y z, CMul u v w) ->
      (x == u && y == v || x == v && y == u) && z == w
    (CMulF x y z, CMulF u v w) ->
      (x == u && y == v || x == v && y == u) && z == w
    (CNEq x y z, CNEq u v w) ->
      (x == u && y == v || x == v && y == u) && z == w
    _ -> False

instance Functor Constraint where
  fmap f (CAdd x) = CAdd (fmap f x)
  -- fmap f (CAdd2 t x) = CAdd2 t (fmap f x)
  fmap f (CMul x y (Left z)) = CMul (fmap f x) (fmap f y) (Left (f z))
  fmap f (CMul x y (Right z)) = CMul (fmap f x) (fmap f y) (Right (fmap f z))
  fmap f (CMulF x y (Left z)) = CMulF (fmap f x) (fmap f y) (Left (f z))
  fmap f (CMulF x y (Right z)) = CMulF (fmap f x) (fmap f y) (Right (fmap f z))
  fmap f (CMulB x y (Left z)) = CMulB (fmap f x) (fmap f y) (Left (f z))
  fmap f (CMulB x y (Right z)) = CMulB (fmap f x) (fmap f y) (Right (fmap f z))
  fmap f (CMulU x y (Left z)) = CMulU (fmap f x) (fmap f y) (Left (f z))
  fmap f (CMulU x y (Right z)) = CMulU (fmap f x) (fmap f y) (Right (fmap f z))
  fmap _ (CNEq x y z) = CNEq x y z

-- | Smart constructor for the CAdd constraint
cadd :: GaloisField n => n -> [(Var, n)] -> [Constraint n]
cadd !c !xs = map CAdd $ case Poly.buildEither c xs of
  Left _ -> []
  Right xs' -> [xs']

cmulSimple :: GaloisField n => Var -> Var -> Var -> [Constraint n]
cmulSimple !x !y !z = [CMul (Poly.singleVar x) (Poly.singleVar y) (Poly.buildEither 0 [(z, 1)])]

-- | Smart constructor for the CMul constraint
cmul :: GaloisField n => (n, [(Var, n)]) -> (n, [(Var, n)]) -> (n, [(Var, n)]) -> [Constraint n]
cmul (a, xs) (b, ys) (c, zs) = case ( do
                                        xs' <- Poly.buildEither a xs
                                        ys' <- Poly.buildEither b ys
                                        return $ CMul xs' ys' (Poly.buildEither c zs)
                                    ) of
  Left _ -> []
  Right result -> [result]

-- | Smart constructor for the CMulF constraint
cMulF :: GaloisField n => (n, [(RefF, n)]) -> (n, [(RefF, n)]) -> (n, [(RefF, n)]) -> [Constraint n]
cMulF (a, xs) (b, ys) (c, zs) =
  [ CMulF
      (Poly' a (Map.fromList xs))
      (Poly' b (Map.fromList ys))
      (if null zs then Left c else Right (Poly' c (Map.fromList zs)))
  ]

-- | Smart constructor for the CMulB constraint
cMulB :: GaloisField n => (n, [(RefB, n)]) -> (n, [(RefB, n)]) -> (n, [(RefB, n)]) -> [Constraint n]
cMulB (a, xs) (b, ys) (c, zs) =
  [ CMulB
      (Poly' a (Map.fromList xs))
      (Poly' b (Map.fromList ys))
      (if null zs then Left c else Right (Poly' c (Map.fromList zs)))
  ]

-- | Smart constructor for the CMulU constraint
cMulU :: GaloisField n => (n, [(RefU, n)]) -> (n, [(RefU, n)]) -> (n, [(RefU, n)]) -> [Constraint n]
cMulU (a, xs) (b, ys) (c, zs) =
  [ CMulU
      (Poly' a (Map.fromList xs))
      (Poly' b (Map.fromList ys))
      (if null zs then Left c else Right (Poly' c (Map.fromList zs)))
  ]


-- | Smart constructor for the CNEq constraint
cneq :: GaloisField n => Var -> Var -> RefF -> [Constraint n]
cneq x y m = [CNEq x y m]

instance (GaloisField n, Integral n) => Show (Constraint n) where
  show (CAdd xs) = "A " <> show xs <> " = 0"
  -- show (CAdd2 t xs) = "A " <> show t <> " " <> show xs <> " = 0"
  show (CMul aV bV cV) = "M " <> show (R1C (Right aV) (Right bV) cV)
  show (CMulF aV bV cV) = "MF " <> show aV <> " * " <> show bV <> " = " <> show cV
  show (CMulB aV bV cV) = "MB " <> show aV <> " * " <> show bV <> " = " <> show cV
  show (CMulU aV bV cV) = "MU " <> show aV <> " * " <> show bV <> " = " <> show cV
  show (CNEq x y m) = "Q " <> show x <> " " <> show y <> " " <> show m

instance GaloisField n => Ord (Constraint n) where
  {-# SPECIALIZE instance Ord (Constraint GF181) #-}

  -- CMul
  compare (CMul aV bV cV) (CMul aX bX cX) = compare (aV, bV, cV) (aX, bX, cX)
  compare _ CMul {} = LT
  compare CMul {} _ = GT
  -- CMulF
  compare (CMulF aV bV cV) (CMulF aX bX cX) = compare (aV, bV, cV) (aX, bX, cX)
  compare _ CMulF {} = LT
  compare CMulF {} _ = GT
  -- CMulB
  compare (CMulB aV bV cV) (CMulB aX bX cX) = compare (aV, bV, cV) (aX, bX, cX)
  compare _ CMulB {} = LT
  compare CMulB {} _ = GT
  -- CMulU
  compare (CMulU aV bV cV) (CMulU aX bX cX) = compare (aV, bV, cV) (aX, bX, cX)
  compare _ CMulU {} = LT
  compare CMulU {} _ = GT
  -- CAdd
  compare (CAdd xs) (CAdd ys) = compare xs ys
  -- compare (CAdd2 {}) (CAdd {}) = LT
  -- compare (CAdd {}) (CAdd2 {}) = GT
  -- compare (CAdd2 t xs) (CAdd2 u ys) =
  --   if t == u
  --     then compare xs ys
  --     else error "[ panic ] CAdd type mismatch"
  -- CNEq
  compare CNEq {} CNEq {} = EQ
  compare CNEq {} _ = LT
  compare _ CNEq {} = GT

--------------------------------------------------------------------------------

-- | Constraint System
data ConstraintSystem n = ConstraintSystem
  { -- | Constraints
    csConstraints :: !(Set (Constraint n)),
    -- | Binary representation of Number input variables
    csNumBinReps :: BinReps,
    -- | Binary representation of custom output variables
    csCustomBinReps :: BinReps,
    csVarCounters :: !VarCounters,
    csCounters :: Counters
  }
  deriving (Eq, Generic, NFData)