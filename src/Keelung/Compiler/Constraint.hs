{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveFunctor #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use list comprehension" #-}

module Keelung.Compiler.Constraint
  ( RefF (..),
    RefB (..),
    RefU (..),
    reindexRefF,
    reindexRefB,
    reindexRefU,
    Constraint (..),
    cAddB,
    cAddF,
    cVarEqU,
    cVarBindU,
    cMulB,
    cMulF,
    cMulU,
    cMulSimpleB,
    cMulSimpleF,
    cNEqF,
    cNEqU,
    fromConstraint,
    ConstraintSystem (..),
    fromConstraintSystem,
  )
where

import Data.Bifunctor (first)
import Data.Field.Galois (GaloisField)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Keelung.Compiler.Relocated as Relocated
import Keelung.Constraint.Polynomial (Poly)
import qualified Keelung.Constraint.Polynomial as Poly
import qualified Keelung.Constraint.R1CS as Constraint
import Keelung.Syntax.Counters
import Keelung.Types

fromConstraint :: Integral n => Counters -> Constraint n -> Relocated.Constraint n
fromConstraint counters (CAddB as) = Relocated.CAdd (fromPolyB_ counters as)
fromConstraint counters (CAddF as) = Relocated.CAdd (fromPolyF_ counters as)
fromConstraint counters (CVarEqU x y) = case Poly.buildEither 0 [(reindexRefU counters x, 1), (reindexRefU counters y, -1)] of
  Left _ -> error "CVarEqU: two variables are the same"
  Right xs -> Relocated.CAdd xs
fromConstraint counters (CVarBindU x n) = Relocated.CAdd (Poly.bind (reindexRefU counters x) n)
fromConstraint counters (CMulF as bs cs) =
  Relocated.CMul
    (fromPolyF_ counters as)
    (fromPolyF_ counters bs)
    ( case cs of
        Left n -> Left n
        Right xs -> fromPolyF counters xs
    )
fromConstraint counters (CMulB as bs cs) =
  Relocated.CMul
    (fromPolyB_ counters as)
    (fromPolyB_ counters bs)
    ( case cs of
        Left n -> Left n
        Right xs -> fromPolyB counters xs
    )
fromConstraint counters (CMulU as bs cs) =
  Relocated.CMul
    (fromPolyU_ counters as)
    (fromPolyU_ counters bs)
    ( case cs of
        Left n -> Left n
        Right xs -> fromPolyU counters xs
    )
fromConstraint counters (CNEqF x y m) = Relocated.CNEq (Constraint.CNEQ (Left (reindexRefF counters x)) (Left (reindexRefF counters y)) (reindexRefF counters m))
fromConstraint counters (CNEqU x y m) = Relocated.CNEq (Constraint.CNEQ (Left (reindexRefU counters x)) (Left (reindexRefU counters y)) (reindexRefU counters m))

--------------------------------------------------------------------------------

data RefB = RefBI Var | RefBO Var | RefB Var | RefUBit Width RefU Int
  deriving (Eq, Ord)

instance Show RefB where
  show (RefBI x) = "$BI" ++ show x
  show (RefBO x) = "$BO" ++ show x
  show (RefB x) = "$B" ++ show x
  show (RefUBit _ x i) = show x ++ "[" ++ show i ++ "]"

data RefF = RefFI Var | RefFO Var | RefF Var | RefBtoRefF RefB
  deriving (Eq, Ord)

instance Show RefF where
  show (RefFI x) = "$FI" ++ show x
  show (RefFO x) = "$FO" ++ show x
  show (RefF x) = "$F" ++ show x
  show (RefBtoRefF x) = show x

data RefU = RefUI Width Var | RefUO Width Var | RefU Width Var | RefBtoRefU RefB
  deriving (Eq, Ord)

instance Show RefU where
  show ref = case ref of
    RefUI w x -> "$UI" ++ toSubscript w ++ show x
    RefUO w x -> "$UO" ++ toSubscript w ++ show x
    RefU w x -> "$U" ++ toSubscript w ++ show x
    RefBtoRefU x -> show x
    where
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

--------------------------------------------------------------------------------

reindexRefF :: Counters -> RefF -> Var
reindexRefF counters (RefFI x) = reindex counters OfInput OfField x
reindexRefF counters (RefFO x) = reindex counters OfOutput OfField x
reindexRefF counters (RefF x) = reindex counters OfIntermediate OfField x
reindexRefF counters (RefBtoRefF x) = reindexRefB counters x

reindexRefB :: Counters -> RefB -> Var
reindexRefB counters (RefBI x) = reindex counters OfInput OfBoolean x
reindexRefB counters (RefBO x) = reindex counters OfOutput OfBoolean x
reindexRefB counters (RefB x) = reindex counters OfIntermediate OfBoolean x
reindexRefB counters (RefUBit w x i) =
  let i' = i `mod` w
   in case x of
        RefUI _ x' -> reindex counters OfInput (OfUIntBinRep w) x' + i'
        RefUO _ x' -> reindex counters OfOutput (OfUIntBinRep w) x' + i'
        RefU _ x' -> reindex counters OfIntermediate (OfUIntBinRep w) x' + i'
        RefBtoRefU x' ->
          if i' == 0
            then reindexRefB counters x'
            else error "reindexRefB: RefUBit"

reindexRefU :: Counters -> RefU -> Var
reindexRefU counters (RefUI w x) = reindex counters OfInput (OfUInt w) x
reindexRefU counters (RefUO w x) = reindex counters OfOutput (OfUInt w) x
reindexRefU counters (RefU w x) = reindex counters OfIntermediate (OfUInt w) x
reindexRefU counters (RefBtoRefU x) = reindexRefB counters x

--------------------------------------------------------------------------------

-- | Like Poly but with using Refs instead of Ints as variables
data Poly' ref n = Poly' n (Map ref n)
  deriving (Eq, Functor, Show, Ord)

buildPoly' :: (GaloisField n, Ord ref) => n -> [(ref, n)] -> Either n (Poly' ref n)
buildPoly' c xs =
  let result = Map.filter (/= 0) $ Map.fromListWith (+) xs
   in if Map.null result
        then Left c
        else Right (Poly' c result)

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
  = CAddF !(Poly' RefF n)
  | CAddB !(Poly' RefB n)
  | CVarEqU RefU RefU -- when x == y
  | CVarBindU RefU n -- when x = val
  | CMulF !(Poly' RefF n) !(Poly' RefF n) !(Either n (Poly' RefF n))
  | CMulB !(Poly' RefB n) !(Poly' RefB n) !(Either n (Poly' RefB n))
  | CMulU !(Poly' RefU n) !(Poly' RefU n) !(Either n (Poly' RefU n))
  | CNEqF RefF RefF RefF
  | CNEqU RefU RefU RefU

instance GaloisField n => Eq (Constraint n) where
  xs == ys = case (xs, ys) of
    (CAddF x, CAddF y) -> x == y
    (CAddB x, CAddB y) -> x == y
    (CVarEqU x y, CVarEqU u v) -> (x == u && y == v) || (x == v && y == u)
    (CVarBindU x y, CVarBindU u v) -> x == u && y == v
    (CMulF x y z, CMulF u v w) ->
      (x == u && y == v || x == v && y == u) && z == w
    (CMulB x y z, CMulB u v w) ->
      (x == u && y == v || x == v && y == u) && z == w
    (CMulU x y z, CMulU u v w) ->
      (x == u && y == v || x == v && y == u) && z == w
    (CNEqF x y z, CNEqF u v w) ->
      (x == u && y == v || x == v && y == u) && z == w
    (CNEqU x y z, CNEqU u v w) ->
      (x == u && y == v || x == v && y == u) && z == w
    _ -> False

instance Functor Constraint where
  fmap f (CAddF x) = CAddF (fmap f x)
  fmap f (CAddB x) = CAddB (fmap f x)
  fmap _ (CVarEqU x y) = CVarEqU x y
  fmap f (CVarBindU x y) = CVarBindU x (f y)
  fmap f (CMulF x y (Left z)) = CMulF (fmap f x) (fmap f y) (Left (f z))
  fmap f (CMulF x y (Right z)) = CMulF (fmap f x) (fmap f y) (Right (fmap f z))
  fmap f (CMulB x y (Left z)) = CMulB (fmap f x) (fmap f y) (Left (f z))
  fmap f (CMulB x y (Right z)) = CMulB (fmap f x) (fmap f y) (Right (fmap f z))
  fmap f (CMulU x y (Left z)) = CMulU (fmap f x) (fmap f y) (Left (f z))
  fmap f (CMulU x y (Right z)) = CMulU (fmap f x) (fmap f y) (Right (fmap f z))
  fmap _ (CNEqF x y z) = CNEqF x y z
  fmap _ (CNEqU x y z) = CNEqU x y z

-- | Smart constructor for the CAddB constraint
cAddB :: GaloisField n => n -> [(RefB, n)] -> [Constraint n]
cAddB !c !xs = case buildPoly' c xs of
  Left _ -> []
  Right xs' -> [CAddB xs']

-- | Smart constructor for the CAddF constraint
cAddF :: GaloisField n => n -> [(RefF, n)] -> [Constraint n]
cAddF !c !xs = case buildPoly' c xs of
  Left _ -> []
  Right xs' -> [CAddF xs']

-- | Smart constructor for the CVarEqU constraint
cVarEqU :: GaloisField n => RefU -> RefU -> [Constraint n]
cVarEqU x y = if x == y then [] else [CVarEqU x y]

-- | Smart constructor for the cVarBindU constraint
cVarBindU :: GaloisField n => RefU -> n -> [Constraint n]
cVarBindU x n = [CVarBindU x n]

cMulSimple :: GaloisField n => (Poly' ref n -> Poly' ref n -> Either n (Poly' ref n) -> Constraint n) -> ref -> ref -> ref -> [Constraint n]
cMulSimple ctor !x !y !z =
  [ ctor (Poly' 0 (Map.singleton x 1)) (Poly' 0 (Map.singleton y 1)) (Right (Poly' 0 (Map.singleton z 1)))
  ]

cMulSimpleF :: GaloisField n => RefF -> RefF -> RefF -> [Constraint n]
cMulSimpleF = cMulSimple CMulF

cMulSimpleB :: GaloisField n => RefB -> RefB -> RefB -> [Constraint n]
cMulSimpleB = cMulSimple CMulB

-- | Smart constructor for the CMul constraint
cMul ::
  (GaloisField n, Ord ref) =>
  (Poly' ref n -> Poly' ref n -> Either n (Poly' ref n) -> Constraint n) ->
  (n, [(ref, n)]) ->
  (n, [(ref, n)]) ->
  (n, [(ref, n)]) ->
  [Constraint n]
cMul ctor (a, xs) (b, ys) (c, zs) = case ( do
                                             xs' <- buildPoly' a xs
                                             ys' <- buildPoly' b ys
                                             return $ ctor xs' ys' (buildPoly' c zs)
                                         ) of
  Left _ -> []
  Right result -> [result]

-- | Smart constructor for the CMulF constraint
cMulF :: GaloisField n => (n, [(RefF, n)]) -> (n, [(RefF, n)]) -> (n, [(RefF, n)]) -> [Constraint n]
cMulF = cMul CMulF

-- | Smart constructor for the CMulB constraint
cMulB :: GaloisField n => (n, [(RefB, n)]) -> (n, [(RefB, n)]) -> (n, [(RefB, n)]) -> [Constraint n]
cMulB = cMul CMulB

-- | Smart constructor for the CMulU constraint
cMulU :: GaloisField n => (n, [(RefU, n)]) -> (n, [(RefU, n)]) -> (n, [(RefU, n)]) -> [Constraint n]
cMulU = cMul CMulU

-- | Smart constructor for the CNEq constraint
cNEqF :: GaloisField n => RefF -> RefF -> RefF -> [Constraint n]
cNEqF x y m = [CNEqF x y m]

cNEqU :: GaloisField n => RefU -> RefU -> RefU -> [Constraint n]
cNEqU x y m = [CNEqU x y m]

instance (GaloisField n, Integral n) => Show (Constraint n) where
  show (CAddF xs) = "AF " <> show xs <> " = 0"
  show (CAddB xs) = "AB " <> show xs <> " = 0"
  show (CVarEqU x y) = "VU " <> show x <> " = " <> show y
  show (CVarBindU x n) = "BU " <> show x <> " = " <> show n
  show (CMulF aV bV cV) = "MF " <> show aV <> " * " <> show bV <> " = " <> show cV
  show (CMulB aV bV cV) = "MB " <> show aV <> " * " <> show bV <> " = " <> show cV
  show (CMulU aV bV cV) = "MU " <> show aV <> " * " <> show bV <> " = " <> show cV
  show (CNEqF x y m) = "QF " <> show x <> " " <> show y <> " " <> show m
  show (CNEqU x y m) = "QU " <> show x <> " " <> show y <> " " <> show m

--------------------------------------------------------------------------------

-- | A constraint system is a collection of constraints
data ConstraintSystem n = ConstraintSystem
  { csCounters :: !Counters,
    csVarEqU :: [(RefU, RefU)], -- when x == y
    csVarBindU :: [(RefU, n)], -- when x = val
    csAddF :: [Poly' RefF n],
    csAddB :: [Poly' RefB n],
    csMulF :: [(Poly' RefF n, Poly' RefF n, Either n (Poly' RefF n))],
    csMulB :: [(Poly' RefB n, Poly' RefB n, Either n (Poly' RefB n))],
    csMulU :: [(Poly' RefU n, Poly' RefU n, Either n (Poly' RefU n))],
    csNEqF :: [(RefF, RefF, RefF)],
    csNEqU :: [(RefU, RefU, RefU)]
  }

fromConstraintSystem :: (GaloisField n, Integral n) => ConstraintSystem n -> Relocated.RelocatedConstraintSystem n
fromConstraintSystem cs =
  Relocated.RelocatedConstraintSystem
    { Relocated.csCounters = counters,
      Relocated.csConstraints = varEqUs <> varBindUs <> addFs <> addBs <> mulFs <> mulBs <> mulUs <> nEqFs <> nEqUs
    }
  where
    counters = csCounters cs
    uncurry3 f (a, b, c) = f a b c
    varEqUs = Set.fromList $ map (fromConstraint counters . uncurry CVarEqU) $ csVarEqU cs
    varBindUs = Set.fromList $ map (fromConstraint counters . uncurry CVarBindU) $ csVarBindU cs
    addFs = Set.fromList $ map (fromConstraint counters . CAddF) $ csAddF cs
    addBs = Set.fromList $ map (fromConstraint counters . CAddB) $ csAddB cs
    mulFs = Set.fromList $ map (fromConstraint counters . uncurry3 CMulF) $ csMulF cs
    mulBs = Set.fromList $ map (fromConstraint counters . uncurry3 CMulB) $ csMulB cs
    mulUs = Set.fromList $ map (fromConstraint counters . uncurry3 CMulU) $ csMulU cs
    nEqFs = Set.fromList $ map (\(x, y, m) -> Relocated.CNEq (Constraint.CNEQ (Left (reindexRefF counters x)) (Left (reindexRefF counters y)) (reindexRefF counters m))) $ csNEqF cs
    nEqUs = Set.fromList $ map (\(x, y, m) -> Relocated.CNEq (Constraint.CNEQ (Left (reindexRefU counters x)) (Left (reindexRefU counters y)) (reindexRefU counters m))) $ csNEqU cs