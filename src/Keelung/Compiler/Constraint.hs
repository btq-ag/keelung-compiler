{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# HLINT ignore "Use list comprehension" #-}
{-# LANGUAGE DeriveGeneric #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Keelung.Compiler.Constraint
  ( RefF (..),
    RefB (..),
    RefU (..),
    reindexRefF,
    reindexRefB,
    reindexRefU,
    Constraint (..),
    addOccurrencesWithPolyG,
    removeOccurrencesWithPolyG,
    addOccurrences,
    removeOccurrences,
    substPolyG,
    cAddF,
    cAddB,
    cAddU,
    cVarEqF,
    cVarEqB,
    cVarEqU,
    cVarBindF,
    cVarBindB,
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
    relocateConstraintSystem,
    sizeOfConstraintSystem,
  )
where

import Control.DeepSeq (NFData)
import Data.Bifunctor (first)
import Data.Field.Galois (GaloisField)
import Data.IntMap.Strict qualified as IntMap
import Data.Map.Merge.Strict qualified as Map
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe qualified as Maybe
import Data.Sequence qualified as Seq
import GHC.Generics (Generic)
import Keelung.Compiler.Optimize.MinimizeConstraints.UnionFind (UnionFind)
import Keelung.Compiler.Optimize.MinimizeConstraints.UnionFind qualified as UnionFind
import Keelung.Compiler.Relocated qualified as Relocated
import Keelung.Constraint.Polynomial (Poly)
import Keelung.Constraint.Polynomial qualified as Poly
import Keelung.Constraint.R1CS qualified as Constraint
import Keelung.Data.Bindings (showList')
import Keelung.Data.PolyG (PolyG)
import Keelung.Data.PolyG qualified as PolyG
import Keelung.Data.Struct (Struct (..))
import Keelung.Syntax.Counters
import Keelung.Types

fromConstraint :: Integral n => Counters -> Constraint n -> Relocated.Constraint n
fromConstraint counters (CAddB as) = Relocated.CAdd (fromPolyB_ counters as)
fromConstraint counters (CAddF as) = Relocated.CAdd (fromPolyF_ counters as)
fromConstraint counters (CAddU as) = Relocated.CAdd (fromPolyU_ counters as)
fromConstraint counters (CVarEqF x y) = case Poly.buildEither 0 [(reindexRefF counters x, 1), (reindexRefF counters y, -1)] of
  Left _ -> error "CVarEqF: two variables are the same"
  Right xs -> Relocated.CAdd xs
fromConstraint counters (CVarEqB x y) = case Poly.buildEither 0 [(reindexRefB counters x, 1), (reindexRefB counters y, -1)] of
  Left _ -> error "CVarEqB: two variables are the same"
  Right xs -> Relocated.CAdd xs
fromConstraint counters (CVarEqU x y) = case Poly.buildEither 0 [(reindexRefU counters x, 1), (reindexRefU counters y, -1)] of
  Left _ -> error "CVarEqU: two variables are the same"
  Right xs -> Relocated.CAdd xs
fromConstraint counters (CVarBindF x n) = Relocated.CAdd (Poly.bind (reindexRefF counters x) n)
fromConstraint counters (CVarBindB x n) = Relocated.CAdd (Poly.bind (reindexRefB counters x) n)
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

data RefB = RefBO Var | RefBI Var | RefB Var | RefUBit Width RefU Int
  deriving (Eq, Ord, Generic, NFData)

instance Show RefB where
  show (RefBI x) = "BI" ++ show x
  show (RefBO x) = "BO" ++ show x
  show (RefB x) = "B" ++ show x
  show (RefUBit _ x i) = show x ++ "[" ++ show i ++ "]"

data RefF = RefFO Var | RefFI Var | RefBtoRefF RefB | RefF Var
  deriving (Eq, Ord, Generic, NFData)

instance Show RefF where
  show (RefFI x) = "FI" ++ show x
  show (RefFO x) = "FO" ++ show x
  show (RefF x) = "F" ++ show x
  show (RefBtoRefF x) = show x

data RefU = RefUO Width Var | RefUI Width Var | RefBtoRefU RefB | RefU Width Var
  deriving (Eq, Ord, Generic, NFData)

instance Show RefU where
  show ref = case ref of
    RefUI w x -> "UI" ++ toSubscript w ++ show x
    RefUO w x -> "UO" ++ toSubscript w ++ show x
    RefU w x -> "U" ++ toSubscript w ++ show x
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

pinnedRefF :: RefF -> Bool
pinnedRefF (RefFI _) = True
pinnedRefF (RefFO _) = True
pinnedRefF (RefBtoRefF ref) = pinnedRefB ref
pinnedRefF _ = False

pinnedRefB :: RefB -> Bool
pinnedRefB (RefBI _) = True
pinnedRefB (RefBO _) = True
pinnedRefB (RefUBit _ ref _) = pinnedRefU ref
pinnedRefB _ = False

pinnedRefU :: RefU -> Bool
pinnedRefU (RefUI _ _) = True
pinnedRefU (RefUO _ _) = True
pinnedRefU (RefBtoRefU ref) = pinnedRefB ref
pinnedRefU _ = False

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

fromPolyF :: Integral n => Counters -> PolyG RefF n -> Either n (Poly n)
fromPolyF counters poly = let (c, xs) = PolyG.view poly in Poly.buildEither c (map (first (reindexRefF counters)) xs)

fromPolyB :: Integral n => Counters -> PolyG RefB n -> Either n (Poly n)
fromPolyB counters poly = let (c, xs) = PolyG.view poly in Poly.buildEither c (map (first (reindexRefB counters)) xs)

fromPolyU :: Integral n => Counters -> PolyG RefU n -> Either n (Poly n)
fromPolyU counters poly = let (c, xs) = PolyG.view poly in Poly.buildEither c (map (first (reindexRefU counters)) xs)

fromPolyF_ :: Integral n => Counters -> PolyG RefF n -> Poly n
fromPolyF_ counters xs = case fromPolyF counters xs of
  Left _ -> error "[ panic ] fromPolyF_: Left"
  Right p -> p

fromPolyB_ :: Integral n => Counters -> PolyG RefB n -> Poly n
fromPolyB_ counters xs = case fromPolyB counters xs of
  Left _ -> error "[ panic ] fromPolyB_: Left"
  Right p -> p

fromPolyU_ :: Integral n => Counters -> PolyG RefU n -> Poly n
fromPolyU_ counters xs = case fromPolyU counters xs of
  Left _ -> error "[ panic ] fromPolyU_: Left"
  Right p -> p

--------------------------------------------------------------------------------

-- -- | Normalize a polynomial by substituting roots
-- -- for the variables that appear in the polynomial.
-- -- substPoly :: (GaloisField n, Integral n) => UnionFind RefF -> PolyG RefF n -> Maybe (PolyG RefF n, UnionFind RefF)
-- substPolyG :: (GaloisField n, Integral n, Ord ref) => UnionFind ref n -> PolyG ref n -> Maybe (PolyG ref n, UnionFind ref n, [ref])
-- substPolyG ctx poly = do
--   let (c, xs) = PolyG.viewAsMap poly
--   case Map.foldlWithKey' substPolyG_ (False, ctx, Nothing, []) xs of
--     (False, _, _, _) -> Nothing
--     (True, _, Nothing, _) -> Nothing
--     (True, ctx', Just poly', substitutedRefs) -> Just (PolyG.addConstant c poly', ctx', substitutedRefs)

-- -- substPolyG :: (Integral n, GaloisField n) => (Bool, UnionFind RefF, Map RefF n) -> RefF -> n -> (Bool, UnionFind RefF, Map RefF n)
-- substPolyG_ :: (Integral n, Ord ref) => (Bool, UnionFind ref n, Maybe (PolyG ref n), [ref]) -> ref -> n -> (Bool, UnionFind ref n, Maybe (PolyG ref n), [ref])
-- substPolyG_ (changed, ctx, xs, substitutedRefs) ref coeff = case UnionFind.findMaybe ref ctx of
--   Nothing -> case xs of
--     Nothing -> (changed, ctx, Just $ PolyG.singleton 0 (ref, coeff), substitutedRefs)
--     Just xs' -> (changed, ctx, Just $ PolyG.insert 0 (ref, coeff) xs', substitutedRefs)
--   Just ((slope, root, intercept), ctx') ->
--     let substitutedRefs' = if root == ref then substitutedRefs else ref : substitutedRefs
--      in case xs of
--           -- ref = slope * root + intercept
--           Nothing -> (changed, ctx, Just $ PolyG.singleton (intercept * coeff) (root, slope * coeff), substitutedRefs')
--           Just xs' -> (True, ctx', Just $ PolyG.insert (intercept * coeff) (root, slope * coeff) xs', substitutedRefs')

substPolyG :: (GaloisField n, Integral n, Ord ref) => UnionFind ref n -> PolyG ref n -> Maybe (PolyG ref n, [ref])
substPolyG ctx poly = do
  let (c, xs) = PolyG.viewAsMap poly
  case Map.foldlWithKey' (substPolyG_ ctx) (False, Left c, []) xs of
    (False, _, _) -> Nothing
    (True, Left _constant, _) -> Nothing
    (True, Right poly', substitutedRefs) -> Just (poly', substitutedRefs)

-- substPolyG :: (Integral n, GaloisField n) => (Bool, UnionFind RefF, Map RefF n) -> RefF -> n -> (Bool, UnionFind RefF, Map RefF n)
substPolyG_ :: (Integral n, Ord ref) => UnionFind ref n -> (Bool, Either n (PolyG ref n), [ref]) -> ref -> n -> (Bool, Either n (PolyG ref n), [ref])
substPolyG_ ctx (changed, xs, substitutedRefs) ref coeff =
  let (isAlreadyRoot, (result, intercept)) = UnionFind.lookup ref ctx
   in if isAlreadyRoot
        then case xs of
          Left c -> (changed, Right $ PolyG.singleton c (ref, coeff), substitutedRefs)
          Right xs' -> (changed, Right $ PolyG.insert 0 (ref, coeff) xs', substitutedRefs)
        else case result of
          Nothing ->
            -- ref = intercept
            let substitutedRefs' = ref : substitutedRefs
             in case xs of
                  Left c -> (changed, Left (intercept + c), substitutedRefs')
                  Right xs' -> (True, Right $ PolyG.insert (intercept * coeff) (ref, 1) xs', substitutedRefs')
          Just (slope, root) ->
            let substitutedRefs' = if root == ref then substitutedRefs else ref : substitutedRefs
             in case xs of
                  -- ref = slope * root + intercept
                  Left c -> (changed, Right $ PolyG.singleton (intercept * coeff + c) (root, slope * coeff), substitutedRefs')
                  Right xs' -> (True, Right $ PolyG.insert (intercept * coeff) (root, slope * coeff) xs', substitutedRefs')

-- let (isAlreadyRoot, slope, root, intercept) = UnionFind.lookup ref ctx
--  in if isAlreadyRoot
--       then case xs of
--         Nothing -> (changed, Just $ PolyG.singleton 0 (ref, coeff), substitutedRefs)
--         Just xs' -> (changed, Just $ PolyG.insert 0 (ref, coeff) xs', substitutedRefs)
--       else
--         let substitutedRefs' = if root == ref then substitutedRefs else ref : substitutedRefs
--          in case xs of
--               -- ref = slope * root + intercept
--               Nothing -> (changed, Just $ PolyG.singleton (intercept * coeff) (root, slope * coeff), substitutedRefs')
--               Just xs' -> (True, Just $ PolyG.insert (intercept * coeff) (root, slope * coeff) xs', substitutedRefs')

--------------------------------------------------------------------------------

-- | Constraint
--      CAdd: 0 = c + c₀x₀ + c₁x₁ ... cₙxₙ
--      CMul: ax * by = c or ax * by = cz
--      CNEq: if (x - y) == 0 then m = 0 else m = recip (x - y)
data Constraint n
  = CAddF !(PolyG RefF n)
  | CAddB !(PolyG RefB n)
  | CAddU !(PolyG RefU n)
  | CVarEqF RefF RefF -- when x == y
  | CVarEqB RefB RefB -- when x == y
  | CVarEqU RefU RefU -- when x == y
  | CVarBindF RefF n -- when x = val
  | CVarBindB RefB n -- when x = val
  | CVarBindU RefU n -- when x = val
  | CMulF !(PolyG RefF n) !(PolyG RefF n) !(Either n (PolyG RefF n))
  | CMulB !(PolyG RefB n) !(PolyG RefB n) !(Either n (PolyG RefB n))
  | CMulU !(PolyG RefU n) !(PolyG RefU n) !(Either n (PolyG RefU n))
  | CNEqF RefF RefF RefF
  | CNEqU RefU RefU RefU

instance GaloisField n => Eq (Constraint n) where
  xs == ys = case (xs, ys) of
    (CAddF x, CAddF y) -> x == y
    (CAddB x, CAddB y) -> x == y
    (CVarEqU x y, CVarEqU u v) -> (x == u && y == v) || (x == v && y == u)
    (CVarBindU x y, CVarBindU u v) -> x == u && y == v
    (CVarBindF x y, CVarBindF u v) -> x == u && y == v
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
  fmap f (CAddU x) = CAddU (fmap f x)
  fmap _ (CVarEqF x y) = CVarEqF x y
  fmap _ (CVarEqB x y) = CVarEqB x y
  fmap _ (CVarEqU x y) = CVarEqU x y
  fmap f (CVarBindF x y) = CVarBindF x (f y)
  fmap f (CVarBindB x y) = CVarBindB x (f y)
  fmap f (CVarBindU x y) = CVarBindU x (f y)
  fmap f (CMulF x y (Left z)) = CMulF (fmap f x) (fmap f y) (Left (f z))
  fmap f (CMulF x y (Right z)) = CMulF (fmap f x) (fmap f y) (Right (fmap f z))
  fmap f (CMulB x y (Left z)) = CMulB (fmap f x) (fmap f y) (Left (f z))
  fmap f (CMulB x y (Right z)) = CMulB (fmap f x) (fmap f y) (Right (fmap f z))
  fmap f (CMulU x y (Left z)) = CMulU (fmap f x) (fmap f y) (Left (f z))
  fmap f (CMulU x y (Right z)) = CMulU (fmap f x) (fmap f y) (Right (fmap f z))
  fmap _ (CNEqF x y z) = CNEqF x y z
  fmap _ (CNEqU x y z) = CNEqU x y z

-- | Smart constructor for the CAddF constraint
cAddF :: GaloisField n => n -> [(RefF, n)] -> [Constraint n]
cAddF !c !xs = case PolyG.build c xs of
  Left _ -> []
  Right xs' -> [CAddF xs']

-- | Smart constructor for the CAddB constraint
cAddB :: GaloisField n => n -> [(RefB, n)] -> [Constraint n]
cAddB !c !xs = case PolyG.build c xs of
  Left _ -> []
  Right xs' -> [CAddB xs']

-- | Smart constructor for the CAddU constraint
cAddU :: GaloisField n => n -> [(RefU, n)] -> [Constraint n]
cAddU !c !xs = case PolyG.build c xs of
  Left _ -> []
  Right xs' -> [CAddU xs']

-- | Smart constructor for the CVarEqF constraint
cVarEqF :: GaloisField n => RefF -> RefF -> [Constraint n]
cVarEqF x y = if x == y then [] else [CVarEqF x y]

-- | Smart constructor for the CVarEqB constraint
cVarEqB :: GaloisField n => RefB -> RefB -> [Constraint n]
cVarEqB x y = if x == y then [] else [CVarEqB x y]

-- | Smart constructor for the CVarEqU constraint
cVarEqU :: GaloisField n => RefU -> RefU -> [Constraint n]
cVarEqU x y = if x == y then [] else [CVarEqU x y]

-- | Smart constructor for the cVarBindF constraint
cVarBindF :: GaloisField n => RefF -> n -> [Constraint n]
cVarBindF x n = [CVarBindF x n]

-- | Smart constructor for the cVarBindB constraint
cVarBindB :: GaloisField n => RefB -> n -> [Constraint n]
cVarBindB x n = [CVarBindB x n]

-- | Smart constructor for the cVarBindU constraint
cVarBindU :: GaloisField n => RefU -> n -> [Constraint n]
cVarBindU x n = [CVarBindU x n]

cMulSimple :: (GaloisField n, Ord ref) => (PolyG ref n -> PolyG ref n -> Either n (PolyG ref n) -> Constraint n) -> ref -> ref -> ref -> [Constraint n]
cMulSimple ctor !x !y !z = case ( do
                                    xs' <- PolyG.build 0 [(x, 1)]
                                    ys' <- PolyG.build 0 [(y, 1)]
                                    return $ ctor xs' ys' (PolyG.build 0 [(z, 1)])
                                ) of
  Left _ -> []
  Right result -> [result]

cMulSimpleF :: GaloisField n => RefF -> RefF -> RefF -> [Constraint n]
cMulSimpleF = cMulSimple CMulF

cMulSimpleB :: GaloisField n => RefB -> RefB -> RefB -> [Constraint n]
cMulSimpleB = cMulSimple CMulB

-- | Smart constructor for the CMul constraint
cMul ::
  (GaloisField n, Ord ref) =>
  (PolyG ref n -> PolyG ref n -> Either n (PolyG ref n) -> Constraint n) ->
  (n, [(ref, n)]) ->
  (n, [(ref, n)]) ->
  (n, [(ref, n)]) ->
  [Constraint n]
cMul ctor (a, xs) (b, ys) (c, zs) = case ( do
                                             xs' <- PolyG.build a xs
                                             ys' <- PolyG.build b ys
                                             return $ ctor xs' ys' (PolyG.build c zs)
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
  show (CAddU xs) = "AU " <> show xs <> " = 0"
  show (CVarEqF x y) = "VF " <> show x <> " = " <> show y
  show (CVarEqB x y) = "VB " <> show x <> " = " <> show y
  show (CVarEqU x y) = "VU " <> show x <> " = " <> show y
  show (CVarBindF x n) = "BF " <> show x <> " = " <> show n
  show (CVarBindB x n) = "BB " <> show x <> " = " <> show n
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
    csUseNewOptimizer :: Bool,
    -- for counting the occurences of variables in constraints (excluding the ones that are in UnionFind)
    csOccurrenceF :: !(Map RefF Int),
    csOccurrenceB :: !(Map RefB Int),
    csOccurrenceU :: !(Map RefU Int),
    -- when x = val
    csVarBindF :: Map RefF n,
    csVarBindB :: Map RefB n,
    csVarBindU :: Map RefU n,
    -- when x == y (UnionFind)
    csVarEqF :: UnionFind RefF n,
    csVarEqB :: [(RefB, RefB)],
    csVarEqU :: [(RefU, RefU)],
    -- addative constraints
    csAddF :: [PolyG RefF n],
    csAddB :: [PolyG RefB n],
    csAddU :: [PolyG RefU n],
    -- multiplicative constraints
    csMulF :: [(PolyG RefF n, PolyG RefF n, Either n (PolyG RefF n))],
    csMulB :: [(PolyG RefB n, PolyG RefB n, Either n (PolyG RefB n))],
    csMulU :: [(PolyG RefU n, PolyG RefU n, Either n (PolyG RefU n))],
    -- constraints for computing equality
    csNEqF :: Map (RefF, RefF) RefF,
    csNEqU :: Map (RefU, RefU) RefU
  }
  deriving (Eq, Generic, NFData)

instance (GaloisField n, Integral n) => Show (ConstraintSystem n) where
  show cs =
    "ConstraintSystem {\n"
      <> showVarBindF
      <> showVarBindB
      <> showVarBindU
      <> showVarEqF
      <> showVarEqB
      <> showVarEqU
      <> showAddF
      <> showAddB
      <> showAddU
      <> showMulF
      <> showMulB
      <> showMulU
      <> showNEqF
      <> showNEqU
      <> showBooleanConstraints
      <> showBinRepConstraints
      <> showOccurrencesF
      <> showOccurrencesB
      <> showOccurrencesU
      <> showVariables
      <> "}"
    where
      counters = csCounters cs
      -- sizes of constraint groups
      totalBinRepConstraintSize = getBinRepConstraintSize counters
      booleanConstraintSize = getBooleanConstraintSize counters

      adapt :: String -> [a] -> (a -> String) -> String
      adapt name xs f =
        let size = length xs
         in if size == 0
              then ""
              else "  " <> name <> " (" <> show size <> "):\n\n" <> unlines (map (("    " <>) . f) xs) <> "\n"

      -- Boolean constraints
      showBooleanConstraints =
        if booleanConstraintSize == 0
          then ""
          else
            "  Boolean constriants ("
              <> show booleanConstraintSize
              <> "):\n\n"
              <> unlines (map ("    " <>) (prettyBooleanConstraints counters))
              <> "\n"

      -- BinRep constraints
      showBinRepConstraints =
        if totalBinRepConstraintSize == 0
          then ""
          else
            "  Binary representation constriants ("
              <> show totalBinRepConstraintSize
              <> "):\n\n"
              <> unlines (map ("    " <>) (prettyBinRepConstraints counters))
              <> "\n"

      showVarEqF = "  VarEqF:\n" <> indent (indent (show (csVarEqF cs)))
      showVarEqB = adapt "VarEqB" (csVarEqB cs) $ \(var, val) -> show var <> " = " <> show val
      showVarEqU = adapt "VarEqU" (csVarEqU cs) $ \(var, val) -> show var <> " = " <> show val

      showVarBindU = adapt "VarBindU" (Map.toList $ csVarBindU cs) $ \(var, val) -> show var <> " = " <> show val
      showVarBindF = adapt "VarBindF" (Map.toList $ csVarBindF cs) $ \(var, val) -> show var <> " = " <> show val
      showVarBindB = adapt "VarBindB" (Map.toList $ csVarBindB cs) $ \(var, val) -> show var <> " = " <> show val

      showAddF = adapt "AddF" (csAddF cs) show
      showAddB = adapt "AddB" (csAddB cs) show
      showAddU = adapt "AddU" (csAddU cs) show

      showMulF = adapt "MulF" (csMulF cs) $ \(a, b, c) -> show a <> " * " <> show b <> " = " <> show c
      showMulB = adapt "MulB" (csMulB cs) $ \(a, b, c) -> show a <> " * " <> show b <> " = " <> show c
      showMulU = adapt "MulU" (csMulU cs) $ \(a, b, c) -> show a <> " * " <> show b <> " = " <> show c

      showNEqF = adapt "NEqF" (Map.toList $ csNEqF cs) $ \((x, y), m) -> "NEqF " <> show x <> " " <> show y <> " " <> show m
      showNEqU = adapt "NEqU" (Map.toList $ csNEqU cs) $ \((x, y), m) -> "NEqF " <> show x <> " " <> show y <> " " <> show m

      showOccurrencesF =
        if Map.null $ csOccurrenceF cs
          then ""
          else "  OccruencesF:\n  " <> indent (showList' (map (\(var, n) -> show var <> ": " <> show n) (Map.toList $ csOccurrenceF cs)))
      showOccurrencesB =
        if Map.null $ csOccurrenceB cs
          then ""
          else "  OccruencesB:\n  " <> indent (showList' (map (\(var, n) -> show var <> ": " <> show n) (Map.toList $ csOccurrenceB cs)))
      showOccurrencesU =
        if Map.null $ csOccurrenceU cs
          then ""
          else "  OccruencesU:\n  " <> indent (showList' (map (\(var, n) -> show var <> ": " <> show n) (Map.toList $ csOccurrenceU cs)))

      showVariables :: String
      showVariables =
        let totalSize = getTotalCount counters
            padRight4 s = s <> replicate (4 - length s) ' '
            padLeft12 n = replicate (12 - length (show n)) ' ' <> show n
            formLine typ = padLeft12 (getCount OfOutput typ counters) <> "  " <> padLeft12 (getCount OfInput typ counters) <> "      " <> padLeft12 (getCount OfIntermediate typ counters)
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
            uint w = "\n    UInt" <> padRight4 (toSubscript w) <> formLine (OfUInt w)
            showUInts (Counters o _ _ _ _) =
              let xs = map uint (IntMap.keys (structU o))
               in if null xs then "\n    UInt            none          none              none" else mconcat xs
         in if totalSize == 0
              then ""
              else
                "  Variables ("
                  <> show totalSize
                  <> "):\n"
                  <> "                  output         input      intermediate\n"
                  <> "\n    Field   "
                  <> formLine OfField
                  <> "\n    Boolean "
                  <> formLine OfBoolean
                  <> showUInts counters
                  <> "\n"

relocateConstraintSystem :: (GaloisField n, Integral n) => ConstraintSystem n -> Relocated.RelocatedConstraintSystem n
relocateConstraintSystem cs =
  Relocated.RelocatedConstraintSystem
    { Relocated.csCounters = counters,
      Relocated.csConstraints =
        varEqFs
          <> varEqBs
          <> varEqUs
          <> varBindFs
          <> varBindBs
          <> varBindUs
          <> addFs
          <> addBs
          <> addUs
          <> mulFs
          <> mulBs
          <> mulUs
          <> nEqFs
          <> nEqUs
    }
  where
    counters = csCounters cs
    uncurry3 f (a, b, c) = f a b c

    -- remove the constraint if it containts any variable that is not pinned and have occurrence count of 0
    shouldRemoveF occurrences var =
      csUseNewOptimizer cs
        && case Map.lookup var occurrences of
          Nothing -> not (pinnedRefF var)
          Just 0 -> not (pinnedRefF var)
          Just _ -> False

    fromUnionFindF _occurrences (var1, (Nothing, c)) = 
      Just $ fromConstraint counters (CVarBindF var1 c)
      -- if shouldRemoveF occurrences var1 || shouldRemoveF occurrences var2
      --   then Nothing
      --   else Just $ fromConstraint counters (CVarEqF var1 var2)
    fromUnionFindF occurrences (var1, (Just (1, var2), 0)) =
      if shouldRemoveF occurrences var1 || shouldRemoveF occurrences var2
        then Nothing
        else Just $ fromConstraint counters (CVarEqF var1 var2)
    fromUnionFindF occurrences (var1, (Just (slope2, var2), intercept2)) =
      case PolyG.build intercept2 [(var1, -1), (var2, slope2)] of
        Left _ -> Nothing
        Right poly ->
          if shouldRemoveF occurrences var1 || shouldRemoveF occurrences var2
            then Nothing
            else Just $ fromConstraint counters (CAddF poly)

    varEqFs = Seq.fromList $ Maybe.mapMaybe (fromUnionFindF (csOccurrenceF cs)) $ Map.toList $ UnionFind.toMap $ csVarEqF cs

    varEqBs = Seq.fromList $ map (fromConstraint counters . uncurry CVarEqB) $ csVarEqB cs
    varEqUs = Seq.fromList $ map (fromConstraint counters . uncurry CVarEqU) $ csVarEqU cs
    varBindFs = Seq.fromList $ map (fromConstraint counters . uncurry CVarBindF) $ Map.toList $ csVarBindF cs
    varBindBs = Seq.fromList $ map (fromConstraint counters . uncurry CVarBindB) $ Map.toList $ csVarBindB cs
    varBindUs = Seq.fromList $ map (fromConstraint counters . uncurry CVarBindU) $ Map.toList $ csVarBindU cs
    addFs = Seq.fromList $ map (fromConstraint counters . CAddF) $ csAddF cs
    addBs = Seq.fromList $ map (fromConstraint counters . CAddB) $ csAddB cs
    addUs = Seq.fromList $ map (fromConstraint counters . CAddU) $ csAddU cs
    mulFs = Seq.fromList $ map (fromConstraint counters . uncurry3 CMulF) $ csMulF cs
    mulBs = Seq.fromList $ map (fromConstraint counters . uncurry3 CMulB) $ csMulB cs
    mulUs = Seq.fromList $ map (fromConstraint counters . uncurry3 CMulU) $ csMulU cs
    nEqFs = Seq.fromList $ map (\((x, y), m) -> Relocated.CNEq (Constraint.CNEQ (Left (reindexRefF counters x)) (Left (reindexRefF counters y)) (reindexRefF counters m))) $ Map.toList $ csNEqF cs
    nEqUs = Seq.fromList $ map (\((x, y), m) -> Relocated.CNEq (Constraint.CNEQ (Left (reindexRefU counters x)) (Left (reindexRefU counters y)) (reindexRefU counters m))) $ Map.toList $ csNEqU cs

addOccurrencesWithPolyG :: Ord ref => PolyG ref n -> Map ref Int -> Map ref Int
addOccurrencesWithPolyG poly occurrences =
  Map.merge
    (Map.traverseMissing (\_ count -> return count)) -- do nothing when it's not in the polynomial
    (Map.traverseMissing (\_ _ -> return 1)) -- set the occurrence count to 1 when it's not in the occurrences map
    (Map.zipWithAMatched (\_ count _ -> return (succ count))) -- increment the occurrence count when it's present in both
    occurrences
    (snd (PolyG.viewAsMap poly))

addOccurrences :: Ord ref => [ref] -> Map ref Int -> Map ref Int
addOccurrences = flip $ foldl (\occurrences ref -> Map.insertWith (+) ref 1 occurrences)

removeOccurrencesWithPolyG :: Ord ref => PolyG ref n -> Map ref Int -> Map ref Int
removeOccurrencesWithPolyG poly occurrences =
  Map.merge
    (Map.traverseMissing (\_ count -> return count)) -- do nothing when it's not in the polynomial
    (Map.traverseMissing (\_ _ -> return 1)) -- do nothing when it's not in the occurrences map
    (Map.zipWithAMatched (\_ count _ -> return (pred count `max` 0))) -- increment the occurrence count when it's present in both
    occurrences
    (snd (PolyG.viewAsMap poly))

removeOccurrences :: Ord ref => [ref] -> Map ref Int -> Map ref Int
removeOccurrences = flip $ foldl (flip (Map.adjust (\count -> pred count `max` 0)))

sizeOfConstraintSystem :: ConstraintSystem n -> Int
sizeOfConstraintSystem cs =
  UnionFind.size (csVarEqF cs)
    + length (csVarEqB cs)
    + length (csVarEqU cs)
    + length (csVarBindF cs)
    + length (csVarBindB cs)
    + length (csVarBindU cs)
    + length (csAddF cs)
    + length (csAddB cs)
    + length (csAddU cs)
    + length (csMulF cs)
    + length (csMulB cs)
    + length (csMulU cs)
    + length (csNEqF cs)
    + length (csNEqU cs)