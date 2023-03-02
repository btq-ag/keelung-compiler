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
    -- addOccurrencesWithPolyG,
    -- removeOccurrencesWithPolyG,
    -- addOccurrences,
    -- removeOccurrences,
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
  )
where

import Control.DeepSeq (NFData)
import Data.Bifunctor (first)
import Data.Field.Galois (GaloisField)
import Data.Map.Strict qualified as Map
import GHC.Generics (Generic)
import Keelung.Compiler.Optimize.MinimizeConstraints.UnionFind (UnionFind)
import Keelung.Compiler.Optimize.MinimizeConstraints.UnionFind qualified as UnionFind
import Keelung.Compiler.Relocated qualified as Relocated
import Keelung.Constraint.R1CS qualified as Constraint
import Keelung.Data.PolyG (PolyG)
import Keelung.Data.PolyG qualified as PolyG
import Keelung.Data.Polynomial (Poly)
import Keelung.Data.Polynomial qualified as Poly
import Keelung.Data.VarGroup (toSubscript)
import Keelung.Syntax
import Keelung.Syntax.Counters

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

data RefB = RefBO Var | RefBI Var | RefBP Var | RefUBit Width RefU Int | RefB Var
  deriving (Eq, Ord, Generic, NFData)

instance Show RefB where
  show (RefBO x) = "BO" ++ show x
  show (RefBI x) = "BI" ++ show x
  show (RefBP x) = "BP" ++ show x
  show (RefB x) = "B" ++ show x
  show (RefUBit _ x i) = show x ++ "[" ++ show i ++ "]"

data RefF = RefFO Var | RefFI Var | RefFP Var | RefBtoRefF RefB | RefF Var
  deriving (Eq, Ord, Generic, NFData)

instance Show RefF where
  show (RefFO x) = "FO" ++ show x
  show (RefFI x) = "FI" ++ show x
  show (RefFP x) = "FP" ++ show x
  show (RefF x) = "F" ++ show x
  show (RefBtoRefF x) = show x

data RefU = RefUO Width Var | RefUI Width Var | RefUP Width Var | RefBtoRefU RefB | RefU Width Var
  deriving (Eq, Ord, Generic, NFData)

instance Show RefU where
  show ref = case ref of
    RefUO w x -> "UO" ++ toSubscript w ++ show x
    RefUI w x -> "UI" ++ toSubscript w ++ show x
    RefUP w x -> "UP" ++ toSubscript w ++ show x
    RefU w x -> "U" ++ toSubscript w ++ show x
    RefBtoRefU x -> show x

--------------------------------------------------------------------------------

-- pinnedRefF :: RefF -> Bool
-- pinnedRefF (RefFI _) = True
-- pinnedRefF (RefFO _) = True
-- pinnedRefF (RefBtoRefF ref) = pinnedRefB ref
-- pinnedRefF _ = False

-- pinnedRefB :: RefB -> Bool
-- pinnedRefB (RefBI _) = True
-- pinnedRefB (RefBO _) = True
-- pinnedRefB (RefUBit _ ref _) = pinnedRefU ref
-- pinnedRefB _ = False

-- pinnedRefU :: RefU -> Bool
-- pinnedRefU (RefUI _ _) = True
-- pinnedRefU (RefUO _ _) = True
-- pinnedRefU (RefBtoRefU ref) = pinnedRefB ref
-- pinnedRefU _ = False

--------------------------------------------------------------------------------

reindexRefF :: Counters -> RefF -> Var
reindexRefF counters (RefFO x) = reindex counters OfOutput OfField x
reindexRefF counters (RefFI x) = reindex counters OfPublicInput OfField x
reindexRefF counters (RefFP x) = reindex counters OfPrivateInput OfField x
reindexRefF counters (RefF x) = reindex counters OfIntermediate OfField x
reindexRefF counters (RefBtoRefF x) = reindexRefB counters x

reindexRefB :: Counters -> RefB -> Var
reindexRefB counters (RefBO x) = reindex counters OfOutput OfBoolean x
reindexRefB counters (RefBI x) = reindex counters OfPublicInput OfBoolean x
reindexRefB counters (RefBP x) = reindex counters OfPrivateInput OfBoolean x
reindexRefB counters (RefB x) = reindex counters OfIntermediate OfBoolean x
reindexRefB counters (RefUBit w x i) =
  let i' = i `mod` w
   in case x of
        RefUO _ x' -> reindex counters OfOutput (OfUIntBinRep w) x' + i'
        RefUI _ x' -> reindex counters OfPublicInput (OfUIntBinRep w) x' + i'
        RefUP _ x' -> reindex counters OfPrivateInput (OfUIntBinRep w) x' + i'
        RefU _ x' -> reindex counters OfIntermediate (OfUIntBinRep w) x' + i'
        RefBtoRefU x' ->
          if i' == 0
            then reindexRefB counters x'
            else error "reindexRefB: RefUBit"

reindexRefU :: Counters -> RefU -> Var
reindexRefU counters (RefUO w x) = reindex counters OfOutput (OfUInt w) x
reindexRefU counters (RefUI w x) = reindex counters OfPublicInput (OfUInt w) x
reindexRefU counters (RefUP w x) = reindex counters OfPrivateInput (OfUInt w) x
reindexRefU counters (RefU w x) = reindex counters OfIntermediate (OfUInt w) x
reindexRefU counters (RefBtoRefU x) = reindexRefB counters x

--------------------------------------------------------------------------------

fromPolyF :: Integral n => Counters -> PolyG RefF n -> Either n (Poly n)
fromPolyF counters poly = case PolyG.view poly of
  PolyG.Monomial constant (var, coeff) -> Poly.buildEither constant [(reindexRefF counters var, coeff)]
  PolyG.Binomial constant (var1, coeff1) (var2, coeff2) -> Poly.buildEither constant [(reindexRefF counters var1, coeff1), (reindexRefF counters var2, coeff2)]
  PolyG.Polynomial constant xs -> Poly.buildEither constant (map (first (reindexRefF counters)) (Map.toList xs))

fromPolyB :: Integral n => Counters -> PolyG RefB n -> Either n (Poly n)
fromPolyB counters poly = case PolyG.view poly of
  PolyG.Monomial constant (var, coeff) -> Poly.buildEither constant [(reindexRefB counters var, coeff)]
  PolyG.Binomial constant (var1, coeff1) (var2, coeff2) -> Poly.buildEither constant [(reindexRefB counters var1, coeff1), (reindexRefB counters var2, coeff2)]
  PolyG.Polynomial constant xs -> Poly.buildEither constant (map (first (reindexRefB counters)) (Map.toList xs))

fromPolyU :: Integral n => Counters -> PolyG RefU n -> Either n (Poly n)
fromPolyU counters poly = case PolyG.view poly of
  PolyG.Monomial constant (var, coeff) -> Poly.buildEither constant [(reindexRefU counters var, coeff)]
  PolyG.Binomial constant (var1, coeff1) (var2, coeff2) -> Poly.buildEither constant [(reindexRefU counters var1, coeff1), (reindexRefU counters var2, coeff2)]
  PolyG.Polynomial constant xs -> Poly.buildEither constant (map (first (reindexRefU counters)) (Map.toList xs))

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

-- | Substitutes variables in a polynomial.
--   Returns 'Nothing' if nothing changed else returns the substituted polynomial and the list of substituted variables.
substPolyG :: (GaloisField n, Integral n, Ord ref, Show ref) => UnionFind ref n -> PolyG ref n -> Maybe (Either n (PolyG ref n), [ref])
substPolyG ctx poly = do
  let (c, xs) = PolyG.viewAsMap poly
  case Map.foldlWithKey' (substPolyG_ ctx) (False, Left c, []) xs of
    (False, _, _) -> Nothing -- nothing changed
    (True, Left constant, substitutedRefs) -> Just (Left constant, substitutedRefs) -- the polynomial has been reduced to a constant
    (True, Right poly', substitutedRefs) -> Just (Right poly', substitutedRefs)

substPolyG_ :: (Integral n, Ord ref, Show ref, GaloisField n) => UnionFind ref n -> (Bool, Either n (PolyG ref n), [ref]) -> ref -> n -> (Bool, Either n (PolyG ref n), [ref])
substPolyG_ ctx (changed, accPoly, substitutedRefs) ref coeff = case UnionFind.parentOf ctx ref of
  Nothing ->
    -- ref is already a root
    case accPoly of
      Left c -> (changed, PolyG.singleton c (ref, coeff), substitutedRefs)
      Right xs -> (changed, PolyG.insert 0 (ref, coeff) xs, substitutedRefs)
  Just (Nothing, intercept) ->
    -- ref = intercept
    let substitutedRefs' = ref : substitutedRefs -- add ref to substitutedRefs
     in case accPoly of
          Left c -> (True, Left (intercept * coeff + c), substitutedRefs')
          Right accPoly' -> (True, Right $ PolyG.addConstant (intercept * coeff) accPoly', substitutedRefs')
  Just (Just (slope, root), intercept) ->
    if root == ref
      then
        if slope == 1 && intercept == 0
          then -- ref = root, nothing changed
          case accPoly of
            Left c -> (changed, PolyG.singleton c (ref, coeff), substitutedRefs)
            Right xs -> (changed, PolyG.insert 0 (ref, coeff) xs, substitutedRefs)
          else error "[ panic ] Invalid relation in UnionFind: ref = slope * root + intercept, but slope /= 1 || intercept /= 0"
      else
        let substitutedRefs' = ref : substitutedRefs
         in case accPoly of
              -- ref = slope * root + intercept
              Left c -> (True, PolyG.singleton (intercept * coeff + c) (root, slope * coeff), substitutedRefs')
              Right accPoly' -> (True, PolyG.insert (intercept * coeff) (root, slope * coeff) accPoly', substitutedRefs')

-- let (isAlreadyRoot, (result, intercept)) = UnionFind.lookup ref ctx
--  in if isAlreadyRoot
--       then case xs of
--         Left c -> (changed, Right $ PolyG.singleton c (ref, coeff), substitutedRefs)
--         Right xs' -> (changed, Right $ PolyG.insert 0 (ref, coeff) xs', substitutedRefs)
--       else case result of
--         Nothing ->
--           -- ref = intercept
--           let substitutedRefs' = ref : substitutedRefs
--            in case xs of
--                 Left c -> (changed, Left (intercept + c), substitutedRefs')
--                 Right xs' -> (True, Right $ PolyG.insert (intercept * coeff) (ref, 1) xs', substitutedRefs')
--         Just (slope, root) ->
--           let substitutedRefs' = if root == ref then substitutedRefs else ref : substitutedRefs
--            in case xs of
--                 -- ref = slope * root + intercept
--                 Left c -> (changed, Right $ PolyG.singleton (intercept * coeff + c) (root, slope * coeff), substitutedRefs')
--                 Right xs' -> (True, Right $ PolyG.insert (intercept * coeff) (root, slope * coeff) xs', substitutedRefs')

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

-- addOccurrencesWithPolyG :: Ord ref => PolyG ref n -> Map ref Int -> Map ref Int
-- addOccurrencesWithPolyG = addOccurrences . PolyG.vars

-- addOccurrences :: Ord ref => [ref] -> Map ref Int -> Map ref Int
-- addOccurrences = flip $ foldl (\occurrences ref -> Map.insertWith (+) ref 1 occurrences)

-- removeOccurrencesWithPolyG :: Ord ref => PolyG ref n -> Map ref Int -> Map ref Int
-- removeOccurrencesWithPolyG = removeOccurrences . PolyG.vars

-- removeOccurrences :: Ord ref => [ref] -> Map ref Int -> Map ref Int
-- removeOccurrences = flip $ foldl (flip (Map.adjust (\count -> pred count `max` 0)))