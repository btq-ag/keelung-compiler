{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}

module Keelung.Data.VarGroup where

import Control.DeepSeq (NFData)
import Data.Bifunctor (Bifunctor (..))
import Data.Field.Galois (GaloisField)
import Data.Foldable (toList)
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.IntSet (IntSet)
import Data.IntSet qualified as IntSet
import Data.Maybe qualified as Maybe
import Data.Serialize (Serialize)
import Data.Validation
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import GHC.Generics (Generic)
import Keelung.Compiler.Util hiding (Witness)
import Keelung.Data.N (N (N))
import Keelung.Data.Struct
import Keelung.Data.U (U (..))
import Keelung.Syntax (Width)
import Keelung.Syntax.Counters

--------------------------------------------------------------------------------

class HasF a f | a -> f where
  getF :: a -> f
  putF :: f -> a -> a
  modifyF :: (f -> f) -> a -> a
  modifyF f x = putF (f (getF x)) x

instance HasF (Struct f b u) f where
  getF (Struct f _ _) = f
  putF f (Struct _ b u) = Struct f b u
  modifyF func (Struct f b u) = Struct (func f) b u

instance HasF PinnedCounter Int where
  getF (PinnedCounter f _ _) = f
  putF f (PinnedCounter _ b u) = PinnedCounter f b u
  modifyF func (PinnedCounter f b u) = PinnedCounter (func f) b u

instance HasF IntermediateCounter Int where
  getF (IntermediateCounter f _ _) = f
  putF f (IntermediateCounter _ b u) = IntermediateCounter f b u
  modifyF func (IntermediateCounter f b u) = IntermediateCounter (func f) b u

--------------------------------------------------------------------------------

class HasB a b | a -> b where
  getB :: a -> b
  putB :: b -> a -> a
  modifyB :: (b -> b) -> a -> a
  modifyB f x = putB (f (getB x)) x

instance HasB (Struct f b u) b where
  getB (Struct _ b _) = b
  putB b (Struct f _ u) = Struct f b u
  modifyB func (Struct f b u) = Struct f (func b) u

instance HasB PinnedCounter Int where
  getB (PinnedCounter _ b _) = b
  putB b (PinnedCounter f _ u) = PinnedCounter f b u
  modifyB func (PinnedCounter f b u) = PinnedCounter f (func b) u

instance HasB IntermediateCounter Int where
  getB (IntermediateCounter _ b _) = b
  putB b (IntermediateCounter f _ u) = IntermediateCounter f b u
  modifyB func (IntermediateCounter f b u) = IntermediateCounter f (func b) u

class HasU a u | a -> u where
  getUAll :: a -> IntMap u

  getU :: Width -> a -> Maybe u
  getU width = IntMap.lookup width . getUAll

  putUAll :: IntMap u -> a -> a

  putU :: Width -> u -> a -> a
  putU width u x = putUAll (IntMap.insert width u (getUAll x)) x

  modifyU :: Width -> u -> (u -> u) -> a -> a
  modifyU width empty' f x = case getU width x of
    Nothing -> putU width (f empty') x
    Just u -> putU width (f u) x

  modifyUAll :: (IntMap u -> IntMap u) -> a -> a
  modifyUAll f x = putUAll (f (getUAll x)) x

instance HasU (Struct f b u) u where
  getUAll (Struct _ _ u) = u
  putUAll u (Struct f b _) = Struct f b u

instance HasU PinnedCounter Int where
  getUAll (PinnedCounter _ _ u) = u
  putUAll u (PinnedCounter f b _) = PinnedCounter f b u

instance HasU IntermediateCounter Int where
  getUAll (IntermediateCounter _ _ u) = u
  putUAll u (IntermediateCounter f b _) = IntermediateCounter f b u

--------------------------------------------------------------------------------

data VarGroups n = VarGroups
  { ofO :: n,
    ofI :: n,
    ofP :: n,
    ofX :: n
  }
  deriving (Eq, Show, NFData, Generic, Functor)

instance (Serialize n) => Serialize (VarGroups n)

instance (Semigroup n) => Semigroup (VarGroups n) where
  VarGroups o1 i1 p1 x1 <> VarGroups o2 i2 p2 x2 =
    VarGroups (o1 <> o2) (i1 <> i2) (p1 <> p2) (x1 <> x2)

instance (Monoid n) => Monoid (VarGroups n) where
  mempty = VarGroups mempty mempty mempty mempty

--------------------------------------------------------------------------------

class HasO a o | a -> o where
  getO :: a -> o
  putO :: o -> a -> a
  modifyO :: (o -> o) -> a -> a
  modifyO f x = putO (f (getO x)) x

instance HasO (VarGroups n) n where
  getO (VarGroups o _ _ _) = o
  putO o (VarGroups _ i p x) = VarGroups o i p x

--------------------------------------------------------------------------------

class HasI a i | a -> i where
  getI :: a -> i
  putI :: i -> a -> a
  modifyI :: (i -> i) -> a -> a
  modifyI f x = putI (f (getI x)) x

instance HasI (VarGroups n) n where
  getI (VarGroups _ i _ _) = i
  putI i (VarGroups o _ p x) = VarGroups o i p x

--------------------------------------------------------------------------------

class HasP a p | a -> p where
  getP :: a -> p
  putP :: p -> a -> a
  modifyP :: (p -> p) -> a -> a
  modifyP f x = putP (f (getP x)) x

instance HasP (VarGroups n) n where
  getP (VarGroups _ _ p _) = p
  putP p (VarGroups o i _ x) = VarGroups o i p x

--------------------------------------------------------------------------------

class HasX a x | a -> x where
  getX :: a -> x
  putX :: x -> a -> a
  modifyX :: (x -> x) -> a -> a
  modifyX f x = putX (f (getX x)) x

instance HasX (VarGroups n) n where
  getX (VarGroups _ _ _ x) = x
  putX x (VarGroups o i p _) = VarGroups o i p x

--------------------------------------------------------------------------------

type Witness f b u = VarGroups (Struct (Vector f) (Vector b) (Vector u))

convertWitness :: (Integral a) => Witness a Bool U -> Witness Integer Integer Integer
convertWitness (VarGroups o i p x) = VarGroups (convertStruct o) (convertStruct i) (convertStruct p) (convertStruct x)
  where
    convertStruct :: (Integral a) => Struct (Vector a) (Vector Bool) (Vector U) -> Struct (Vector Integer) (Vector Integer) (Vector Integer)
    convertStruct (Struct f b us) = Struct (fmap toInteger f) (fmap (\val -> if val then 1 else 0) b) (IntMap.map (fmap uValue) us)

--------------------------------------------------------------------------------

type VarSet n = VarGroups (Struct IntSet IntSet IntSet)

instance {-# OVERLAPPING #-} Show (VarSet n) where
  show (VarGroups o i p x) =
    showList' $
      showStruct "O" o <> showStruct "I" i <> showStruct "P" p <> showStruct "X" x
    where
      showStruct :: String -> Struct IntSet IntSet IntSet -> [String]
      showStruct prefix (Struct f b u) =
        map (\var -> "B" <> prefix <> show var) (IntSet.toList b)
          <> map (\var -> "F" <> prefix <> show var) (IntSet.toList f)
          <> concatMap (\(width, xs) -> map (\var -> "U" <> toSubscript width <> prefix <> show var) (IntSet.toList xs)) (IntMap.toList u)

--------------------------------------------------------------------------------

-- | Data structure for interpreters
type Partial n = VarGroups (Struct (PartialBinding n) (PartialBinding Bool) (PartialBinding U))

-- | Expected number of bindings and actual bindings
type PartialBinding n = (Int, IntMap n)

instance {-# OVERLAPPING #-} (GaloisField n, Integral n) => Show (Partial n) where
  show (VarGroups o i p x) = showList' $ showStruct "O" o <> showStruct "I" i <> showStruct "P" p <> showStruct "" x
    where
      showPartialBinding :: (GaloisField n, Integral n) => String -> (Int, IntMap n) -> IntMap String
      showPartialBinding prefix (_size, bindings) = IntMap.mapWithKey (\k v -> prefix <> show k <> " := " <> show (N v)) bindings

      showPartialBindingB :: String -> (Int, IntMap Bool) -> IntMap String
      showPartialBindingB prefix (_size, bindings) = IntMap.mapWithKey (\k v -> prefix <> show k <> " := " <> show v) bindings

      showPartialBindingU :: String -> (Int, IntMap U) -> IntMap String
      showPartialBindingU prefix (_size, bindings) = IntMap.mapWithKey (\k v -> prefix <> show k <> " := " <> show v) bindings

      showStruct :: (GaloisField n, Integral n) => String -> Struct (PartialBinding n) (PartialBinding Bool) (PartialBinding U) -> [String]
      showStruct suffix (Struct f b u) =
        toList (showPartialBinding ("F" <> suffix) f)
          <> toList (showPartialBindingB ("B" <> suffix) b)
          <> concatMap (\(width, xs) -> toList (showPartialBindingU ("U" <> suffix <> toSubscript width) xs)) (IntMap.toList u)

-- | Convert a partial binding to a total binding, or return the variables that are not bound
toTotal :: Partial n -> Either (VarSet n) (Witness n Bool U)
toTotal (VarGroups o i p x) =
  toEither $
    VarGroups
      <$> first (\struct -> VarGroups struct mempty mempty mempty) (convertStruct o)
      <*> first (\struct -> VarGroups mempty struct mempty mempty) (convertStruct i)
      <*> first (\struct -> VarGroups mempty mempty struct mempty) (convertStruct p)
      <*> first (VarGroups mempty mempty mempty) (convertStruct x)
  where
    convertStruct ::
      Struct (PartialBinding n) (PartialBinding Bool) (PartialBinding U) ->
      Validation (Struct IntSet IntSet IntSet) (Struct (Vector n) (Vector Bool) (Vector U))
    convertStruct (Struct f b u) =
      Struct
        <$> first (\set -> Struct set mempty mempty) (toTotal' f)
        <*> first (\set -> Struct mempty set mempty) (toTotal' b)
        <*> first (Struct mempty mempty) (sequenceIntMap toTotal' u)

    sequenceIntMap :: (a -> Validation b c) -> IntMap a -> Validation (IntMap b) (IntMap c)
    sequenceIntMap f = sequenceA . IntMap.mapWithKey (\width xs -> first (IntMap.singleton width) (f xs))

emptyPartial :: Partial n
emptyPartial =
  VarGroups
    (Struct (0, mempty) (0, mempty) mempty)
    (Struct (0, mempty) (0, mempty) mempty)
    (Struct (0, mempty) (0, mempty) mempty)
    (Struct (0, mempty) (0, mempty) mempty)

partialIsEmpty :: (Eq n) => Partial n -> Bool
partialIsEmpty (VarGroups o i p x) = isEmptyStruct o && isEmptyStruct i && isEmptyStruct p && isEmptyStruct x
  where
    isEmptyStruct (Struct f b u) = f == (0, mempty) && b == (0, mempty) && IntMap.null u

toTotal' :: (Int, IntMap n) -> Validation IntSet (Vector n)
toTotal' (size, xs) =
  if IntMap.size xs < size
    then
      let completeIntSet = IntSet.fromDistinctAscList [0 .. size - 1]
       in Failure (IntSet.difference completeIntSet (IntMap.keysSet xs))
    else Success (Vector.fromList (toList xs))

restrictVars :: Partial n -> VarSet n -> Partial n
restrictVars (VarGroups o i p x) (VarGroups o' i' p' x') =
  VarGroups
    (restrictStruct o o')
    (restrictStruct i i')
    (restrictStruct p p')
    (restrictStruct x x')
  where
    restrictStruct :: Struct (PartialBinding n) (PartialBinding Bool) (PartialBinding U) -> Struct IntSet IntSet IntSet -> Struct (PartialBinding n) (PartialBinding Bool) (PartialBinding U)
    restrictStruct (Struct f b u) (Struct f' b' u') =
      Struct
        (restrict f f')
        (restrict b b')
        (IntMap.intersectionWith restrict u u')

    restrict :: (Int, IntMap n) -> IntSet -> (Int, IntMap n)
    restrict (size, xs) set = (size, IntMap.restrictKeys xs set)

----------------------------------------------------------------------------

instance HasO Counters PinnedCounter where
  getO = countOutput
  putO x counters = counters {countOutput = x}
  modifyO f counters = counters {countOutput = f (countOutput counters)}

instance HasI Counters PinnedCounter where
  getI = countPublicInput
  putI x counters = counters {countPublicInput = x}
  modifyI f counters = counters {countPublicInput = f (countOutput counters)}

instance HasP Counters PinnedCounter where
  getP = countPrivateInput
  putP x counters = counters {countPrivateInput = x}
  modifyP f counters = counters {countPrivateInput = f (countOutput counters)}

instance HasX Counters IntermediateCounter where
  getX = countIntermediate
  putX x counters = counters {countIntermediate = x}
  modifyX f counters = counters {countIntermediate = f (countIntermediate counters)}

instance HasF Counters (VarGroups Int) where
  getF counters = VarGroups (getF (getO counters)) (getF (getI counters)) (getF (getP counters)) (getF (getX counters))
  putF x counters =
    counters
      { countOutput = putF (getO x) (getO counters),
        countPublicInput = putF (getI x) (getI counters),
        countPrivateInput = putF (getP x) (getP counters),
        countIntermediate = putF (getX x) (getX counters)
      }

instance HasB Counters (VarGroups Int) where
  getB counters = VarGroups (getB (getO counters)) (getB (getI counters)) (getB (getP counters)) (getB (getX counters))
  putB x counters =
    counters
      { countOutput = putB (getO x) (getO counters),
        countPublicInput = putB (getI x) (getI counters),
        countPrivateInput = putB (getP x) (getP counters),
        countIntermediate = putB (getX x) (getX counters)
      }

instance HasU Counters (VarGroups Int) where
  getUAll counters = transpose $ VarGroups (getUAll (getO counters)) (getUAll (getI counters)) (getUAll (getP counters)) (getUAll (getX counters))
    where
      transpose :: VarGroups (IntMap Int) -> IntMap (VarGroups Int)
      transpose (VarGroups o i p x) =
        IntMap.filter (/= VarGroups 0 0 0 0) $
          IntMap.fromList $
            map
              ( \w ->
                  let result = VarGroups <$> IntMap.lookup w o <*> IntMap.lookup w i <*> IntMap.lookup w p <*> IntMap.lookup w x
                   in (w, Maybe.fromMaybe (VarGroups 0 0 0 0) result)
              )
              (IntSet.toList $ IntMap.keysSet o <> IntMap.keysSet i <> IntMap.keysSet p <> IntMap.keysSet x)
  putUAll xs counters =
    let transposed = transpose xs
     in counters
          { countOutput = putUAll (getO transposed) (getO counters),
            countPublicInput = putUAll (getI transposed) (getI counters),
            countPrivateInput = putUAll (getP transposed) (getP counters),
            countIntermediate = putUAll (getX transposed) (getX counters)
          }
    where
      transpose :: IntMap (VarGroups Int) -> VarGroups (IntMap Int)
      transpose = IntMap.foldlWithKey' go mempty

      go :: VarGroups (IntMap Int) -> Width -> VarGroups Int -> VarGroups (IntMap Int)
      go acc width (VarGroups o i p x) =
        VarGroups
          (IntMap.insertWith (+) width o (getO acc))
          (IntMap.insertWith (+) width i (getI acc))
          (IntMap.insertWith (+) width p (getP acc))
          (IntMap.insertWith (+) width x (getX acc))
