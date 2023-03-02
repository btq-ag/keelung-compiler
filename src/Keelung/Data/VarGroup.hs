{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
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
import Data.List qualified as List
import Data.Maybe qualified as Maybe
import Data.Serialize (Serialize)
import Data.Validation
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import GHC.Generics (Generic)
import Keelung.Data.N (N (N))
import Keelung.Data.Struct
import Keelung.Syntax (Width)
import Keelung.Syntax.Counters

--------------------------------------------------------------------------------

-- | Homogeneous version of 'Struct'
data VarGroup a = VarGroup a a (IntMap a)
  deriving (Eq, Show, Generic)

instance NFData a => NFData (VarGroup a)

instance Functor VarGroup where
  fmap func (VarGroup f b u) = VarGroup (func f) (func b) (fmap func u)

instance Foldable VarGroup where
  foldMap func (VarGroup f b u) = func f <> func b <> foldMap func u

instance Semigroup a => Semigroup (VarGroup a) where
  VarGroup f1 b1 u1 <> VarGroup f2 b2 u2 =
    VarGroup (f1 <> f2) (b1 <> b2) (u1 <> u2)

instance Monoid a => Monoid (VarGroup a) where
  mempty = VarGroup mempty mempty mempty

instance Serialize n => Serialize (VarGroup n)

--------------------------------------------------------------------------------

class HasF a f | a -> f where
  getF :: a -> f
  putF :: f -> a -> a
  modifyF :: (f -> f) -> a -> a
  modifyF f x = putF (f (getF x)) x

instance HasF (VarGroup f) f where
  getF (VarGroup f _ _) = f
  putF f (VarGroup _ b u) = VarGroup f b u
  modifyF func (VarGroup f b u) = VarGroup (func f) b u

instance HasF (Struct f b u) f where
  getF (Struct f _ _) = f
  putF f (Struct _ b u) = Struct f b u
  modifyF func (Struct f b u) = Struct (func f) b u

--------------------------------------------------------------------------------

class HasB a b | a -> b where
  getB :: a -> b
  putB :: b -> a -> a
  modifyB :: (b -> b) -> a -> a
  modifyB f x = putB (f (getB x)) x

instance HasB (VarGroup b) b where
  getB (VarGroup _ b _) = b
  putB b (VarGroup f _ u) = VarGroup f b u
  modifyB func (VarGroup f b u) = VarGroup f (func b) u

instance HasB (Struct f b u) b where
  getB (Struct _ b _) = b
  putB b (Struct f _ u) = Struct f b u
  modifyB func (Struct f b u) = Struct f (func b) u

class HasU a u | a -> u where
  getUAll :: a -> IntMap u

  getU :: Width -> a -> Maybe u
  getU width = IntMap.lookup width . getUAll

  putUAll :: IntMap u -> a -> a

  putU :: Width -> u -> a -> a
  putU width u x = putUAll (IntMap.insert width u (getUAll x)) x

  modifyU :: Width -> (u -> u) -> a -> a
  modifyU width f x = case getU width x of
    Nothing -> x
    Just u -> putU width (f u) x

  modifyUAll :: (IntMap u -> IntMap u) -> a -> a
  modifyUAll f x = putUAll (f (getUAll x)) x

instance HasU (VarGroup u) u where
  getUAll (VarGroup _ _ u) = u
  putUAll u (VarGroup f b _) = VarGroup f b u

instance HasU (Struct n n n) n where
  getUAll (Struct _ _ u) = u
  putUAll u (Struct f b _) = Struct f b u

--------------------------------------------------------------------------------

data VarGroups n = VarGroups
  { ofO :: n,
    ofI :: n,
    ofP :: n,
    ofX :: n
  }
  deriving (Eq, Show, NFData, Generic, Functor)

instance Serialize n => Serialize (VarGroups n)

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

type Witness n = VarGroups (VarGroup (Vector n))

--------------------------------------------------------------------------------

type VarSet n = VarGroups (VarGroup IntSet)

showList' :: [String] -> String
showList' xs = "[" <> List.intercalate ", " xs <> "]"

instance {-# OVERLAPPING #-} Show (VarSet n) where
  show (VarGroups o i p x) =
    showList' $
      showVarGroup "O" o <> showVarGroup "I" i <> showVarGroup "P" p <> showVarGroup "X" x
    where
      showVarGroup :: String -> VarGroup IntSet -> [String]
      showVarGroup prefix (VarGroup f b u) =
        map (\var -> "B" <> prefix <> show var) (IntSet.toList b)
          <> map (\var -> "F" <> prefix <> show var) (IntSet.toList f)
          <> concatMap (\(width, xs) -> map (\var -> "U" <> toSubscript width <> prefix <> show var) (IntSet.toList xs)) (IntMap.toList u)

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

-- | Data structure for interpreters
type Partial n = VarGroups (VarGroup (PartialBinding n))

-- | Expected number of bindings and actual bindings
type PartialBinding n = (Int, IntMap n)

instance {-# OVERLAPPING #-} (GaloisField n, Integral n) => Show (Partial n) where
  show (VarGroups o i p x) = showList' $ showVarGroup "O" o <> showVarGroup "I" i <> showVarGroup "P" p <> showVarGroup "" x
    where
      showPartialBinding :: (GaloisField n, Integral n) => String -> (Int, IntMap n) -> IntMap String
      showPartialBinding prefix (_size, bindings) = IntMap.mapWithKey (\k v -> prefix <> show k <> " := " <> show (N v)) bindings

      showVarGroup :: (GaloisField n, Integral n) => String -> VarGroup (PartialBinding n) -> [String]
      showVarGroup suffix (VarGroup f b u) =
        toList (showPartialBinding ("F" <> suffix) f)
          <> toList (showPartialBinding ("B" <> suffix) b)
          <> concatMap (\(width, xs) -> toList (showPartialBinding ("U" <> suffix <> toSubscript width) xs)) (IntMap.toList u)

-- | Convert a partial binding to a total binding, or return the variables that are not bound
toTotal :: Partial n -> Either (VarSet n) (Witness n)
toTotal (VarGroups o i p x) =
  toEither $
    VarGroups
      <$> first (\struct -> VarGroups struct mempty mempty mempty) (convertVarGroup o)
      <*> first (\struct -> VarGroups mempty struct mempty mempty) (convertVarGroup i)
      <*> first (\struct -> VarGroups mempty mempty struct mempty) (convertVarGroup p)
      <*> first (VarGroups mempty mempty mempty) (convertVarGroup x)
  where
    convertVarGroup ::
      VarGroup (PartialBinding n) ->
      Validation (VarGroup IntSet) (VarGroup (Vector n))
    convertVarGroup (VarGroup f b u) =
      VarGroup
        <$> first (\set -> VarGroup set mempty mempty) (toTotal' f)
        <*> first (\set -> VarGroup mempty set mempty) (toTotal' b)
        <*> first (VarGroup mempty mempty) (sequenceIntMap toTotal' u)

    sequenceIntMap :: (a -> Validation b c) -> IntMap a -> Validation (IntMap b) (IntMap c)
    sequenceIntMap f = sequenceA . IntMap.mapWithKey (\width xs -> first (IntMap.singleton width) (f xs))

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
    (restrictVarGroup o o')
    (restrictVarGroup i i')
    (restrictVarGroup p p')
    (restrictVarGroup x x')
  where
    restrictVarGroup :: VarGroup (PartialBinding n) -> VarGroup IntSet -> VarGroup (PartialBinding n)
    restrictVarGroup (VarGroup f b u) (VarGroup f' b' u') =
      VarGroup
        (restrict f f')
        (restrict b b')
        (IntMap.intersectionWith restrict u u')

    restrict :: (Int, IntMap n) -> IntSet -> (Int, IntMap n)
    restrict (size, xs) set = (size, IntMap.restrictKeys xs set)

----------------------------------------------------------------------------

instance HasO Counters (Struct Int Int Int) where
  getO = countOutput
  putO x counters = counters {countOutput = x}
  modifyO f counters = counters {countOutput = f (countOutput counters)}

instance HasI Counters (Struct Int Int Int) where
  getI = countPublicInput
  putI x counters = counters {countPublicInput = x}
  modifyI f counters = counters {countPublicInput = f (countPublicInput counters)}

instance HasP Counters (Struct Int Int Int) where
  getP = countPrivateInput
  putP x counters = counters {countPrivateInput = x}
  modifyP f counters = counters {countPrivateInput = f (countPrivateInput counters)}

instance HasX Counters (Struct Int Int Int) where
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
