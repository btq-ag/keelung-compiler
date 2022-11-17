{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

module Keelung.Compiler.Syntax.Internal where

import Data.Data (Proxy (Proxy))
import Data.Kind (Type)
import Data.Sequence (Seq (..))
import GHC.Natural (Natural)
import GHC.TypeNats
import Keelung.Types (Var)

--------------------------------------------------------------------------------

-- | Bit Width
type Width = Int

-- | Kinds of different datatypes
data Kind
  = N Nat -- Field element
  | U Nat -- Unsigned integer
  | B -- Boolean

-- | Syntax tree
data Expr :: Kind -> Type -> Type where
  -- values
  Number :: n -> Expr ('N w) n
  UInt :: n -> Expr ('U w) n
  Boolean :: Bool -> Expr 'B n
  -- variables
  VarN :: Var -> Expr ('N w) n
  VarU :: Var -> Expr ('U w) n
  VarB :: Var -> Expr 'B n
  -- arithmetic operations
  AddN :: Expr ('N w) n -> Expr ('N w) n -> Seq (Expr ('N w) n) -> Expr ('N w) n
  AddU :: Expr ('U w) n -> Expr ('U w) n -> Expr ('U w) n
  SubN :: Expr ('N w) n -> Expr ('N w) n -> Expr ('N w) n
  SubU :: Expr ('U w) n -> Expr ('U w) n -> Expr ('U w) n
  MulN :: Expr ('N w) n -> Expr ('N w) n -> Expr ('N w) n
  MulU :: Expr ('U w) n -> Expr ('U w) n -> Expr ('U w) n
  DivN :: Expr ('N w) n -> Expr ('N w) n -> Expr ('N w) n
  DivU :: Expr ('U w) n -> Expr ('U w) n -> Expr ('U w) n
  -- equalities
  Eq :: Expr k n -> Expr k n -> Expr 'B n
  -- logical operations
  -- Neg :: Expr k n -> Expr k n
  And :: Expr k n -> Expr k n -> Seq (Expr k n) -> Expr k n
  Or :: Expr k n -> Expr k n -> Seq (Expr k n) -> Expr k n
  Xor :: Expr k n -> Expr k n -> Expr k n
  -- shift / rotate
  -- ShRN :: Int -> Expr ('N w) n -> Expr ('N w) n
  -- ShRU :: Int -> Expr ('U w) n -> Expr ('U w) n
  -- ShLN :: Int -> Expr ('N w) n -> Expr ('N w) n
  -- ShLU :: Int -> Expr ('U w) n -> Expr ('U w) n
  RoLN :: Int -> Expr ('N w) n -> Expr ('N w) n
  RoLU :: Int -> Expr ('U w) n -> Expr ('U w) n
  -- conditional
  If :: Expr 'B n -> Expr k n -> Expr k n -> Expr k n

instance Eq n => Eq (Expr k n) where
  (Number a) == (Number b) = a == b
  (UInt a) == (UInt b) = a == b
  (Boolean a) == (Boolean b) = a == b
  (VarN a) == (VarN b) = a == b
  (VarU a) == (VarU b) = a == b
  (VarB a) == (VarB b) = a == b
  (AddN a b c) == (AddN d e f) = a == d && b == e && c == f
  (AddU a b) == (AddU c d) = a == c && b == d
  (SubN a b) == (SubN c d) = a == c && b == d
  (SubU a b) == (SubU c d) = a == c && b == d
  (MulN a b) == (MulN c d) = (a == c && b == d) || (a == d && b == c)
  (MulU a b) == (MulU c d) = (a == c && b == d) || (a == d && b == c)
  (DivN a b) == (DivN c d) = a == c && b == d
  (DivU a b) == (DivU c d) = a == c && b == d
  (Eq _ _) == (Eq _ _) = True -- cannot tell if the subexpressions even have the same type
  -- (Neg a) == (Neg b) = a == b
  (And a b c) == (And d e f) = a == d && b == e && c == f
  (Or a b c) == (Or d e f) = a == d && b == e && c == f
  (Xor a b) == (Xor c d) = a == c && b == d || a == d && b == c
  -- (ShRN a b) == (ShRN c d) = a == c && b == d
  -- (ShRU a b) == (ShRU c d) = a == c && b == d
  -- (ShLN a b) == (ShLN c d) = a == c && b == d
  -- (ShLU a b) == (ShLU c d) = a == c && b == d
  (RoLN a b) == (RoLN c d) = a == c && b == d
  (RoLU a b) == (RoLU c d) = a == c && b == d
  (If a b c) == (If d e f) = a == d && b == e && c == f
  _ == _ = False

instance Functor (Expr k) where
  fmap f (Number n) = Number (f n)
  fmap f (UInt n) = UInt (f n)
  fmap _ (Boolean b) = Boolean b
  fmap _ (VarN n) = VarN n
  fmap _ (VarU n) = VarU n
  fmap _ (VarB n) = VarB n
  fmap f (AddN a b c) = AddN (fmap f a) (fmap f b) (fmap (fmap f) c)
  fmap f (AddU a b) = AddU (fmap f a) (fmap f b)
  fmap f (SubN a b) = SubN (fmap f a) (fmap f b)
  fmap f (SubU a b) = SubU (fmap f a) (fmap f b)
  fmap f (MulN a b) = MulN (fmap f a) (fmap f b)
  fmap f (MulU a b) = MulU (fmap f a) (fmap f b)
  fmap f (DivN a b) = DivN (fmap f a) (fmap f b)
  fmap f (DivU a b) = DivU (fmap f a) (fmap f b)
  fmap f (Eq a b) = Eq (fmap f a) (fmap f b)
  -- fmap f (Neg a) = Neg (fmap f a)
  fmap f (And a b c) = And (fmap f a) (fmap f b) (fmap (fmap f) c)
  fmap f (Or a b c) = Or (fmap f a) (fmap f b) (fmap (fmap f) c)
  fmap f (Xor a b) = Xor (fmap f a) (fmap f b)
  -- fmap f (ShRN a b) = ShRN a (fmap f b)
  -- fmap f (ShRU a b) = ShRU a (fmap f b)
  -- fmap f (ShLN a b) = ShLN a (fmap f b)
  -- fmap f (ShLU a b) = ShLU a (fmap f b)
  fmap f (RoLN a b) = RoLN a (fmap f b)
  fmap f (RoLU a b) = RoLU a (fmap f b)
  fmap f (If a b c) = If (fmap f a) (fmap f b) (fmap f c)

instance Num n => Num (Expr ('N w) n) where
  x + y = AddN x y mempty
  x - y = SubN x y
  x * y = MulN x y
  abs = id
  signum = const 1
  fromInteger = Number . fromInteger

instance Num n => Num (Expr ('U w) n) where
  x + y = AddU x y
  x - y = SubU x y
  x * y = MulU x y
  abs = id
  signum = const 1
  fromInteger = UInt . fromInteger

instance Show n => Show (Expr k n) where
  showsPrec prec expr =
    let chain :: Show n => String -> Int -> Seq (Expr k n) -> String -> String
        chain delim n = showParen (prec > n) . go delim n
        go :: Show n => String -> Int -> Seq (Expr k n) -> String -> String
        go _ _ Empty = showString ""
        go _ n (x :<| Empty) = showsPrec (succ n) x
        go delim n (x :<| xs') = showsPrec (succ n) x . showString delim . go delim n xs'
     in case expr of
          Number n -> shows n
          UInt n -> shows n
          Boolean b -> shows b
          VarN var -> showString "$" . shows var
          VarU var -> showString "$" . shows var
          VarB var -> showString "$" . shows var
          AddN a b c -> chain " + " 6 $ a :<| b :<| c
          AddU a b -> chain " + " 6 $ a :<| b :<| Empty
          SubN a b -> chain " - " 6 $ a :<| b :<| Empty
          SubU a b -> chain " - " 6 $ a :<| b :<| Empty
          MulN a b -> chain " * " 7 $ a :<| b :<| Empty
          MulU a b -> chain " * " 7 $ a :<| b :<| Empty
          DivN a b -> chain " / " 7 $ a :<| b :<| Empty
          DivU a b -> chain " / " 7 $ a :<| b :<| Empty
          Eq a b -> showsPrec 6 a . showString " == " . showsPrec 6 b
          -- Neg a -> showString "¬ " . showsPrec 8 a
          And a b c -> chain " ∧ " 3 $ a :<| b :<| c
          Or a b c -> chain " ∨ " 2 $ a :<| b :<| c
          Xor a b -> chain " ⊕ " 4 $ a :<| b :<| Empty
          -- ShRN n a -> showsPrec 8 a . showString " >> " . shows n
          -- ShRU n a -> showsPrec 8 a . showString " >> " . shows n
          -- ShLN n a -> showsPrec 8 a . showString " << " . shows n
          -- ShLU n a -> showsPrec 8 a . showString " << " . shows n
          RoLN n a -> showString "RotateL " . shows n . showString " " . showsPrec 8 a
          RoLU n a -> showString "RotateL " . shows n . showString " " . showsPrec 8 a
          If p a b -> showParen (prec > 1) $ showString "if " . showsPrec 2 p . showString " then " . showsPrec 2 a . showString " else " . showsPrec 2 b

--------------------------------------------------------------------------------

-- | Typeclass for deriving the bit width of an expression
class HasWidth k where
  bitWidthOf :: Expr k n -> Natural

instance KnownNat w => HasWidth ('N w) where
  bitWidthOf _ = natVal (Proxy :: Proxy w)

instance HasWidth 'B where
  bitWidthOf _ = 1

instance KnownNat w => HasWidth ('U w) where
  bitWidthOf _ = natVal (Proxy :: Proxy w)

--------------------------------------------------------------------------------

-- | "Degree" of an expression
data Degree = D0 | D1 | Dn

type family Max (x :: Degree) (y :: Degree) :: Degree where
  Max 'D0 n = n
  Max 'D1 'D0 = 'D1
  Max 'D1 n = n
  Max 'Dn _ = 'Dn
