-- Datatype of the DSL
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}

module Keelung.Syntax where

import Data.Field.Galois (GaloisField)
import Data.Semiring (Ring (..), Semiring (..), one)

--------------------------------------------------------------------------------

data Type
  = Num -- numbers
  | Bool -- booleans
  deriving (Show)

data Ref
  = V Type
  | A Ref
  deriving (Show)

--------------------------------------------------------------------------------

-- | Values are parameterised by some field and indexed by Type
data Value :: * -> Type -> * where
  Number :: n -> Value n 'Num
  Boolean :: Bool -> Value n 'Bool

instance Show n => Show (Value n ty) where
  show (Number n) = show n
  show (Boolean b) = show b

--------------------------------------------------------------------------------

-- data Addr :: * where
  -- Addr :: Int -> Addr ('A val)
  -- AddrOfAddr :: Addr ('A val) -> Addr ('A ('A val))

type Addr = Int 

-- instance Show (Addr ref) where
--   show (Addr n) = show n
--   show (AddrOfAddr n) = "@" <> show n

-- | Variables are indexed by Type
data Reference :: Ref -> * where
  Variable :: Int -> Reference ('V val)
  Array :: Addr -> Reference ('A val)

instance Show (Reference ref) where
  show (Variable i) = "$" <> show i
  show (Array addr) = "@" <> show addr

--------------------------------------------------------------------------------

-- | Expressions are parameterised by some field and indexed by Type
data Expr :: * -> Type -> * where
  -- value
  Val :: Value n val -> Expr n val
  -- variable referecing
  Var :: Reference ('V val) -> Expr n val
  -- operators on numbers
  Add :: Expr n 'Num -> Expr n 'Num -> Expr n 'Num
  Sub :: Expr n 'Num -> Expr n 'Num -> Expr n 'Num
  Mul :: Expr n 'Num -> Expr n 'Num -> Expr n 'Num
  Div :: Expr n 'Num -> Expr n 'Num -> Expr n 'Num
  Eq :: Expr n 'Num -> Expr n 'Num -> Expr n 'Bool
  -- operators on booleans
  And :: Expr n 'Bool -> Expr n 'Bool -> Expr n 'Bool
  Or :: Expr n 'Bool -> Expr n 'Bool -> Expr n 'Bool
  Xor :: Expr n 'Bool -> Expr n 'Bool -> Expr n 'Bool
  BEq :: Expr n 'Num -> Expr n 'Num -> Expr n 'Bool
  -- if...then...else 
  IfThenElse :: Expr n 'Bool -> Expr n ty -> Expr n ty -> Expr n ty

instance Show n => Show (Expr n ty) where
  showsPrec prec expr = case expr of
    Val val -> shows val
    Var var -> shows var
    Add x y -> showParen (prec > 6) $ showsPrec 6 x . showString " + " . showsPrec 7 y
    Sub x y -> showParen (prec > 6) $ showsPrec 6 x . showString " - " . showsPrec 7 y
    Mul x y -> showParen (prec > 7) $ showsPrec 7 x . showString " * " . showsPrec 8 y
    Div x y -> showParen (prec > 7) $ showsPrec 7 x . showString " / " . showsPrec 8 y
    Eq x y -> showParen (prec > 5) $ showsPrec 6 x . showString " = " . showsPrec 6 y
    And x y -> showParen (prec > 3) $ showsPrec 4 x . showString " ∧ " . showsPrec 3 y
    Or x y -> showParen (prec > 2) $ showsPrec 3 x . showString " ∨ " . showsPrec 2 y
    Xor x y -> showParen (prec > 4) $ showsPrec 5 x . showString " ⊕ " . showsPrec 4 y
    BEq x y -> showParen (prec > 5) $ showsPrec 6 x . showString " = " . showsPrec 6 y
    IfThenElse p x y -> showParen (prec > 1) $ showString "if " . showsPrec 2 p . showString " then " . showsPrec 2 x . showString " else " . showsPrec 2 y 

instance GaloisField n => Num (Expr n 'Num) where
  (+) = Add
  (-) = Sub
  (*) = Mul
  abs = id

  -- law of `signum`: abs x * signum x == x
  signum = const (Val (Number 1))
  fromInteger = Val . Number . fromNatural . fromInteger

instance GaloisField n => Semiring (Expr n 'Num) where
  plus = Add
  times = Mul
  zero = Val (Number 0)
  one = Val (Number 1)

instance GaloisField n => Ring (Expr n 'Num) where
  negate = id

instance GaloisField n => Fractional (Expr n 'Num) where
  fromRational = Val . Number . fromRational
  (/) = Div

--------------------------------------------------------------------------------

true :: Expr n 'Bool
true = Val (Boolean True)

false :: Expr n 'Bool
false = Val (Boolean False)

--------------------------------------------------------------------------------

fromBool :: GaloisField n => Expr n 'Bool -> Expr n 'Num
fromBool (Val (Boolean False)) = zero 
fromBool (Val (Boolean True)) = one 
fromBool (Var (Variable n)) = Var (Variable n)
fromBool (Eq x y) = IfThenElse (Eq x y) one zero 
fromBool (And x y) = IfThenElse (And x y) one zero 
fromBool (Or x y) = IfThenElse (Or x y) one zero 
fromBool (Xor x y) = IfThenElse (Xor x y) one zero 
fromBool (BEq x y) = IfThenElse (BEq x y) one zero 
fromBool (IfThenElse p x y) = IfThenElse p (fromBool x) (fromBool y)