-- Datatype of the DSL
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}

module Keelung.Syntax where

import Data.Field.Galois (GaloisField)
import Data.Semiring (Ring (..), Semiring (..), one)
import Keelung.Syntax.Common

--------------------------------------------------------------------------------

data Type
  = Num -- numbers
  | Bool -- booleans
  deriving (Show, Eq)

data Reference
  = V Type
  | A Reference
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

data Ref :: Reference -> * where
  Variable :: Var -> Ref ('V val)
  Array :: Addr -> Ref ('A val)

instance Show (Ref ref) where
  show (Variable i) = "$" <> show i
  show (Array addr) = "@" <> show addr

--------------------------------------------------------------------------------

-- | Expressions are parameterised by some field and indexed by Type
data Expr :: Type -> * -> * where
  -- value
  Val :: Value n val -> Expr val n
  -- variable referecing
  Var :: Type -> Ref ('V val) -> Expr val n
  -- operators on numbers
  Add :: Expr 'Num n -> Expr 'Num n -> Expr 'Num n
  Sub :: Expr 'Num n -> Expr 'Num n -> Expr 'Num n
  Mul :: Expr 'Num n -> Expr 'Num n -> Expr 'Num n
  Div :: Expr 'Num n -> Expr 'Num n -> Expr 'Num n
  Eq :: Expr 'Num n -> Expr 'Num n -> Expr 'Bool n
  -- operators on booleans
  And :: Expr 'Bool n -> Expr 'Bool n -> Expr 'Bool n
  Or :: Expr 'Bool n -> Expr 'Bool n -> Expr 'Bool n
  Xor :: Expr 'Bool n -> Expr 'Bool n -> Expr 'Bool n
  BEq :: Expr 'Bool n -> Expr 'Bool n -> Expr 'Bool n
  -- if...then...else
  IfThenElse :: Expr 'Bool n -> Expr ty n -> Expr ty n -> Expr ty n

instance Functor (Expr ty) where
  fmap f expr = case expr of
    Val val -> Val $ case val of
      Number a -> Number (f a)
      Boolean b -> Boolean b
    Var t ref -> Var t ref
    Add x y -> Add (fmap f x) (fmap f y)
    Sub x y -> Sub (fmap f x) (fmap f y)
    Mul x y -> Mul (fmap f x) (fmap f y)
    Div x y -> Div (fmap f x) (fmap f y)
    Eq x y -> Eq (fmap f x) (fmap f y)
    And x y -> And (fmap f x) (fmap f y)
    Or x y -> Or (fmap f x) (fmap f y)
    Xor x y -> Xor (fmap f x) (fmap f y)
    BEq x y -> BEq (fmap f x) (fmap f y)
    IfThenElse p x y -> IfThenElse (fmap f p) (fmap f x) (fmap f y)

collectBooleanVars :: Expr ty n -> [Var]
collectBooleanVars expr = case expr of
  Var Bool (Variable n) -> [n]
  Var Num (Variable _) -> []
  Val _ -> []
  Add x y -> collectBooleanVars x <> collectBooleanVars y
  Sub x y -> collectBooleanVars x <> collectBooleanVars y
  Mul x y -> collectBooleanVars x <> collectBooleanVars y
  Div x y -> collectBooleanVars x <> collectBooleanVars y
  Eq x y -> collectBooleanVars x <> collectBooleanVars y
  And x y -> collectBooleanVars x <> collectBooleanVars y
  Or x y -> collectBooleanVars x <> collectBooleanVars y
  Xor x y -> collectBooleanVars x <> collectBooleanVars y
  BEq x y -> collectBooleanVars x <> collectBooleanVars y
  IfThenElse b x y ->
    collectBooleanVars b <> collectBooleanVars x <> collectBooleanVars y

instance Show n => Show (Expr ty n) where
  showsPrec prec expr = case expr of
    Val val -> shows val
    Var _ var -> shows var
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

instance GaloisField n => Num (Expr 'Num n) where
  (+) = Add
  (-) = Sub
  (*) = Mul
  abs = id

  -- law of `signum`: abs x * signum x == x
  signum = const (Val (Number 1))
  fromInteger = Val . Number . fromNatural . fromInteger

instance GaloisField n => Semiring (Expr 'Num n) where
  plus = Add
  times = Mul
  zero = Val (Number 0)
  one = Val (Number 1)

instance GaloisField n => Ring (Expr 'Num n) where
  negate = id

instance GaloisField n => Fractional (Expr 'Num n) where
  fromRational = Val . Number . fromRational
  (/) = Div

--------------------------------------------------------------------------------

true :: Expr 'Bool n
true = Val (Boolean True)

false :: Expr 'Bool n
false = Val (Boolean False)

neq :: Expr 'Num n -> Expr 'Num n -> Expr 'Bool n
neq x y = IfThenElse (x `Eq` y) false true

--------------------------------------------------------------------------------

fromBool :: GaloisField n => Expr 'Bool n -> Expr 'Num n
fromBool (Val (Boolean False)) = zero
fromBool (Val (Boolean True)) = one
fromBool (Var _ (Variable n)) = Var Num (Variable n)
fromBool (Eq x y) = IfThenElse (Eq x y) one zero
fromBool (And x y) = IfThenElse (And x y) one zero
fromBool (Or x y) = IfThenElse (Or x y) one zero
fromBool (Xor x y) = IfThenElse (Xor x y) one zero
fromBool (BEq x y) = IfThenElse (BEq x y) one zero
fromBool (IfThenElse p x y) = IfThenElse p (fromBool x) (fromBool y)

toBool :: GaloisField n => Expr 'Num n -> Expr 'Bool n
toBool (Val (Number 0)) = false
toBool (Val (Number _)) = true
toBool (Var _ (Variable n)) = Var Bool (Variable n)
toBool (Add x y) = Add x y `neq` 0
toBool (Sub x y) = Sub x y `neq` 0
toBool (Mul x y) = Mul x y `neq` 0
toBool (Div x y) = Div x y `neq` 0
toBool (IfThenElse p x y) = IfThenElse p (toBool x) (toBool y)