-- Datatype of the DSL
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}

module Keelung.Syntax where

import Data.Field.Galois (GaloisField)
import Data.IntSet (IntSet)
import Data.Semiring (Ring (..), Semiring (..), one)
import Keelung.Syntax.Common
import qualified Data.IntSet as IntSet

--------------------------------------------------------------------------------

data Type
  = Num -- numbers
  | Bool -- booleans
  | Unit -- booleans
  deriving (Show, Eq)

data Reference
  = V Type
  | A Reference
  deriving (Show)

--------------------------------------------------------------------------------

-- | Values are parameterised by some field and indexed by Type
data Value :: Type -> * -> * where
  Number :: n -> Value 'Num n
  Boolean :: Bool -> Value 'Bool n

instance Show n => Show (Value ty n) where
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
  Val :: Value val n -> Expr val n
  -- variable referecing
  Var :: Ref ('V val) -> Expr val n
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
  -- bool <-> num conversion
  ToBool :: Expr 'Num n -> Expr 'Bool n
  ToNum :: Expr 'Bool n -> Expr 'Num n

instance Functor (Expr ty) where
  fmap f expr = case expr of
    Val val -> Val $ case val of
      Number a -> Number (f a)
      Boolean b -> Boolean b
    Var ref -> Var ref
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
    ToBool x -> ToBool (fmap f x)
    ToNum x -> ToNum (fmap f x)

instance Show n => Show (Expr ty n) where
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
    ToBool x -> showString "ToBool " . showsPrec prec x
    ToNum x -> showString "ToNum " . showsPrec prec x

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

-- calculate the "size" of an expression
sizeOfExpr :: Expr ty n -> Int
sizeOfExpr expr = case expr of
  Val _ -> 1
  Var _ -> 1
  Add x y -> 1 + sizeOfExpr x + sizeOfExpr y
  Sub x y -> 1 + sizeOfExpr x + sizeOfExpr y
  Mul x y -> 1 + sizeOfExpr x + sizeOfExpr y
  Div x y -> 1 + sizeOfExpr x + sizeOfExpr y
  Eq x y -> 1 + sizeOfExpr x + sizeOfExpr y
  And x y -> 1 + sizeOfExpr x + sizeOfExpr y
  Or x y -> 1 + sizeOfExpr x + sizeOfExpr y
  Xor x y -> 1 + sizeOfExpr x + sizeOfExpr y
  BEq x y -> 1 + sizeOfExpr x + sizeOfExpr y
  IfThenElse x y z -> 1 + sizeOfExpr x + sizeOfExpr y + sizeOfExpr z
  ToBool x -> 1 + sizeOfExpr x
  ToNum x -> 1 + sizeOfExpr x

-- collect free variables of an expression
freeVars :: Expr ty n -> IntSet
freeVars expr = case expr of
  Val _ -> mempty
  Var (Variable n) -> IntSet.singleton n
  Add x y -> freeVars x <> freeVars y
  Sub x y -> freeVars x <> freeVars y
  Mul x y -> freeVars x <> freeVars y
  Div x y -> freeVars x <> freeVars y
  Eq x y -> freeVars x <> freeVars y
  And x y -> freeVars x <> freeVars y
  Or x y -> freeVars x <> freeVars y
  Xor x y -> freeVars x <> freeVars y
  BEq x y -> freeVars x <> freeVars y
  IfThenElse x y z -> freeVars x <> freeVars y <> freeVars z
  ToBool x -> freeVars x
  ToNum x -> freeVars x

--------------------------------------------------------------------------------

num :: n -> Expr 'Num n
num = Val . Number

true :: Expr 'Bool n
true = Val (Boolean True)

false :: Expr 'Bool n
false = Val (Boolean False)

neq :: Expr 'Num n -> Expr 'Num n -> Expr 'Bool n
neq x y = IfThenElse (x `Eq` y) false true

--------------------------------------------------------------------------------

fromBool :: GaloisField n => Expr 'Bool n -> Expr 'Num n
fromBool = ToNum

toBool :: GaloisField n => Expr 'Num n -> Expr 'Bool n
toBool = ToBool