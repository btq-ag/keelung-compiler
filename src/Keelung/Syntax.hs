-- Datatype of the DSL
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}

module Keelung.Syntax where

import Data.Field.Galois (GaloisField)
import Data.Semiring (Ring (..), Semiring (..), one)

--------------------------------------------------------------------------------

type Addr = Int

-- type Var = Int

--------------------------------------------------------------------------------

data Val
  = Num -- numbers
  | Bool -- booleans
  deriving (Show)

data Ref
  = Var Val
  | Arr Ref
  deriving (Show)

data Type
  = Ref Ref
  | Val Val
  deriving (Show)

--------------------------------------------------------------------------------

-- | Values are parameterised by some field and indexed by Type
data Value :: * -> Val -> * where
  Number :: n -> Value n 'Num
  Boolean :: Bool -> Value n 'Bool

-- Array :: Type -> Addr -> Value n ty

instance Show n => Show (Value n ty) where
  show (Number n) = show n
  show (Boolean b) = show b

--   show (Array _ n) = "@" <> show n

--------------------------------------------------------------------------------

-- | Variables are indexed by Type
data Reference :: Ref -> * where
  Variable :: Int -> Reference ('Var val)
  Array :: Addr -> Reference ('Arr val)

instance Show (Reference ref) where
  show (Variable i) = "$" <> show i
  show (Array addr) = "@" <> show addr

--------------------------------------------------------------------------------

-- | Expressions are parameterised by some field and indexed by Type
data Expr :: * -> Type -> * where
  -- value
  Value :: Value n val -> Expr n ('Val val)
  -- variable
  -- Reference :: Reference ref -> Expr n ('Ref ref)
  Deref :: Reference ('Var val) -> Expr n ('Val val)
  -- operators on numbers
  VAdd :: Expr n ('Val 'Num) -> Expr n ('Val 'Num) -> Expr n ('Val 'Num)
  VSub :: Expr n ('Val 'Num) -> Expr n ('Val 'Num) -> Expr n ('Val 'Num)
  VMul :: Expr n ('Val 'Num) -> Expr n ('Val 'Num) -> Expr n ('Val 'Num)
  VDiv :: Expr n ('Val 'Num) -> Expr n ('Val 'Num) -> Expr n ('Val 'Num)
  VEq :: Expr n ('Val 'Num) -> Expr n ('Val 'Num) -> Expr n ('Val 'Bool)
  -- -- operators on booleans
  -- And :: Expr n 'Bool -> Expr n 'Bool -> Expr n 'Bool
  -- Or :: Expr n 'Bool -> Expr n 'Bool -> Expr n 'Bool
  -- Xor :: Expr n 'Bool -> Expr n 'Bool -> Expr n 'Bool
  -- BEq :: Expr n 'Num -> Expr n 'Num -> Expr n 'Bool
  -- operators on reference of numbers
  -- RAdd :: Expr n ('Ref ('Var 'Num)) -> Expr n ('Ref ('Var 'Num)) -> Expr n ('Ref ('Var 'Num))
  -- RSub :: Expr n ('Ref ('Var 'Num)) -> Expr n ('Ref ('Var 'Num)) -> Expr n ('Ref ('Var 'Num))
  -- RMul :: Expr n ('Ref ('Var 'Num)) -> Expr n ('Ref ('Var 'Num)) -> Expr n ('Ref ('Var 'Num))
  -- RDiv :: Expr n ('Ref ('Var 'Num)) -> Expr n ('Ref ('Var 'Num)) -> Expr n ('Ref ('Var 'Num))
  -- REq :: Expr n ('Ref ('Var 'Num)) -> Expr n ('Ref ('Var 'Num)) -> Expr n ('Ref ('Var 'Bool))



instance Show n => Show (Expr n ty) where
  showsPrec prec expr = case expr of
    Value val -> shows val
    Deref ref -> shows ref
    VAdd x y -> showParen (prec > 6) $ showsPrec 6 x . showString " + " . showsPrec 7 y
    VSub x y -> showParen (prec > 6) $ showsPrec 6 x . showString " - " . showsPrec 7 y
    VMul x y -> showParen (prec > 7) $ showsPrec 7 x . showString " * " . showsPrec 8 y
    VDiv x y -> showParen (prec > 7) $ showsPrec 7 x . showString " / " . showsPrec 8 y
    VEq x y -> showParen (prec > 5) $ showsPrec 6 x . showString " = " . showsPrec 6 y

-- instance Show n => Show (Expr n ty) where
--   showsPrec prec expr = case expr of
--     Val val -> shows val
--     Var var -> shows var
--     Add x y -> showParen (prec > 6) $ showsPrec 6 x . showString " + " . showsPrec 7 y
--     Sub x y -> showParen (prec > 6) $ showsPrec 6 x . showString " - " . showsPrec 7 y
--     Mul x y -> showParen (prec > 7) $ showsPrec 7 x . showString " * " . showsPrec 8 y
--     Div x y -> showParen (prec > 7) $ showsPrec 7 x . showString " / " . showsPrec 8 y
--     Eq x y -> showParen (prec > 5) $ showsPrec 6 x . showString " = " . showsPrec 6 y
--     And x y -> showParen (prec > 3) $ showsPrec 4 x . showString " ∧ " . showsPrec 3 y
--     Or x y -> showParen (prec > 2) $ showsPrec 3 x . showString " ∨ " . showsPrec 2 y
--     Xor x y -> showParen (prec > 4) $ showsPrec 5 x . showString " ⊕ " . showsPrec 4 y
--     BEq x y -> showParen (prec > 5) $ showsPrec 6 x . showString " = " . showsPrec 6 y

instance GaloisField n => Num (Expr n ('Val 'Num)) where
  (+) = VAdd
  (-) = VSub
  (*) = VMul
  abs = id

  -- law of `signum`: abs x * signum x == x
  signum = const (Value (Number 1))
  fromInteger = Value . Number . fromNatural . fromInteger

-- instance Num (Reference ('Var 'Num)) where
--   (+) = VAdd
--   (-) = VSub
--   (*) = VMul
--   abs = id

--   -- law of `signum`: abs x * signum x == x
--   signum = const (Value (Number 1))
--   fromInteger = Value . Number . fromNatural . fromInteger

-- instance GaloisField n => Semiring (Expr n ('Val 'Num)) where
--   plus = Add
--   times = Mul
--   zero = Val (Number 0)
--   one = Val (Number 1)

-- instance GaloisField n => Ring (Expr n ('Val 'Num)) where
--   negate = id

-- instance GaloisField n => Fractional (Expr n ('Val 'Num)) where
--   fromRational = Val . Number . fromRational
--   (/) = Div

-- instance GaloisField n => Num (Expr n ('Ref ('Var 'Num))) where
--   (+) = RAdd
--   (-) = RSub
--   (*) = RMul
--   abs = id

--   -- law of `signum`: abs x * signum x == x
--   signum = const (AsRef (Value (Number 1)))
--   fromInteger = AsRef . Value . Number . fromNatural . fromInteger


-- --------------------------------------------------------------------------------

-- true :: Expr n 'Bool
-- true = Val (Boolean True)

-- false :: Expr n 'Bool
-- false = Val (Boolean False)

-- --------------------------------------------------------------------------------

-- -- fromBool :: GaloisField n => Expr n 'Bool -> Expr n 'Num
-- -- fromBool (Val (Boolean False)) = zero
-- -- fromBool (Val (Boolean True)) = one
-- -- fromBool (Val (Array ty n)) = Val (Array ty n)
-- -- fromBool (Var (Variable _ n)) = Var (Variable Num n)
-- -- fromBool (Eq x y) =
-- -- fromBool (And x y) = _wd
-- -- fromBool (Or x y) = _we
-- -- fromBool (Xor x y) = _wf
-- -- fromBool (BEq x y) = _wg