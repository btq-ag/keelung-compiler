-- Datatype of the DSL
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}

module Keelung.Syntax where

--------------------------------------------------------------------------------

data Type
  = Num -- numbers
  | Bool -- booleans (well, special numbers!)
  | Arr -- a bunch of numbers

-- | Values are parameterised by some field and indexed by Type
data Value :: * -> Type -> * where
  Number :: n -> Value n 'Num
  Boolean :: Bool -> Value n 'Bool
  Array :: Type -> Int -> Value n ty

-- | Variables are indexed by Type
data Variable :: Type -> * where
  Variable :: Int -> Variable ty

-- | Expressions are parameterised by some field and indexed by Type
data Expr :: * -> Type -> * where
  -- value
  Val :: Value n ty -> Expr n ty
  -- variable
  Var :: Variable ty -> Expr n ty
  -- operators on numbers
  Add :: Expr n 'Num -> Expr n 'Num -> Expr n 'Num
  Mul :: Expr n 'Num -> Expr n 'Num -> Expr n 'Num
  Sub :: Expr n 'Num -> Expr n 'Num -> Expr n 'Num
  Div :: Expr n 'Num -> Expr n 'Num -> Expr n 'Num
  Eq :: Expr n 'Num -> Expr n 'Num -> Expr n 'Bool
  -- operators on booleans
  And :: Expr n 'Bool -> Expr n 'Bool -> Expr n 'Bool
  Or :: Expr n 'Bool -> Expr n 'Bool -> Expr n 'Bool
  Xor :: Expr n 'Bool -> Expr n 'Bool -> Expr n 'Bool
  BEq :: Expr n 'Num -> Expr n 'Num -> Expr n 'Bool