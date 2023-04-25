{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}

module Keelung.Compiler.Syntax.Untyped
  ( Width,
    widthOfU,
    Expr (..),
    ExprB (..),
    ExprF (..),
    ExprU (..),
    TypeErased (..),
    Assignment (..),
    lookupF,
    lookupB,
    lookupU,
    SideEffect (..),
  )
where

import Data.Field.Galois (GaloisField)
import Data.IntMap (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.Sequence (Seq (..))
import Keelung.Compiler.Constraint
import Keelung.Data.Struct (Struct (..))
import Keelung.Field (N (..))
import Keelung.Syntax (Var, Width)
import Keelung.Syntax.Counters
import Keelung.Syntax.Counters qualified as Counters

--------------------------------------------------------------------------------

data ExprB n
  = ValB n
  | VarB Var
  | VarBO Var
  | VarBI Var
  | VarBP Var
  | -- logical operators
    AndB (ExprB n) (ExprB n) (Seq (ExprB n))
  | OrB (ExprB n) (ExprB n) (Seq (ExprB n))
  | XorB (ExprB n) (ExprB n)
  | NotB (ExprB n)
  | IfB (ExprB n) (ExprB n) (ExprB n)
  | -- comparison operators
    NEqB (ExprB n) (ExprB n)
  | NEqF (ExprF n) (ExprF n)
  | NEqU (ExprU n) (ExprU n)
  | EqB (ExprB n) (ExprB n)
  | EqF (ExprF n) (ExprF n)
  | EqU (ExprU n) (ExprU n)
  | LTU (ExprU n) (ExprU n)
  | LTEU (ExprU n) (ExprU n)
  | GTU (ExprU n) (ExprU n)
  | GTEU (ExprU n) (ExprU n)
  | -- bit tests on UInt
    BitU (ExprU n) Int
  deriving (Functor, Eq)

instance (Integral n, Show n) => Show (ExprB n) where
  showsPrec prec expr = case expr of
    ValB 0 -> showString "F"
    ValB _ -> showString "T"
    VarB var -> showString "B" . shows var
    VarBO var -> showString "BO" . shows var
    VarBI var -> showString "BI" . shows var
    VarBP var -> showString "BP" . shows var
    AndB x0 x1 xs -> chain prec " ∧ " 3 $ x0 :<| x1 :<| xs
    OrB x0 x1 xs -> chain prec " ∨ " 2 $ x0 :<| x1 :<| xs
    XorB x0 x1 -> chain prec " ⊕ " 4 $ x0 :<| x1 :<| Empty
    NotB x -> chain prec "¬ " 5 $ x :<| Empty
    IfB p x y -> showParen (prec > 1) $ showString "if " . showsPrec 2 p . showString " then " . showsPrec 2 x . showString " else " . showsPrec 2 y
    NEqB x0 x1 -> chain prec " ≠ " 5 $ x0 :<| x1 :<| Empty
    NEqF x0 x1 -> chain prec " ≠ " 5 $ x0 :<| x1 :<| Empty
    NEqU x0 x1 -> chain prec " ≠ " 5 $ x0 :<| x1 :<| Empty
    EqB x0 x1 -> chain prec " ≡ " 5 $ x0 :<| x1 :<| Empty
    EqF x0 x1 -> chain prec " ≡ " 5 $ x0 :<| x1 :<| Empty
    EqU x0 x1 -> chain prec " ≡ " 5 $ x0 :<| x1 :<| Empty
    LTU x0 x1 -> chain prec " < " 5 $ x0 :<| x1 :<| Empty
    LTEU x0 x1 -> chain prec " ≤ " 5 $ x0 :<| x1 :<| Empty
    GTU x0 x1 -> chain prec " > " 5 $ x0 :<| x1 :<| Empty
    GTEU x0 x1 -> chain prec " ≥ " 5 $ x0 :<| x1 :<| Empty
    BitU x i -> showsPrec prec x . showString "[" . shows i . showString "]"

--------------------------------------------------------------------------------

data ExprF n
  = ValF n
  | VarF Var
  | VarFO Var
  | VarFI Var
  | VarFP Var
  | -- arithmetic operators
    SubF (ExprF n) (ExprF n)
  | AddF (ExprF n) (ExprF n) (Seq (ExprF n))
  | MulF (ExprF n) (ExprF n)
  | DivF (ExprF n) (ExprF n)
  | -- logical operators

    -- | MMIF (ExprF n) Int -- modular multiplicative inverse
    IfF (ExprB n) (ExprF n) (ExprF n)
  | BtoF (ExprB n)
  deriving (Functor, Eq)

instance (Show n, Integral n) => Show (ExprF n) where
  showsPrec prec expr = case expr of
    ValF n -> shows n
    VarF var -> showString "F" . shows var
    VarFO var -> showString "FO" . shows var
    VarFI var -> showString "FI" . shows var
    VarFP var -> showString "FP" . shows var
    SubF x y -> chain prec " - " 6 $ x :<| y :<| Empty
    AddF x0 x1 xs -> chain prec " + " 6 $ x0 :<| x1 :<| xs
    MulF x y -> chain prec " * " 7 $ x :<| y :<| Empty
    -- MMIF x p -> showString "modInv " . showsPrec prec x . showString " " . shows p
    DivF x y -> chain prec " / " 7 $ x :<| y :<| Empty
    IfF p x y -> showParen (prec > 1) $ showString "if " . showsPrec 2 p . showString " then " . showsPrec 2 x . showString " else " . showsPrec 2 y
    BtoF x -> showString "B→F " . showsPrec prec x

--------------------------------------------------------------------------------

data ExprU n
  = ValU Width n
  | VarU Width Var
  | VarUO Width Var
  | VarUI Width Var
  | VarUP Width Var
  | -- arithmetic operators
    SubU Width (ExprU n) (ExprU n)
  | AddU Width (ExprU n) (ExprU n)
  | MulU Width (ExprU n) (ExprU n)
  | MMIU Width (ExprU n) Integer -- modular multiplicative inverse
  | -- logical operators
    AndU Width (ExprU n) (ExprU n) (Seq (ExprU n))
  | OrU Width (ExprU n) (ExprU n) (Seq (ExprU n))
  | XorU Width (ExprU n) (ExprU n)
  | NotU Width (ExprU n)
  | IfU Width (ExprB n) (ExprU n) (ExprU n)
  | -- bit operators
    RoLU Width Int (ExprU n)
  | ShLU Width Int (ExprU n)
  | SetU Width (ExprU n) Int (ExprB n) -- set bit
  | -- conversion operators
    BtoU Width (ExprB n)
  deriving (Functor, Eq)

instance (Show n, Integral n) => Show (ExprU n) where
  showsPrec prec expr = case expr of
    ValU _ n -> shows n
    VarU _ var -> showString "U" . shows var
    VarUO _ var -> showString "UO" . shows var
    VarUI _ var -> showString "UI" . shows var
    VarUP _ var -> showString "UP" . shows var
    SubU _ x y -> chain prec " - " 6 $ x :<| y :<| Empty
    AddU _ x y -> chain prec " + " 6 $ x :<| y :<| Empty
    MulU _ x y -> chain prec " * " 7 $ x :<| y :<| Empty
    MMIU _ x p -> showParen (prec > 8) $ showsPrec 9 x . showString "⁻¹ (mod " . shows p . showString ")"
    AndU _ x0 x1 xs -> chain prec " ∧ " 3 $ x0 :<| x1 :<| xs
    OrU _ x0 x1 xs -> chain prec " ∨ " 2 $ x0 :<| x1 :<| xs
    XorU _ x0 x1 -> chain prec " ⊕ " 4 $ x0 :<| x1 :<| Empty
    NotU _ x -> showParen (prec > 8) $ showString "¬ " . showsPrec 9 x
    IfU _ p x y -> showParen (prec > 1) $ showString "if " . showsPrec 2 p . showString " then " . showsPrec 2 x . showString " else " . showsPrec 2 y
    RoLU _ n x -> showParen (prec > 8) $ showString "RoL " . showsPrec 9 n . showString " " . showsPrec 9 x
    ShLU _ n x -> showParen (prec > 8) $ showString "ShL " . showsPrec 9 n . showString " " . showsPrec 9 x
    SetU _ x i b -> showParen (prec > 8) $ showsPrec 9 x . showString "[" . showsPrec 9 i . showString "] := " . showsPrec 9 b
    BtoU _ x -> showString "B→U " . showsPrec prec x

--------------------------------------------------------------------------------

-- | "Untyped" expression
data Expr n
  = ExprB (ExprB n) -- Boolean expression
  | ExprF (ExprF n) -- Field expression
  | ExprU (ExprU n) -- UInt expression
  deriving (Functor)

chain :: Show n => Int -> String -> Int -> Seq n -> ShowS
chain prec delim n = showParen (prec > n) . go
  where
    go :: Show n => Seq n -> String -> String
    go Empty = showString ""
    go (x :<| Empty) = showsPrec (succ n) x
    go (x :<| xs') = showsPrec (succ n) x . showString delim . go xs'

instance (Integral n, Show n) => Show (Expr n) where
  showsPrec _prec expr = case expr of
    ExprB x -> shows x
    ExprF x -> shows x
    ExprU x -> shows x

-- | Bit width of a unsigned integer expression
widthOfU :: ExprU n -> Width
widthOfU expr = case expr of
  ValU w _ -> w
  VarU w _ -> w
  VarUO w _ -> w
  VarUI w _ -> w
  VarUP w _ -> w
  SubU w _ _ -> w
  AddU w _ _ -> w
  MulU w _ _ -> w
  MMIU w _ _ -> w
  AndU w _ _ _ -> w
  OrU w _ _ _ -> w
  XorU w _ _ -> w
  NotU w _ -> w
  IfU w _ _ _ -> w
  RoLU w _ _ -> w
  ShLU w _ _ -> w
  SetU w _ _ _ -> w
  BtoU w _ -> w

--------------------------------------------------------------------------------

data Assignment n
  = AssignmentF Ref (ExprF n)
  | AssignmentU RefU (ExprU n)
  | AssignmentB RefB (ExprB n)

instance (Integral n, Show n) => Show (Assignment n) where
  show (AssignmentF var expr) = show var ++ " := " ++ show expr
  show (AssignmentU var expr) = show var ++ " := " ++ show expr
  show (AssignmentB var expr) = show var ++ " := " ++ show expr

instance Functor Assignment where
  fmap f (AssignmentF var expr) = AssignmentF var (fmap f expr)
  fmap f (AssignmentU var expr) = AssignmentU var (fmap f expr)
  fmap f (AssignmentB var expr) = AssignmentB var (fmap f expr)

--------------------------------------------------------------------------------

-- | The result after type erasure
data TypeErased n = TypeErased
  { -- | The expression after type erasure
    erasedExpr :: ![(Var, Expr n)],
    -- | Bit width of the chosen field
    erasedFieldBitWidth :: !Width,
    -- | Variable bookkeepung
    erasedCounters :: !Counters,
    -- | Relations between variables and/or expressions
    -- erasedRelations :: !(Relations n),
    -- | Assertions after type erasure
    erasedAssertions :: ![Expr n],
    -- | Side effects
    erasedSideEffects :: !(Seq (SideEffect n))
  }

instance (GaloisField n, Integral n) => Show (TypeErased n) where
  show (TypeErased expr _ counters assertions _sideEffects) =
    "TypeErased {\n"
      -- expressions
      <> "  Expression: "
      <> show (map (fmap N . snd) expr)
      <> "\n"
      -- relations
      -- <> indent (show relations)
      <> ( if length assertions < 20
             then "  assertions:\n    " <> show assertions <> "\n"
             else ""
         )
      -- side effects
      <> Counters.prettyVariables counters
      <> "\n\
         \}"

--------------------------------------------------------------------------------

data SideEffect n
  = AssignmentF2 Var (ExprF n)
  | AssignmentB2 Var (ExprB n)
  | AssignmentU2 Width Var (ExprU n)
  | DivMod Width (ExprU n) (ExprU n) (ExprU n) (ExprU n)
  | AssertLTE Width (ExprU n) Integer
  | AssertLT Width (ExprU n) Integer
  | AssertGTE Width (ExprU n) Integer
  | AssertGT Width (ExprU n) Integer
  deriving (Show, Eq)

--------------------------------------------------------------------------------

lookupF :: Var -> Struct (IntMap f) b u -> Maybe f
lookupF var = IntMap.lookup var . structF

lookupB :: Var -> Struct a (IntMap b) u -> Maybe b
lookupB var = IntMap.lookup var . structB

lookupU :: Width -> Var -> Struct a b (IntMap u) -> Maybe u
lookupU width var bindings = IntMap.lookup var =<< IntMap.lookup width (structU bindings)
