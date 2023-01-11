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
    Relations (..),
    -- sizeOfExpr,
  )
where

import Data.Field.Galois (GaloisField)
import Data.IntMap (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.Sequence (Seq (..))
import Keelung.Compiler.Constraint
import Keelung.Data.Struct (Struct (..))
import qualified Keelung.Data.Struct as Struct
import Keelung.Field (N (..))
import Keelung.Syntax.Counters
import qualified Keelung.Syntax.Counters as Counters
import Keelung.Types (Var, Width)

--------------------------------------------------------------------------------

data ExprB n
  = ValB n
  | VarB Var
  | VarBO Var
  | VarBI Var
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
  | BitU (ExprU n) Int
  deriving (Functor, Eq)

instance (Integral n, Show n) => Show (ExprB n) where
  showsPrec prec expr = case expr of
    ValB 0 -> showString "F"
    ValB _ -> showString "T"
    VarB var -> showString "$B" . shows var
    VarBO var -> showString "$BO" . shows var
    VarBI var -> showString "$BI" . shows var
    AndB x0 x1 xs -> chain prec " ∧ " 3 $ x0 :<| x1 :<| xs
    OrB x0 x1 xs -> chain prec " ∨ " 2 $ x0 :<| x1 :<| xs
    XorB x0 x1 -> chain prec " ⊕ " 4 $ x0 :<| x1 :<| Empty
    NotB x -> chain prec "¬ " 5 $ x :<| Empty
    IfB p x y -> showParen (prec > 1) $ showString "if " . showsPrec 2 p . showString " then " . showsPrec 2 x . showString " else " . showsPrec 2 y
    NEqB x0 x1 -> chain prec " != " 5 $ x0 :<| x1 :<| Empty
    NEqF x0 x1 -> chain prec " != " 5 $ x0 :<| x1 :<| Empty
    NEqU x0 x1 -> chain prec " != " 5 $ x0 :<| x1 :<| Empty
    EqB x0 x1 -> chain prec " == " 5 $ x0 :<| x1 :<| Empty
    EqF x0 x1 -> chain prec " == " 5 $ x0 :<| x1 :<| Empty
    EqU x0 x1 -> chain prec " == " 5 $ x0 :<| x1 :<| Empty
    BitU x i -> showsPrec prec x . showString "[" . shows i . showString "]"

--------------------------------------------------------------------------------

data ExprF n
  = ValF n
  | VarF Var
  | VarFO Var
  | VarFI Var
  | -- arithmetic operators
    SubF (ExprF n) (ExprF n)
  | AddF (ExprF n) (ExprF n) (Seq (ExprF n))
  | MulF (ExprF n) (ExprF n)
  | DivF (ExprF n) (ExprF n)
  | -- logical operators
    IfF (ExprB n) (ExprF n) (ExprF n)
  | BtoF (ExprB n)
  deriving (Functor, Eq)

instance (Show n, Integral n) => Show (ExprF n) where
  showsPrec prec expr = case expr of
    ValF n -> shows n
    VarF var -> showString "$N" . shows var
    VarFO var -> showString "$NO" . shows var
    VarFI var -> showString "$NI" . shows var
    SubF x y -> chain prec " - " 6 $ x :<| y :<| Empty
    AddF x0 x1 xs -> chain prec " + " 6 $ x0 :<| x1 :<| xs
    MulF x y -> chain prec " * " 7 $ x :<| y :<| Empty
    DivF x y -> chain prec " / " 7 $ x :<| y :<| Empty
    IfF p x y -> showParen (prec > 1) $ showString "if " . showsPrec 2 p . showString " then " . showsPrec 2 x . showString " else " . showsPrec 2 y
    BtoF x -> showString "B→F " . showsPrec prec x

--------------------------------------------------------------------------------

data ExprU n
  = ValU Width n
  | VarU Width Var
  | VarUO Width Var
  | VarUI Width Var
  | -- arithmetic operators
    SubU Width (ExprU n) (ExprU n)
  | AddU Width (ExprU n) (ExprU n)
  | MulU Width (ExprU n) (ExprU n)
  | -- logical operators
    AndU Width (ExprU n) (ExprU n) (Seq (ExprU n))
  | OrU Width (ExprU n) (ExprU n) (Seq (ExprU n))
  | XorU Width (ExprU n) (ExprU n)
  | NotU Width (ExprU n)
  | IfU Width (ExprB n) (ExprU n) (ExprU n)
  | RoLU Width Int (ExprU n)
  | ShLU Width Int (ExprU n)
  | BtoU Width (ExprB n)
  deriving (Functor, Eq)

instance (Show n, Integral n) => Show (ExprU n) where
  showsPrec prec expr = case expr of
    ValU _ n -> shows n
    VarU _ var -> showString "$U" . shows var
    VarUO _ var -> showString "$UO" . shows var
    VarUI _ var -> showString "$UI" . shows var
    SubU _ x y -> chain prec " - " 6 $ x :<| y :<| Empty
    AddU _ x y -> chain prec " + " 6 $ x :<| y :<| Empty
    MulU _ x y -> chain prec " * " 7 $ x :<| y :<| Empty
    AndU _ x0 x1 xs -> chain prec " ∧ " 3 $ x0 :<| x1 :<| xs
    OrU _ x0 x1 xs -> chain prec " ∨ " 2 $ x0 :<| x1 :<| xs
    XorU _ x0 x1 -> chain prec " ⊕ " 4 $ x0 :<| x1 :<| Empty
    NotU _ x -> showParen (prec > 8) $ showString "¬ " . showsPrec 9 x
    IfU _ p x y -> showParen (prec > 1) $ showString "if " . showsPrec 2 p . showString " then " . showsPrec 2 x . showString " else " . showsPrec 2 y
    RoLU _ n x -> showParen (prec > 8) $ showString "RoL " . showsPrec 9 n . showString " " . showsPrec 9 x
    ShLU _ n x -> showParen (prec > 8) $ showString "ShL " . showsPrec 9 n . showString " " . showsPrec 9 x
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
  SubU w _ _ -> w
  AddU w _ _ -> w
  MulU w _ _ -> w
  AndU w _ _ _ -> w
  OrU w _ _ _ -> w
  XorU w _ _ -> w
  NotU w _ -> w
  IfU w _ _ _ -> w
  RoLU w _ _ -> w
  ShLU w _ _ -> w
  BtoU w _ -> w

--------------------------------------------------------------------------------

data Assignment n
  = AssignmentF RefF (ExprF n)
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
    erasedRelations :: !(Relations n),
    -- | Assertions after type erasure
    erasedAssertions :: ![Expr n]
  }

instance (GaloisField n, Integral n) => Show (TypeErased n) where
  show (TypeErased expr _ counters relations assertions) =
    "TypeErased {\n"
      -- expressions
      <> "  Expression: "
      <> show (map (fmap N. snd) expr)
      <> "\n"
      -- relations
      <> show relations
      <> ( if length assertions < 20
             then "  assertions:\n    " <> show assertions <> "\n"
             else ""
         )
      <> Counters.prettyVariables counters
      <> "\n\
         \}"

--------------------------------------------------------------------------------

lookupF :: Var -> Struct (IntMap f) b u -> Maybe f
lookupF var = IntMap.lookup var . structF

lookupB :: Var -> Struct a (IntMap b) u -> Maybe b
lookupB var = IntMap.lookup var . structB

lookupU :: Width -> Var -> Struct a b (IntMap u) -> Maybe u
lookupU width var bindings = IntMap.lookup var =<< IntMap.lookup width (structU bindings)

--------------------------------------------------------------------------------

data Relations n = Relations
  { -- var = value
    valueBindings :: Struct (IntMap n) (IntMap n) (IntMap n),
    valueBindingsI :: Struct (IntMap n) (IntMap n) (IntMap n),
    -- var = expression
    exprBindings :: Struct (IntMap (ExprF n)) (IntMap (ExprB n)) (IntMap (ExprU n)),
    exprBindingsI :: Struct (IntMap (ExprF n)) (IntMap (ExprB n)) (IntMap (ExprU n))
  }

instance (Integral n, Show n) => Show (Relations n) where
  show (Relations vb vbi eb ebi) =
    ( if Struct.empty vb
        then ""
        else "Binding of intermediate variables to values:\n" <> show vb <> "\n"
    )
      <> ( if Struct.empty vbi
             then ""
             else "Binding of input variables to values:\n" <> show vb <> "\n"
         )
      <> ( if Struct.empty eb
             then ""
             else "Binding of intermediate variables to expressions:\n" <> show eb <> "\n"
         )
      <> ( if Struct.empty ebi
             then ""
             else "Binding of input variables to expressions:\n" <> show ebi <> "\n"
         )

instance Semigroup (Relations n) where
  Relations vb0 vbi0 eb0 ebi0 <> Relations vb1 vbi1 eb1 ebi1 =
    Relations
      (vb0 <> vb1)
      (vbi0 <> vbi1)
      (eb0 <> eb1)
      (ebi0 <> ebi1)

instance Monoid (Relations n) where
  mempty = Relations mempty mempty mempty mempty
