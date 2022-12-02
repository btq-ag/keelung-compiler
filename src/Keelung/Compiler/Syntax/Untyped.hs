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
    Bindings (..),
    insertF,
    insertB,
    insertU,
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
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Sequence (Seq (..))
import Keelung.Compiler.Constraint2
import Keelung.Field (N (..))
import Keelung.Syntax.Counters
import qualified Keelung.Syntax.Counters as Counters
import Keelung.Types (Var, Width)

--------------------------------------------------------------------------------

data ExprB n
  = ValB n
  | VarB Var
  | OutputVarB Var
  | InputVarB Var
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
  deriving (Functor)

instance (Integral n, Show n) => Show (ExprB n) where
  showsPrec prec expr = case expr of
    ValB 0 -> showString "F"
    ValB _ -> showString "T"
    VarB var -> showString "$B" . shows var
    OutputVarB var -> showString "$BO" . shows var
    InputVarB var -> showString "$BI" . shows var
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
  = ValF Width n
  | VarF Width Var
  | VarFO Width Var
  | VarFI Width Var
  | -- arithmetic operators
    SubF Width (ExprF n) (ExprF n)
  | AddF Width (ExprF n) (ExprF n) (Seq (ExprF n))
  | MulF Width (ExprF n) (ExprF n)
  | DivF Width (ExprF n) (ExprF n)
  | -- logical operators
    IfF Width (ExprB n) (ExprF n) (ExprF n)
  | BtoF Width (ExprB n)
  deriving (Functor)

instance (Show n, Integral n) => Show (ExprF n) where
  showsPrec prec expr = case expr of
    ValF _ n -> shows n
    VarF _ var -> showString "$N" . shows var
    VarFO _ var -> showString "$NO" . shows var
    VarFI _ var -> showString "$NI" . shows var
    SubF _ x y -> chain prec " - " 6 $ x :<| y :<| Empty
    AddF _ x0 x1 xs -> chain prec " + " 6 $ x0 :<| x1 :<| xs
    MulF _ x y -> chain prec " * " 7 $ x :<| y :<| Empty
    DivF _ x y -> chain prec " / " 7 $ x :<| y :<| Empty
    IfF _ p x y -> showParen (prec > 1) $ showString "if " . showsPrec 2 p . showString " then " . showsPrec 2 x . showString " else " . showsPrec 2 y
    BtoF _ x -> showString "B→F " . showsPrec prec x

--------------------------------------------------------------------------------

data ExprU n
  = ValU Width n
  | VarU Width Var
  | OutputVarU Width Var
  | InputVarU Width Var
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
  deriving (Functor)

instance (Show n, Integral n) => Show (ExprU n) where
  showsPrec prec expr = case expr of
    ValU _ n -> shows n
    VarU _ var -> showString "$U" . shows var
    OutputVarU _ var -> showString "$UO" . shows var
    InputVarU _ var -> showString "$UI" . shows var
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

instance Num n => Num (ExprU n) where
  x + y = AddU (widthOfU x) x y
  x - y = SubU (widthOfU x) x y
  x * y = MulU (widthOfU x) x y
  abs = id
  signum = const 1
  fromInteger = error "[ panic ] Dunno how to convert an Integer to an UInt"

--------------------------------------------------------------------------------

-- | "Untyped" expression
data Expr n
  = ExprB (ExprB n) -- Boolean expression
  | ExprF (ExprF n) -- Field expression
  | ExprU (ExprU n) -- UInt expression
  deriving (Functor)

instance Num n => Num (ExprF n) where
  x + y = AddF (widthOfF x) x y Empty
  x - y = SubF (widthOfF x) x y
  x * y = MulF (widthOfF x) x y
  abs = id
  signum = const 1
  fromInteger = error "[ panic ] Dunno how to convert an Integer to a Number"

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

widthOfF :: ExprF n -> Width
widthOfF expr = case expr of
  ValF w _ -> w
  VarF w _ -> w
  VarFI w _ -> w
  VarFO w _ -> w
  SubF w _ _ -> w
  AddF w _ _ _ -> w
  MulF w _ _ -> w
  DivF w _ _ -> w
  IfF w _ _ _ -> w
  BtoF w _ -> w

widthOfU :: ExprU n -> Width
widthOfU expr = case expr of
  ValU w _ -> w
  VarU w _ -> w
  OutputVarU w _ -> w
  InputVarU w _ -> w
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
    erasedExpr :: ![Expr n],
    -- | Bit width of the chosen field
    erasedFieldBitWidth :: !Width,
    -- | Variable bookkeepung
    erasedCounters :: !Counters,
    -- | Relations between variables and/or expressions
    erasedRelations :: !(Relations n),
    -- | Assertions after type erasure
    erasedAssertions :: ![Expr n],
    -- | Assignments after type erasure
    erasedAssignments :: ![Assignment n]
  }

instance (GaloisField n, Integral n) => Show (TypeErased n) where
  show (TypeErased expr _ counters relations assertions assignments) =
    "TypeErased {\n"
      -- expressions
      <> "  Expression: "
      <> show (fmap (fmap N) expr)
      <> "\n"
      -- relations
      <> show relations
      <> ( if length assignments < 20
             then "  assignments:\n    " <> show (map (fmap N) assignments) <> "\n"
             else ""
         )
      <> ( if length assertions < 20
             then "  assertions:\n    " <> show assertions <> "\n"
             else ""
         )
      <> Counters.prettyVariables counters
      <> "\n\
         \}"
    

--------------------------------------------------------------------------------

-- | Container for holding something for each datatypes
data Bindings n = Bindings
  { bindingsF :: Map RefF n, -- Field elements
    bindingsB :: Map RefB n, -- Booleans
    bindingsUs :: IntMap (Map RefU n) -- Unsigned integers of different bitwidths
  }
  deriving (Eq, Functor, Show)

instance Semigroup (Bindings n) where
  Bindings n0 b0 u0 <> Bindings n1 b1 u1 =
    Bindings (n0 <> n1) (b0 <> b1) (IntMap.unionWith (<>) u0 u1)

instance Monoid (Bindings n) where
  mempty = Bindings mempty mempty mempty

-- instance Show n => Show (Bindings n) where
--   show (Bindings fs bs us) =
--     "  Field elements: "
--       <> unlines (map (("    " <>) . show) (IntMap.toList ns))
--       <> "\n"
--       <> "  Booleans: "
--       <> unlines (map (("    " <>) . show) (IntMap.toList bs))
--       <> "\n"
--       <> "  Unsigned integers: "
--       <> unlines
--         ( map
--             (("    " <>) . show)
--             (concat $ IntMap.elems (fmap IntMap.toList us))
--         )
--       <> "\n"

instance Foldable Bindings where
  foldMap f (Bindings fs bs us) =
    foldMap f fs <> foldMap f bs <> foldMap (foldMap f) us

instance Traversable Bindings where
  traverse f (Bindings fs bs us) =
    Bindings <$> traverse f fs <*> traverse f bs <*> traverse (traverse f) us

insertF :: RefF -> n -> Bindings n -> Bindings n
insertF var val (Bindings fs bs us) = Bindings (Map.insert var val fs) bs us

insertB :: RefB -> n -> Bindings n -> Bindings n
insertB var val (Bindings fs bs us) = Bindings fs (Map.insert var val bs) us

insertU :: Width -> RefU -> n -> Bindings n -> Bindings n
insertU width var val (Bindings fs bs us) = Bindings fs bs (IntMap.insertWith (<>) width (Map.singleton var val) us)

lookupF :: RefF -> Bindings n -> Maybe n
lookupF var (Bindings fs _ _) = Map.lookup var fs

lookupB :: RefB -> Bindings n -> Maybe n
lookupB var (Bindings _ bs _) = Map.lookup var bs

lookupU :: Width -> RefU -> Bindings n -> Maybe n
lookupU width var (Bindings _ _ us) = IntMap.lookup width us >>= Map.lookup var

--------------------------------------------------------------------------------

data Relations n = Relations
  { -- var = value
    valueBindings :: Bindings n,
    -- var = expression
    exprBindings :: Bindings (Expr n)
    -- [| expression |] = True
  }

instance (Integral n, Show n) => Show (Relations n) where
  show (Relations vbs ebs) =
    "Binding of variables to values:\n" <> show vbs <> "\n"
      <> "Binding of variables to expressions:\n"
      <> show ebs
      <> "\n"

instance Semigroup (Relations n) where
  Relations vbs0 ebs0 <> Relations vbs1 ebs1 =
    Relations (vbs0 <> vbs1) (ebs0 <> ebs1)

instance Monoid (Relations n) where
  mempty = Relations mempty mempty
