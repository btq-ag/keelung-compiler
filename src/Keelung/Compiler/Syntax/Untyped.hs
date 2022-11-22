{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}

module Keelung.Compiler.Syntax.Untyped
  ( Op (..),
    BitWidth (..),
    Width,
    bitWidthOf,
    getWidth,
    castToNumber,
    narrowDownToExprN,
    narrowDownToExprU,
    narrowDownToExprB,
    Expr (..),
    ExprB (..),
    ExprN (..),
    ExprU (..),
    TypeErased (..),
    Assignment (..),
    Bindings (..),
    insertN,
    insertB,
    insertU,
    lookupN,
    lookupB,
    lookupU,
    Relations (..),
    sizeOfExpr,
  )
where

import Data.Field.Galois (GaloisField)
import Data.IntMap (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.Sequence (Seq (..))
import Keelung.Field (N (..))
import Keelung.Syntax.BinRep (BinReps)
import qualified Keelung.Syntax.BinRep as BinRep
import Keelung.Syntax.VarCounters
import Keelung.Types (Var)

--------------------------------------------------------------------------------

-- N-ary operators
data Op
  = Or
  | Xor
  | NEq
  | Eq
  | BEq
  deriving (Eq, Show)

--------------------------------------------------------------------------------

type Width = Int

data BitWidth
  = BWNumber Width
  | BWBoolean
  | BWUInt Width
  | BWUnit
  | BWArray BitWidth Int
  deriving (Eq, Ord, Show)

getWidth :: BitWidth -> Width
getWidth (BWNumber n) = n
getWidth BWBoolean = 1
getWidth (BWUInt n) = n
getWidth BWUnit = 0
getWidth (BWArray ns n) = n * getWidth ns

--------------------------------------------------------------------------------

data ExprB n
  = ValB n
  | VarB Var
  | -- logical operators
    AndB (ExprB n) (ExprB n) (Seq (ExprB n))
  | IfB (ExprB n) (ExprB n) (ExprB n)
  deriving (Functor)

instance (Integral n, Show n) => Show (ExprB n) where
  showsPrec prec expr = case expr of
    ValB 0 -> showString "F"
    ValB _ -> showString "T"
    VarB var -> showString "$" . shows var
    AndB x0 x1 xs -> chain prec " ∧ " 3 $ x0 :<| x1 :<| xs
    IfB p x y -> showParen (prec > 1) $ showString "if " . showsPrec 2 p . showString " then " . showsPrec 2 x . showString " else " . showsPrec 2 y

--------------------------------------------------------------------------------

data ExprN n
  = ValN Width n
  | VarN Width Var
  | -- arithmetic operators
    SubN Width (ExprN n) (ExprN n)
  | AddN Width (ExprN n) (ExprN n) (Seq (ExprN n))
  | MulN Width (ExprN n) (ExprN n)
  | DivN Width (ExprN n) (ExprN n)
  | -- logical operators
    IfN Width (ExprB n) (ExprN n) (ExprN n)
  deriving (Functor)

instance (Show n, Integral n) => Show (ExprN n) where
  showsPrec prec expr = case expr of
    ValN _ n -> shows n
    VarN _ var -> showString "$" . shows var
    SubN _ x y -> chain prec " - " 6 $ x :<| y :<| Empty
    AddN _ x0 x1 xs -> chain prec " + " 6 $ x0 :<| x1 :<| xs
    MulN _ x y -> chain prec " * " 7 $ x :<| y :<| Empty
    DivN _ x y -> chain prec " / " 7 $ x :<| y :<| Empty
    IfN _ p x y -> showParen (prec > 1) $ showString "if " . showsPrec 2 p . showString " then " . showsPrec 2 x . showString " else " . showsPrec 2 y

--------------------------------------------------------------------------------

data ExprU n
  = ValU Width n
  | VarU Width Var
  | -- arithmetic operators
    SubU Width (ExprU n) (ExprU n)
  | AddU Width (ExprU n) (ExprU n)
  | MulU Width (ExprU n) (ExprU n)
  | -- logical operators
    AndU Width (ExprU n) (ExprU n) (Seq (ExprU n))
  | IfU Width (ExprB n) (ExprU n) (ExprU n)
  deriving (Functor)

instance (Show n, Integral n) => Show (ExprU n) where
  showsPrec prec expr = case expr of
    ValU _ n -> shows n
    VarU _ var -> showString "$" . shows var
    SubU _ x y -> chain prec " - " 6 $ x :<| y :<| Empty
    AddU _ x y -> chain prec " + " 6 $ x :<| y :<| Empty
    MulU _ x y -> chain prec " * " 7 $ x :<| y :<| Empty
    AndU _ x0 x1 xs -> chain prec " ∧ " 3 $ x0 :<| x1 :<| xs
    IfU _ p x y -> showParen (prec > 1) $ showString "if " . showsPrec 2 p . showString " then " . showsPrec 2 x . showString " else " . showsPrec 2 y

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
  | ExprN (ExprN n) -- Field expression
  | ExprU (ExprU n) -- UInt expression
  | Rotate BitWidth Int (Expr n)
  | -- N-Ary operators with >= 2 operands
    NAryOp BitWidth Op (Expr n) (Expr n) (Seq (Expr n))
  deriving (Functor)

instance Num n => Num (ExprN n) where
  x + y = AddN (widthOfN x) x y Empty
  x - y = SubN (widthOfN x) x y
  x * y = MulN (widthOfN x) x y
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
  showsPrec prec expr = case expr of
    ExprB x -> shows x
    ExprN x -> shows x
    ExprU x -> shows x
    Rotate _ n x -> showString "ROTATE " . shows n . showString " " . showsPrec 11 x
    NAryOp _ op x0 x1 xs -> case op of
      Or -> chain prec " ∨ " 2 $ x0 :<| x1 :<| xs
      Xor -> chain prec " ⊕ " 4 $ x0 :<| x1 :<| xs
      NEq -> chain prec " != " 5 $ x0 :<| x1 :<| xs
      Eq -> chain prec " == " 5 $ x0 :<| x1 :<| xs
      BEq -> chain prec " == " 5 $ x0 :<| x1 :<| xs

-- | Calculate the "size" of an expression for benchmarking
sizeOfExpr :: Expr n -> Int
sizeOfExpr expr = case expr of
  ExprN x -> sizeOfExprN x
  ExprB x -> sizeOfExprB x
  ExprU x -> sizeOfExprU x
  Rotate _ _ x -> 1 + sizeOfExpr x
  NAryOp _ _ x0 x1 xs ->
    let operands = x0 :<| x1 :<| xs
     in sum (fmap sizeOfExpr operands) + (length operands - 1)

sizeOfExprB :: ExprB n -> Int
sizeOfExprB expr = case expr of
  ValB _ -> 1
  VarB _ -> 1
  AndB x0 x1 xs ->
    let operands = x0 :<| x1 :<| xs
     in sum (fmap sizeOfExprB operands) + (length operands - 1)
  IfB x y z -> 1 + sizeOfExprB x + sizeOfExprB y + sizeOfExprB z

sizeOfExprN :: ExprN n -> Int
sizeOfExprN xs = case xs of
  ValN _ _ -> 1
  VarN _ _ -> 1
  SubN _ x y -> sizeOfExprN x + sizeOfExprN y + 1
  AddN _ x0 x1 xs' ->
    let operands = x0 :<| x1 :<| xs'
     in sum (fmap sizeOfExprN operands) + (length operands - 1)
  MulN _ x y -> sizeOfExprN x + sizeOfExprN y + 1
  DivN _ x y -> sizeOfExprN x + sizeOfExprN y + 1
  IfN _ p x y -> 1 + sizeOfExprB p + sizeOfExprN x + sizeOfExprN y

sizeOfExprU :: ExprU n -> Int
sizeOfExprU xs = case xs of
  ValU _ _ -> 1
  VarU _ _ -> 1
  SubU _ x y -> sizeOfExprU x + sizeOfExprU y + 1
  AddU _ x y -> sizeOfExprU x + sizeOfExprU y + 1
  MulU _ x y -> sizeOfExprU x + sizeOfExprU y + 1
  AndU _ x0 x1 xs' ->
    let operands = x0 :<| x1 :<| xs'
     in sum (fmap sizeOfExprU operands) + (length operands - 1)
  IfU _ p x y -> 1 + sizeOfExprB p + sizeOfExprU x + sizeOfExprU y

bitWidthOf :: Expr n -> BitWidth
bitWidthOf expr = case expr of
  ExprB _ -> BWBoolean
  ExprN x -> BWNumber $ widthOfN x
  ExprU x -> BWUInt $ widthOfU x
  Rotate bw _ _ -> bw
  NAryOp bw _ _ _ _ -> bw

widthOfN :: ExprN n -> Width
widthOfN expr = case expr of
  ValN w _ -> w
  VarN w _ -> w
  SubN w _ _ -> w
  AddN w _ _ _ -> w
  MulN w _ _ -> w
  DivN w _ _ -> w
  IfN w _ _ _ -> w

widthOfU :: ExprU n -> Width
widthOfU expr = case expr of
  ValU w _ -> w
  VarU w _ -> w
  SubU w _ _ -> w
  AddU w _ _ -> w
  MulU w _ _ -> w
  AndU w _ _ _ -> w
  IfU w _ _ _ -> w

castToNumber :: Width -> Expr n -> Expr n
castToNumber width expr = case expr of
  ExprB x -> case x of
    ValB val -> ExprN (ValN width val)
    VarB var -> ExprN (VarN width var)
    AndB {} -> error "[ panic ] castToNumber: AndB"
    IfB {} -> error "[ panic ] castToNumber: IfB"
  ExprN x -> case x of
    ValN _ val -> ExprN (ValN width val)
    VarN _ var -> ExprN (VarN width var)
    SubN _ a b -> ExprN (SubN width a b)
    AddN _ a b xs -> ExprN (AddN width a b xs)
    MulN _ a b -> ExprN (MulN width a b)
    DivN _ a b -> ExprN (DivN width a b)
    IfN _ p a b -> ExprN (IfN width p a b)
  ExprU x -> case x of
    ValU _ val -> ExprN (ValN width val)
    VarU _ var -> ExprN (VarN width var)
    SubU _ a b ->
      ExprN $
        SubN
          width
          (narrowDownToExprN (castToNumber width (ExprU a)))
          (narrowDownToExprN (castToNumber width (ExprU b)))
    AddU _ a b -> ExprN (AddN width (narrowDownToExprN $ castToNumber width (ExprU a)) (narrowDownToExprN $ castToNumber width (ExprU b)) Empty)
    MulU _ a b -> ExprN (MulN width (narrowDownToExprN $ castToNumber width (ExprU a)) (narrowDownToExprN $ castToNumber width (ExprU b)))
    AndU {} -> error "[ panic ] castToNumber: AndU"
    IfU _ p a b -> ExprN (IfN width p (narrowDownToExprN $ castToNumber width (ExprU a)) (narrowDownToExprN $ castToNumber width (ExprU b)))
  Rotate _ n x -> Rotate (BWNumber width) n x
  NAryOp _ op a b c -> NAryOp (BWNumber width) op a b c

-- NOTE: temporary hack, should be removed
narrowDownToExprN :: Expr n -> ExprN n
narrowDownToExprN x = case x of
  ExprN x' -> x'
  _ -> error "[ panic ] Expected ExprN"

narrowDownToExprU :: Expr n -> ExprU n
narrowDownToExprU x = case x of
  ExprU x' -> x'
  _ -> error "[ panic ] Expected ExprU"

narrowDownToExprB :: Expr n -> ExprB n
narrowDownToExprB x = case x of
  ExprB x' -> x'
  _ -> error "[ panic ] Expected ExprB"

--------------------------------------------------------------------------------

data Assignment n = Assignment Var (Expr n)

instance (Integral n, Show n) => Show (Assignment n) where
  show (Assignment var expr) = "$" <> show var <> " := " <> show expr

instance Functor Assignment where
  fmap f (Assignment var expr) = Assignment var (fmap f expr)

--------------------------------------------------------------------------------

-- | The result after type erasure
data TypeErased n = TypeErased
  { -- | The expression after type erasure
    erasedExpr :: ![Expr n],
    -- | Variable bookkeepung
    erasedVarCounters :: !VarCounters,
    -- | Relations between variables and/or expressions
    erasedRelations :: !(Relations n),
    -- | Assertions after type erasure
    erasedAssertions :: ![Expr n],
    -- | Assignments after type erasure
    erasedAssignments :: ![Assignment n],
    -- | Binary representation of Number inputs
    erasedBinReps :: BinReps,
    -- | Binary representation of custom inputs
    erasedCustomBinReps :: BinReps
  }

instance (GaloisField n, Integral n) => Show (TypeErased n) where
  show (TypeErased expr counters relations assertions assignments numBinReps customBinReps) =
    "TypeErased {\n"
      -- expressions
      <> " . expression: "
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
      <> indent (show counters)
      <> "  Boolean variables: $"
      <> show (fst (boolVarsRange counters))
      <> " .. $"
      <> show (snd (boolVarsRange counters) - 1)
      <> "\n"
      <> showBinRepConstraints
      <> "\n\
         \}"
    where
      totalBinRepConstraintSize = numInputVarSize counters + totalCustomInputSize counters
      showBinRepConstraints =
        if totalBinRepConstraintSize == 0
          then ""
          else
            "  Binary representation constriants (" <> show totalBinRepConstraintSize <> "):\n"
              <> unlines
                ( map
                    (("    " <>) . show)
                    (BinRep.toList (numBinReps <> customBinReps))
                )

--------------------------------------------------------------------------------

-- | Container for holding something for each datatypes
data Bindings n = Bindings
  { bindingsN :: IntMap n, -- Field elements
    bindingsB :: IntMap n, -- Booleans
    bindingsUs :: IntMap (IntMap n) -- Unsigned integers of different bitwidths
  }
  deriving (Eq, Functor)

instance Semigroup (Bindings n) where
  Bindings n0 b0 u0 <> Bindings n1 b1 u1 =
    Bindings (n0 <> n1) (b0 <> b1) (IntMap.unionWith (<>) u0 u1)

instance Monoid (Bindings n) where
  mempty = Bindings mempty mempty mempty

instance Show n => Show (Bindings n) where
  show (Bindings ns bs us) =
    "  Field elements: "
      <> unlines (map (("    " <>) . show) (IntMap.toList ns))
      <> "\n"
      <> "  Booleans: "
      <> unlines (map (("    " <>) . show) (IntMap.toList bs))
      <> "\n"
      <> "  Unsigned integers: "
      <> unlines
        ( map
            (("    " <>) . show)
            (concat $ IntMap.elems (fmap IntMap.toList us))
        )
      <> "\n"

instance Foldable Bindings where
  foldMap f (Bindings ns bs us) =
    foldMap f ns <> foldMap f bs <> foldMap (foldMap f) us

instance Traversable Bindings where
  traverse f (Bindings ns bs us) =
    Bindings <$> traverse f ns <*> traverse f bs <*> traverse (traverse f) us

insertN :: Var -> n -> Bindings n -> Bindings n
insertN var val (Bindings ns bs us) = Bindings (IntMap.insert var val ns) bs us

insertB :: Var -> n -> Bindings n -> Bindings n
insertB var val (Bindings ns bs us) = Bindings ns (IntMap.insert var val bs) us

insertU :: Var -> Width -> n -> Bindings n -> Bindings n
insertU var width val (Bindings ns bs us) = Bindings ns bs (IntMap.insertWith (<>) width (IntMap.singleton var val) us)

lookupN :: Var -> Bindings n -> Maybe n
lookupN var (Bindings ns _ _) = IntMap.lookup var ns

lookupB :: Var -> Bindings n -> Maybe n
lookupB var (Bindings _ bs _) = IntMap.lookup var bs

lookupU :: Width -> Var -> Bindings n -> Maybe n
lookupU width var (Bindings _ _ us) = IntMap.lookup width us >>= IntMap.lookup var

-- data Mixed n = MixedN Var n | MixedB Var n | MixedU Width Var n
--   deriving (Eq, Ord, Show)

-- pairWithKey :: Bindings n -> Bindings (Mixed n)
-- pairWithKey (Bindings ns bs us) =
--   Bindings (IntMap.mapWithKey MixedN ns) (IntMap.mapWithKey MixedB bs) (IntMap.mapWithKey (IntMap.mapWithKey . MixedU) us)

-- stripKey :: Bindings (Mixed n) -> Bindings n
-- stripKey (Bindings ns bs us) =
--   Bindings (fmap (\(MixedN _ n) -> n) ns) (fmap (\(MixedB _ n) -> n) bs) (fmap (fmap (\(MixedU _ _ n) -> n)) us)

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
