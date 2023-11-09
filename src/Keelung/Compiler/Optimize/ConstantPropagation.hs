{-# LANGUAGE TupleSections #-}

module Keelung.Compiler.Optimize.ConstantPropagation (run) where

import Control.Monad.State
import Data.Field.Galois (GaloisField)
import Data.IntMap (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Keelung.Compiler.Syntax.Internal
import Keelung.Data.Struct (Struct (..))
import Keelung.Data.U qualified as U
import Keelung.Syntax (Var)

--------------------------------------------------------------------------------

run :: (Integral n, GaloisField n) => Internal n -> Internal n
run (Internal exprs fieldWidth counters assertions sideEffects) = runM $ do
  sideEffects' <- mapM propagateSideEffect sideEffects
  Internal
    <$> mapM (\(var, expr) -> (var,) <$> propagateExpr expr) exprs
    <*> pure fieldWidth
    <*> pure counters
    <*> mapM propagateExpr assertions
    <*> pure sideEffects'

type Bindings n = Struct (IntMap n) (IntMap n) (IntMap Integer)

type M n = State (Bindings n)

runM :: State (Bindings n) a -> a
runM program = evalState program mempty

propagateSideEffect :: (Integral n, GaloisField n) => SideEffect n -> M n (SideEffect n)
propagateSideEffect sideEffect = case sideEffect of
  AssignmentF var val -> do
    val' <- propagateExprF val
    case val' of
      ValF v -> modify' $ \bindings -> bindings {structF = IntMap.insert var v (structF bindings)}
      _ -> return ()
    return $ AssignmentF var val'
  AssignmentB var val -> do
    val' <- propagateExprB val
    case val' of
      ValB True -> modify' $ \bindings -> bindings {structB = IntMap.insert var 1 (structB bindings)}
      ValB False -> modify' $ \bindings -> bindings {structB = IntMap.insert var 0 (structB bindings)}
      _ -> return ()
    return $ AssignmentB var val'
  AssignmentU width var val -> do
    val' <- propagateExprU val
    case val' of
      ValU v -> modify' $ \bindings -> bindings {structU = IntMap.insertWith (<>) width (IntMap.singleton width (toInteger v)) (structU bindings)}
      _ -> return ()
    return $ AssignmentU width var val'
  RelateUF width varU varF -> return $ RelateUF width varU varF
  DivMod width dividend divisor quotient remainder ->
    DivMod width
      <$> propagateExprU dividend
      <*> propagateExprU divisor
      <*> propagateExprU quotient
      <*> propagateExprU remainder
  CLDivMod width dividend divisor quotient remainder ->
    CLDivMod width
      <$> propagateExprU dividend
      <*> propagateExprU divisor
      <*> propagateExprU quotient
      <*> propagateExprU remainder
  AssertLTE width expr n -> AssertLTE width <$> propagateExprU expr <*> pure n
  AssertLT width expr n -> AssertLT width <$> propagateExprU expr <*> pure n
  AssertGTE width expr n -> AssertGTE width <$> propagateExprU expr <*> pure n
  AssertGT width expr n -> AssertGT width <$> propagateExprU expr <*> pure n

-- constant propogation
propagateExpr :: (GaloisField n, Integral n) => Expr n -> M n (Expr n)
propagateExpr (ExprB x) = ExprB <$> propagateExprB x
propagateExpr (ExprF x) = ExprF <$> propagateExprF x
propagateExpr (ExprU x) = ExprU <$> propagateExprU x

propagateExprF :: (Eq n, Num n) => ExprF n -> M n (ExprF n)
propagateExprF e = do
  bindings <- get
  case e of
    ValF _ -> return e
    VarF var -> case lookupF var bindings of
      Nothing -> return e
      Just val -> return (ValF val)
    VarFO _ -> return e -- no constant propagation for output variables
    VarFI _ -> return e -- no constant propagation for public input variables
    VarFP _ -> return e -- no constant propagation for private input variables
    SubF x y -> SubF <$> propagateExprF x <*> propagateExprF y
    AddF x y xs -> AddF <$> propagateExprF x <*> propagateExprF y <*> mapM propagateExprF xs
    MulF x y -> MulF <$> propagateExprF x <*> propagateExprF y
    ExpF x n -> ExpF <$> propagateExprF x <*> pure n
    DivF x y -> DivF <$> propagateExprF x <*> propagateExprF y
    IfF p x y -> IfF <$> propagateExprB p <*> propagateExprF x <*> propagateExprF y
    BtoF x -> BtoF <$> propagateExprB x
  where
    lookupF :: Var -> Struct (IntMap f) b u -> Maybe f
    lookupF var = IntMap.lookup var . structF

propagateExprU :: (Eq n, Num n) => ExprU n -> M n (ExprU n)
propagateExprU e = do
  bindings <- get
  case e of
    ValU _ -> return e
    VarU w var -> case lookupU w var bindings of
      Nothing -> return e
      Just val -> return (ValU (U.new w val))
    VarUO _ _ -> return e -- no constant propagation for output variables
    VarUI _ _ -> return e -- no constant propagation for public input variables
    VarUP _ _ -> return e -- no constant propagation for private input variables
    AddU w xs -> AddU w <$> mapM (\(x, sign) -> (,sign) <$> propagateExprU x) xs
    MulU w x y -> MulU w <$> propagateExprU x <*> propagateExprU y
    AESMulU w x y -> AESMulU w <$> propagateExprU x <*> propagateExprU y
    CLMulU w x y -> CLMulU w <$> propagateExprU x <*> propagateExprU y
    CLModU w x y -> CLModU w <$> propagateExprU x <*> propagateExprU y
    MMIU w x p -> MMIU w <$> propagateExprU x <*> pure p
    AndU w xs -> AndU w <$> mapM propagateExprU xs
    OrU w xs -> OrU w <$> mapM propagateExprU xs
    XorU w xs -> XorU w <$> mapM propagateExprU xs
    NotU w x -> NotU w <$> propagateExprU x
    IfU w p x y -> IfU w <$> propagateExprB p <*> propagateExprU x <*> propagateExprU y
    RoLU w i x -> RoLU w i <$> propagateExprU x
    ShLU w i x -> ShLU w i <$> propagateExprU x
    SetU w x i b -> SetU w <$> propagateExprU x <*> pure i <*> propagateExprB b
    BtoU w x -> BtoU w <$> propagateExprB x
  where
    lookupU :: Width -> Var -> Struct a b (IntMap u) -> Maybe u
    lookupU width var bindings = IntMap.lookup var =<< IntMap.lookup width (structU bindings)

propagateExprB :: (Eq n, Num n) => ExprB n -> M n (ExprB n)
propagateExprB e = do
  bindings <- get
  case e of
    ValB _ -> return e
    VarB var -> case lookupB var bindings of
      Nothing -> return e
      Just 1 -> return (ValB True)
      Just _ -> return (ValB False)
    VarBO _ -> return e -- no constant propagation for output variables
    VarBI _ -> return e -- no constant propagation for public input variables
    VarBP _ -> return e -- no constant propagation for private input variables
    AndB xs -> AndB <$> mapM propagateExprB xs
    OrB xs -> OrB <$> mapM propagateExprB xs
    XorB xs -> XorB <$> mapM propagateExprB xs
    NotB x -> NotB <$> propagateExprB x
    IfB p x y -> IfB <$> propagateExprB p <*> propagateExprB x <*> propagateExprB y
    NEqB x y -> NEqB <$> propagateExprB x <*> propagateExprB y
    NEqF x y -> NEqF <$> propagateExprF x <*> propagateExprF y
    -- NEqU x y -> NEqU <$> propagateExprU x <*> propagateExprU y
    EqB x y -> EqB <$> propagateExprB x <*> propagateExprB y
    EqF x y -> EqF <$> propagateExprF x <*> propagateExprF y
    EqU x y -> EqU <$> propagateExprU x <*> propagateExprU y
    LTU x y -> LTU <$> propagateExprU x <*> propagateExprU y
    LTEU x y -> LTEU <$> propagateExprU x <*> propagateExprU y
    GTU x y -> GTU <$> propagateExprU x <*> propagateExprU y
    GTEU x y -> GTEU <$> propagateExprU x <*> propagateExprU y
    BitU x i -> BitU <$> propagateExprU x <*> pure i
  where
    lookupB :: Var -> Struct a (IntMap b) u -> Maybe b
    lookupB var = IntMap.lookup var . structB
