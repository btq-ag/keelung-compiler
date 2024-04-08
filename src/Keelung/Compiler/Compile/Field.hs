module Keelung.Compiler.Compile.Field (compile) where

import Data.Field.Galois (GaloisField)
import Data.Foldable (Foldable (toList))
import Data.Sequence (Seq (..))
import Keelung.Compiler.Compile.Field.Conditional qualified as Conditional
import Keelung.Compiler.Compile.Field.Exponentiation qualified as Exponentiation
import Keelung.Compiler.Compile.Monad
import Keelung.Compiler.Syntax.Internal
import Keelung.Data.LC ( LC(..), (@), (*.), neg )
import Keelung.Data.Reference

----------------------------------------------------------------

compile :: (GaloisField n, Integral n) => ExprF n -> M n (LC n)
compile expr = case expr of
  ValF val -> return $ Constant val
  VarF var -> return $ 1 @ F (RefFX var)
  VarFO var -> return $ 1 @ F (RefFO var)
  VarFI var -> return $ 1 @ F (RefFI var)
  VarFP var -> return $ 1 @ F (RefFP var)
  SubF x y -> do
    x' <- compile x
    y' <- compile y
    return $ x' <> neg y'
  AddF x y rest -> do
    operands <- mapM compile (toList (x :<| y :<| rest))
    return $ mconcat operands
  MulF (ValF m) (ValF n) -> return $ Constant (m * n)
  MulF (VarF var) (ValF n) -> return $ n @ F (RefFX var)
  MulF (VarFI var) (ValF n) -> return $ n @ F (RefFI var)
  MulF (VarFO var) (ValF n) -> return $ n @ F (RefFX var)
  MulF (ValF n) (VarF var) -> return $ n @ F (RefFX var)
  MulF (ValF n) (VarFI var) -> return $ n @ F (RefFI var)
  MulF (ValF n) (VarFO var) -> return $ n @ F (RefFO var)
  MulF (ValF n) y -> do
    result <- compile y
    case result of
      Constant val -> return $ Constant (val * n)
      Polynomial poly -> return $ n *. Polynomial poly
  MulF x (ValF n) -> do
    result <- compile x
    case result of
      Constant val -> return $ Constant (val * n)
      Polynomial poly -> return $ n *. Polynomial poly
  MulF x y -> do
    x' <- compile x
    y' <- compile y
    out' <- freshRefF
    let result = 1 @ F out'
    writeMulWithLC x' y' result
    return result
  ExpF x n -> do
    base <- compile x
    Exponentiation.compile base n
  DivF x y -> do
    x' <- compile x
    y' <- compile y
    out' <- freshRefF
    let result = 1 @ F out'
    writeMulWithLC y' result x'
    return result
  IfF p x y -> do
    p' <- compileExprB p
    x' <- compile x
    y' <- compile y
    Conditional.compileIfF p' x' y'
  BtoF x -> do
    result <- compileExprB x
    case result of
      Left var -> return $ 1 @ B var
      Right True -> return $ Constant 1
      Right False -> return $ Constant 0