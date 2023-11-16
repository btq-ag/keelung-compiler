module Keelung.Compiler.Compile.Field (compile) where

import Data.Field.Galois (GaloisField)
import Data.Foldable (Foldable (toList))
import Data.Sequence (Seq (..))
import Keelung.Compiler.Compile.Field.Exponentiation qualified as Exponentiation
import Keelung.Compiler.Compile.Monad
import Keelung.Compiler.Syntax.Internal
import Keelung.Data.LC
import Keelung.Data.Reference
import qualified Keelung.Compiler.Compile.Field.Conditional as Conditional

----------------------------------------------------------------

compile :: (GaloisField n, Integral n) => ExprF n -> M n (LC n)
compile expr = case expr of
  ValF val -> return $ Constant val
  VarF var -> return $ 1 @ F (RefFX var)
  VarFO var -> return $ 1 @ F (RefFO var)
  VarFI var -> return $ 1 @ F (RefFI var)
  VarFP var -> return $ 1 @ F (RefFP var)
  SubF x y -> do
    x' <- toLC x
    y' <- toLC y
    return $ x' <> neg y'
  AddF x y rest -> do
    operands <- mapM toLC (toList (x :<| y :<| rest))
    return $ mconcat operands
  MulF x y -> do
    x' <- toLC x
    y' <- toLC y
    out' <- freshRefF
    let result = 1 @ F out'
    writeMulWithLC x' y' result
    return result
  ExpF x n -> do
    base <- toLC x
    Exponentiation.compile base n
  DivF x y -> do
    x' <- toLC x
    y' <- toLC y
    out' <- freshRefF
    let result = 1 @ F out'
    writeMulWithLC y' result x'
    return result
  IfF p x y -> do
    p' <- compileExprB p
    x' <- toLC x
    y' <- toLC y
    Conditional.compileIfF p' x' y'
  BtoF x -> do
    result <- compileExprB x
    case result of
      Left var -> return $ 1 @ B var
      Right True -> return $ Constant 1
      Right False -> return $ Constant 0

toLC :: (GaloisField n, Integral n) => ExprF n -> M n (LC n)
toLC (MulF (ValF m) (ValF n)) = return $ Constant (m * n)
toLC (MulF (VarF var) (ValF n)) = return $ n @ F (RefFX var)
toLC (MulF (VarFI var) (ValF n)) = return $ n @ F (RefFI var)
toLC (MulF (VarFO var) (ValF n)) = return $ n @ F (RefFX var)
toLC (MulF (ValF n) (VarF var)) = return $ n @ F (RefFX var)
toLC (MulF (ValF n) (VarFI var)) = return $ n @ F (RefFI var)
toLC (MulF (ValF n) (VarFO var)) = return $ n @ F (RefFO var)
toLC (MulF (ValF n) expr) = do
  result <- compileExprF expr
  case result of
    Constant val -> return $ Constant (val * n)
    Polynomial poly -> return $ scale n (Polynomial poly)
toLC (MulF expr (ValF n)) = do
  result <- compileExprF expr
  case result of
    Constant val -> return $ Constant (val * n)
    Polynomial poly -> return $ scale n (Polynomial poly)
toLC (ValF n) = return $ Constant n
toLC (VarF var) = return $ 1 @ F (RefFX var)
toLC (VarFI var) = return $ 1 @ F (RefFI var)
toLC (VarFO var) = return $ 1 @ F (RefFO var)
toLC expr = compileExprF expr