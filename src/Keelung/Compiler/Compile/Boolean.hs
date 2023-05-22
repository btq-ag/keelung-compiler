module Keelung.Compiler.Compile.Boolean where

import Control.Arrow (left)
import Control.Monad (foldM)
import Data.Field.Galois (GaloisField)
import Data.Sequence (Seq (..))
import Keelung (HasWidth (widthOf))
import Keelung.Compiler.Compile.Field
import Keelung.Compiler.Compile.Util
import Keelung.Compiler.Constraint
import Keelung.Compiler.Syntax.FieldBits qualified as FieldBits
import Keelung.Compiler.Syntax.Internal
import Keelung.Compiler.Compile.LC
import Data.Foldable (toList)

compileExprB :: (GaloisField n, Integral n) => (ExprU n -> M n (Either RefU n)) -> (ExprF n -> M n (LC n)) -> ExprB n -> M n (Either RefB Bool)
compileExprB compileU compileF expr =
  let compile = compileExprB compileU compileF
   in case expr of
        ValB val -> return $ Right val -- out = val
        VarB var -> return $ Left (RefBX var) -- out = var
        VarBO var -> return $ Left (RefBO var) -- out = var
        VarBI var -> return $ Left (RefBI var) -- out = var
        VarBP var -> return $ Left (RefBP var) -- out = var
        AndB x0 x1 xs -> do
          x0' <- compile x0
          x1' <- compile x1
          xs' <- mapM compile xs
          andBs x0' x1' xs'
        OrB x0 x1 xs -> do
          x0' <- compile x0
          x1' <- compile x1
          xs' <- mapM compile xs
          orBs x0' x1' xs'
        XorB x y -> do
          x' <- compile x
          y' <- compile y
          xorB x' y'
        NotB x -> do
          x' <- compile x
          case x' of
            Left var -> do
              out <- freshRefB
              writeNEqB var out
              return $ Left out
            Right val -> return $ Right (not val)
        IfB p x y -> do
          p' <- compile p
          x' <- compile x
          y' <- compile y
          compileIfB p' x' y'
        NEqB x y -> compile (XorB x y)
        NEqF x y -> do
          x' <- compileF x
          y' <- compileF y
          eqZero False (x' <> neg y')
        NEqU x y -> do
          x' <- compileU x
          y' <- compileU y
          eqFU False (left U x') (left U y')
        EqB x y -> do
          x' <- compile x
          y' <- compile y
          eqB x' y'
        EqF x y -> do
          x' <- compileF x
          y' <- compileF y
          eqZero True (x' <> neg y')
        EqU x y -> do
          x' <- compileU x
          y' <- compileU y
          eqFU True (left U x') (left U y')
        LTEU x y -> do
          x' <- compileU x
          y' <- compileU y
          case (x', y') of
            (Left xVar, Left yVar) -> computeLTEUVarVar xVar yVar
            (Left xVar, Right yVal) -> computeLTEUVarConst xVar yVal
            (Right xVal, Left yVar) -> computeLTEUConstVar xVal yVar
            (Right xVal, Right yVal) -> return $ Right (xVal <= yVal)
        LTU x y -> do
          x' <- compileU x
          y' <- compileU y
          case (x', y') of
            (Left xVar, Left yVar) -> computeLTUVarVar xVar yVar
            (Left xVar, Right yVal) -> computeLTUVarConst xVar yVal
            (Right xVal, Left yVar) -> computeLTUConstVar xVal yVar
            (Right xVal, Right yVal) -> return $ Right (xVal < yVal)
        GTEU x y -> compile (LTEU y x)
        GTU x y -> compile (LTU y x)
        BitU x i -> do
          let width = widthOf x
          let index = i `mod` width
          result <- compileU x
          case result of
            Left var -> return $ Left (RefUBit width var (i `mod` width)) -- out = x'[i]
            Right val -> return $ Right (FieldBits.testBit' val index)

--------------------------------------------------------------------------------

-- | Conditional
--  out = p * x + (1 - p) * y
--      =>
--  out = p * x + y - p * y
--      =>
--  (out - y) = p * (x - y)
compileIfB :: (GaloisField n, Integral n) => Either RefB Bool -> Either RefB Bool -> Either RefB Bool -> M n (Either RefB Bool)
compileIfB (Right True) x _ = return x
compileIfB (Right False) _ y = return y
compileIfB (Left _) (Right True) (Right True) = return $ Right True
compileIfB (Left p) (Right True) (Right False) = return $ Left p
compileIfB (Left p) (Right False) (Right True) = do
  out <- freshRefB
  writeNEqB p out
  return $ Left out
compileIfB (Left _) (Right False) (Right False) = return $ Right False
compileIfB (Left p) (Right x) (Left y) = do
  out <- freshRefB
  -- (out - y) = p * (x - y)
  writeMul
    (0, [(B p, 1)])
    (if x then 1 else 0, [(B y, -1)])
    (0, [(B y, -1), (B out, 1)])
  return $ Left out
compileIfB (Left p) (Left x) (Right y) = do
  out <- freshRefB
  -- (out - y) = p * (x - y)
  writeMul
    (0, [(B p, 1)])
    (if y then -1 else 0, [(B x, 1)])
    (if y then -1 else 0, [(B out, 1)])
  return $ Left out
compileIfB (Left p) (Left x) (Left y) = do
  out <- freshRefB
  -- (out - y) = p * (x - y)
  writeMul
    (0, [(B p, 1)])
    (0, [(B x, 1), (B y, -1)])
    (0, [(B y, -1), (B out, 1)])
  return $ Left out

fromB :: GaloisField n => Either RefB Bool -> LC n
fromB (Right True) = Constant 1
fromB (Right False) = Constant 0
fromB (Left x) = 1 @ B x

andBs :: (GaloisField n, Integral n) => Either RefB Bool -> Either RefB Bool -> Seq (Either RefB Bool) -> M n (Either RefB Bool)
andBs (Right False) _ _ = return $ Right False
andBs _ (Right False) _ = return $ Right False
andBs (Right True) x Empty = return x
andBs (Right True) x0 (x1 :<| xs) = andBs x0 x1 xs
andBs (Left x) (Right True) Empty = return $ Left x
andBs (Left x0) (Right True) (x1 :<| xs) = andBs (Left x0) x1 xs
andBs (Left x0) (Left x1) Empty = do
  -- 2 operands only
  -- x * y = out
  out <- freshRefB
  writeMul
    (0, [(B x0, 1)])
    (0, [(B x1, 1)])
    (0, [(B out, 1)])
  return $ Left out
andBs (Left x0) (Left x1) (x2 :<| xs) = do
  -- more than 2 operands, rewrite it as an equality instead:
  --      if all operands are 1           then 1 else 0
  --  =>  if the sum of operands is N     then 1 else 0
  --  =>  the sum of operands is N
  let arity = Constant (fromIntegral (3 + length xs))
  let polynomal = 1 @ B x0 <> 1 @ B x1 <> mconcat (fmap fromB (toList (x2 :<| xs))) <> neg arity
  eqZero True polynomal

orBs :: (GaloisField n, Integral n) => Either RefB Bool -> Either RefB Bool -> Seq (Either RefB Bool) -> M n (Either RefB Bool)
orBs (Right True) _ _ = return $ Right True
orBs _ (Right True) _ = return $ Right True
orBs (Right False) x Empty = return x
orBs (Right False) x0 (x1 :<| xs) = orBs x0 x1 xs
orBs (Left x) (Right False) Empty = return $ Left x
orBs (Left x0) (Right False) (x1 :<| xs) = orBs (Left x0) x1 xs
orBs (Left x0) (Left x1) Empty = do
  -- 2 operands only
  -- (1 - x) * y = (out - x)
  out <- freshRefB
  writeMul
    (1, [(B x0, -1)])
    (0, [(B x1, 1)])
    (0, [(B x0, -1), (B out, 1)])
  return $ Left out
orBs (Left x0) (Left x1) (x2 :<| xs) = do
  -- more than 2 operands, rewrite it as an inequality instead:
  --      if all operands are 0           then 0 else 1
  --  =>  if the sum of operands is 0     then 0 else 1
  --  =>  if the sum of operands is not 0 then 1 else 0
  --  =>  the sum of operands is not 0
  let polynomal = 1 @ B x0 <> 1 @ B x1 <> mconcat (fmap fromB (toList (x2 :<| xs)))
  eqZero False $ 1 @ B x0 <> 1 @ B x1 <> polynomal
  
  --  polynomal

xorB :: (GaloisField n, Integral n) => Either RefB Bool -> Either RefB Bool -> M n (Either RefB Bool)
xorB (Right True) (Right True) = return $ Right False
xorB (Right True) (Right False) = return $ Right True
xorB (Right False) (Right True) = return $ Right True
xorB (Right False) (Right False) = return $ Right False
xorB (Right True) (Left y) = do
  out <- freshRefB
  writeNEqB out y
  return $ Left out
xorB (Right False) (Left y) = return $ Left y
xorB (Left x) (Right y) = xorB (Right y) (Left x)
xorB (Left x) (Left y) = do
  -- (1 - 2x) * (y + 1) = (1 + out - 3x)
  out <- freshRefB
  writeMul
    (1, [(B x, -2)])
    (1, [(B y, 1)])
    (1, [(B x, -3), (B out, 1)])
  return $ Left out

eqB :: (GaloisField n, Integral n) => Either RefB Bool -> Either RefB Bool -> M n (Either RefB Bool)
eqB (Right x) (Right y) = return $ Right $ x == y
eqB (Right True) (Left y) = return $ Left y
eqB (Right False) (Left y) = do
  out <- freshRefB
  writeNEqB out y
  return $ Left out
eqB (Left x) (Right y) = eqB (Right y) (Left x)
eqB (Left x) (Left y) = do
  --     x * y + (1 - x) * (1 - y) = out
  -- =>
  --    (1 - x) * (1 - 2y) = (out - y)
  out <- freshRefB
  writeMul
    (1, [(B x, -1)])
    (1, [(B y, -2)])
    (0, [(B out, 1), (B y, -1)])
  return (Left out)

--------------------------------------------------------------------------------

-- Compiling a ≤ b, where a and b are both variables
-- lastBit = if a
--    then if b then 1 else 0
--    else if b then 1 else 1
computeLTEUVarVar :: (GaloisField n, Integral n) => RefU -> RefU -> M n (Either RefB Bool)
computeLTEUVarVar x y = do
  let width = widthOf x
  -- last bit
  let xBit = B (RefUBit width x 0)
      yBit = B (RefUBit width y 0)
  -- x[0] * y[0] = result + x[0] - 1
  result <- freshRefB
  writeMul (0, [(xBit, 1)]) (0, [(yBit, 1)]) (-1, [(B result, 1), (xBit, 1)])
  -- starting from the least significant bit
  Left <$> foldM (compileLTEUVarVarPrim width x y) result [1 .. width - 1]

computeLTEUVarConst :: (GaloisField n, Integral n) => RefU -> n -> M n (Either RefB Bool)
computeLTEUVarConst x y = do
  let width = widthOf x
  -- starting from the least significant bit
  let pairs = [(RefUBit width x i, FieldBits.testBit' y i) | i <- [0 .. width - 1]]
  foldM compileLTEUVarConstPrim (Right True) pairs

computeLTEUConstVar :: (GaloisField n, Integral n) => n -> RefU -> M n (Either RefB Bool)
computeLTEUConstVar x y = do
  let width = widthOf y
  -- starting from the least significant bit
  let pairs = [(FieldBits.testBit' x i, RefUBit width y i) | i <- [0 .. width - 1]]
  foldM compileLTEUConstVarPrim (Right True) pairs

-- Compiling a < b, where a and b are both variables
-- lastBit = if a
--    then if b then 0 else 0
--    else if b then 1 else 0
-- (b - lastBit) = (a)(b)
computeLTUVarVar :: (GaloisField n, Integral n) => RefU -> RefU -> M n (Either RefB Bool)
computeLTUVarVar x y = do
  let width = widthOf x
  -- last bit
  let xBit = B (RefUBit width x 0)
      yBit = B (RefUBit width y 0)
  -- (y - lastBit) = (x)(y)
  lastBit <- freshRefB
  writeMul (0, [(xBit, 1)]) (0, [(yBit, 1)]) (0, [(B lastBit, -1), (yBit, 1)])
  -- starting from the least significant bit
  Left <$> foldM (compileLTEUVarVarPrim width x y) lastBit [1 .. width - 1]

-- output = if a
--    then if b then x else 0
--    else if b then 1 else x
-- output = 2abx + b + x - bx - ab - ax
--  =>
--  1. z = bx
--  2. output - z = (1-a)(b + x - 2z)
compileLTEUVarVarPrim :: (GaloisField n, Integral n) => Width -> RefU -> RefU -> RefB -> Int -> M n RefB
compileLTEUVarVarPrim width x y acc i = do
  let xBit = B (RefUBit width x i)
      yBit = B (RefUBit width y i)

  -- yacc = y[i] * acc
  yacc <- freshRefB
  writeMul (0, [(yBit, 1)]) (0, [(B acc, 1)]) (0, [(B yacc, 1)])

  -- result - yacc = (1 - x[i]) * (y[i] + acc - 2 * yacc)
  result <- freshRefB
  writeMul (1, [(xBit, -1)]) (0, [(yBit, 1), (B acc, 1), (B yacc, -2)]) (0, [(B result, 1), (B yacc, -1)])

  return result

computeLTUVarConst :: (GaloisField n, Integral n) => RefU -> n -> M n (Either RefB Bool)
computeLTUVarConst x y = do
  let width = widthOf x
  -- starting from the least significant bit
  let pairs = [(RefUBit width x i, FieldBits.testBit' y i) | i <- [0 .. width - 1]]
  foldM compileLTEUVarConstPrim (Right False) pairs

computeLTUConstVar :: (GaloisField n, Integral n) => n -> RefU -> M n (Either RefB Bool)
computeLTUConstVar x y = do
  let width = widthOf y
  -- starting from the least significant bit
  let pairs = [(FieldBits.testBit' x i, RefUBit width y i) | i <- [0 .. width - 1]]
  foldM compileLTEUConstVarPrim (Right False) pairs

compileLTEUVarConstPrim :: (GaloisField n, Integral n) => Either RefB Bool -> (RefB, Bool) -> M n (Either RefB Bool)
compileLTEUVarConstPrim (Left acc) (x, True) = do
  -- result - acc = (1 - x[i]) * (1 - acc)
  result <- freshRefB
  writeMul (1, [(B x, -1)]) (1, [(B acc, -1)]) (0, [(B result, 1), (B acc, -1)])
  return $ Left result
compileLTEUVarConstPrim (Left acc) (x, False) = do
  -- result = (1 - x[i]) * acc
  result <- freshRefB
  writeMul (1, [(B x, -1)]) (0, [(B acc, 1)]) (0, [(B result, 1)])
  return $ Left result
compileLTEUVarConstPrim (Right True) (_, True) = return $ Right True
compileLTEUVarConstPrim (Right True) (x, False) = do
  result <- freshRefB
  writeNEqB result x
  return $ Left result
compileLTEUVarConstPrim (Right False) (x, True) = do
  result <- freshRefB
  writeNEqB result x
  return $ Left result
compileLTEUVarConstPrim (Right False) (_, False) = return $ Right False

compileLTEUConstVarPrim :: (GaloisField n, Integral n) => Either RefB Bool -> (Bool, RefB) -> M n (Either RefB Bool)
compileLTEUConstVarPrim (Left acc) (True, y) = do
  -- y[i] * acc = result
  result <- freshRefB
  writeMul (0, [(B y, 1)]) (0, [(B acc, 1)]) (0, [(B result, 1)])
  return $ Left result
compileLTEUConstVarPrim (Left acc) (_, y) = do
  -- - y[i] * acc = result - y[i] - acc
  result <- freshRefB
  writeMul (0, [(B y, -1)]) (0, [(B acc, 1)]) (0, [(B result, 1), (B y, -1), (B acc, -1)])
  return $ Left result
compileLTEUConstVarPrim (Right True) (True, y) = return $ Left y
compileLTEUConstVarPrim (Right True) (False, _) = return $ Right True
compileLTEUConstVarPrim (Right False) (True, _) = return $ Right False
compileLTEUConstVarPrim (Right False) (False, y) = return $ Left y

--------------------------------------------------------------------------------
