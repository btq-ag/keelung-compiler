module Keelung.Compiler.Compile.Boolean (compile, andBs, xorBs) where

import Control.Monad.State
import Data.Bits qualified
import Data.Either qualified as Either
import Data.Field.Galois (GaloisField)
import Data.Foldable (toList)
import Data.List.NonEmpty (NonEmpty)
import Data.List.NonEmpty qualified as NonEmpty
import Data.List.Split qualified as List
import Data.Maybe qualified
import Data.Sequence qualified as Seq
import Keelung (FieldType (..), HasWidth (widthOf))
import Keelung.Compiler.Compile.Monad
import Keelung.Compiler.Compile.Util
import Keelung.Compiler.ConstraintModule (ConstraintModule (..))
import Keelung.Compiler.Syntax.Internal
import Keelung.Data.FieldInfo qualified as FieldInfo
import Keelung.Data.LC
import Keelung.Data.LC qualified as LC
import Keelung.Data.Limb qualified as Limb
import Keelung.Data.Reference
import Keelung.Data.U (U)

compile :: (GaloisField n, Integral n) => (ExprU n -> M n (Either RefU U)) -> ExprB n -> M n (Either RefB Bool)
compile compileU expr = case expr of
  ValB val -> return $ Right val -- out = val
  VarB var -> return $ Left (RefBX var) -- out = var
  VarBO var -> return $ Left (RefBO var) -- out = var
  VarBI var -> return $ Left (RefBI var) -- out = var
  VarBP var -> return $ Left (RefBP var) -- out = var
  AndB xs -> do
    xs' <- mapM compileExprB xs
    andBs (toList xs')
  OrB xs -> do
    xs' <- mapM compileExprB xs
    orBs (toList xs')
  XorB xs -> do
    xs' <- mapM compileExprB xs
    xorBs (toList xs')
  NotB x -> do
    x' <- compileExprB x
    case x' of
      Left var -> do
        out <- freshRefB
        writeRefBNEq var out
        return $ Left out
      Right val -> return $ Right (not val)
  IfB p x y -> do
    p' <- compileExprB p
    x' <- compileExprB x
    y' <- compileExprB y
    compileIfB p' x' y'
  NEqB x y -> compileExprB (XorB (Seq.fromList [x, y]))
  NEqF x y -> do
    x' <- compileExprF x
    y' <- compileExprF y
    eqZero False (x' <> neg y')
  EqB x y -> do
    x' <- compileExprB x
    y' <- compileExprB y
    eqB x' y'
  EqF x y -> do
    x' <- compileExprF x
    y' <- compileExprF y
    eqZero True (x' <> neg y')
  EqU x y -> do
    x' <- compileU x
    y' <- compileU y
    compileEqU x' y'
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
  GTEU x y -> compileExprB (LTEU y x)
  GTU x y -> compileExprB (LTU y x)
  BitU x i -> do
    let width = widthOf x
    let index = i `mod` width
    result <- compileU x
    case result of
      Left var -> return $ Left (RefUBit width var (i `mod` width)) -- out = x'[i]
      Right val -> return $ Right (Data.Bits.testBit val index)

--------------------------------------------------------------------------------

compileEqU :: (GaloisField n, Integral n) => Either RefU U -> Either RefU U -> M n (Either RefB Bool)
compileEqU x y = do
  fieldWidth <- gets (FieldInfo.fieldWidth . cmField)
  result <-
    zipWithM
      (\a b -> eqZero True (a <> neg b)) -- a - b ==? 0
      (fromRefU fieldWidth x)
      (fromRefU fieldWidth y)
  case result of
    [] -> return $ Right True
    [result'] -> return result'
    (x0 : x1 : xs) -> do
      andBs (x0 : x1 : xs)

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
  writeRefBNEq p out
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

-- | O(lg n) OR
--
--    There are two ways of calculating consecutive ORs on prime fields:
--      * O(n)    linear fold       : a + b - ab
--      * O(lg n) divide and conquer: if the sum of operands is not 0
--
--    Cost of these two approaches:
--      arity     linear fold       divide and conquer
--      2         1             <   2
--      3         2             =   2
--      4         3             >   2
orBs :: (GaloisField n, Integral n) => [Either RefB Bool] -> M n (Either RefB Bool)
orBs xs = do
  -- separate the operands into variables and constants
  let (vars, constants) = Either.partitionEithers xs
  let constant = or constants

  if constant
    then return $ Right True -- short circuit
    else do
      -- the divide and conquer approach only works on Prime fields >= 3
      fieldType <- gets (FieldInfo.fieldTypeData . cmField)
      case fieldType of
        Binary _ -> linearFold vars
        Prime 2 -> linearFold vars
        Prime _ -> divideAndConquer vars
  where
    linearFold :: (GaloisField n, Integral n) => [RefB] -> M n (Either RefB Bool)
    linearFold =
      foldM
        ( \acc var -> case acc of
            Right True -> return $ Right True
            Right False -> return $ Left var
            Left accVar -> Left <$> orB accVar var
        )
        (Right False)

    --  rewrite as an inequality instead:
    --       if all operands are 0           then 0 else 1
    --   =>  if the sum of operands is 0     then 0 else 1
    --   =>  if the sum of operands is not 0 then 1 else 0
    --   =>  the sum of operands is not 0
    divideAndConquer :: (GaloisField n, Integral n) => [RefB] -> M n (Either RefB Bool)
    divideAndConquer [] = return $ Right False
    divideAndConquer [var] = return $ Left var
    divideAndConquer [var1, var2] = Left <$> orB var1 var2
    divideAndConquer (var : vars) = do
      -- split operands into pieces in case that the order of field is too small
      -- each pieces has at most (order - 1) operands
      order <- gets (FieldInfo.fieldOrder . cmField)

      let pieces = List.chunksOf (fromInteger order - 1) (var : vars)
      let seqToLC piece = mconcat (fmap (\x -> 1 @ B x) (toList piece))
      mapM (eqZero False . seqToLC) pieces >>= orBs

    -- 2 operands only, works on both Prime and Binary fields
    -- (1 - x) * y = (out - x)
    orB :: (GaloisField n, Integral n) => RefB -> RefB -> M n RefB
    orB var1 var2 = do
      out <- freshRefB
      writeMul
        (1, [(B var1, -1)])
        (0, [(B var2, 1)])
        (0, [(B var1, -1), (B out, 1)])
      return out

-- | O(lg n) AND
--
--    There are two ways of calculating consecutive ANDs on prime fields:
--      * O(n)    linear fold       : a * b
--      * O(lg n) divide and conquer: if the sum of N operands is N
--
--    Cost of these two approaches:
--      arity     linear fold       divide and conquer
--      2         1             <   2
--      3         2             =   2
--      4         3             >   2
andBs :: (GaloisField n, Integral n) => [Either RefB Bool] -> M n (Either RefB Bool)
andBs xs = do
  -- separate the operands into variables and constants
  let (vars, constants) = Either.partitionEithers xs
  let constant = and constants

  if constant
    then do
      -- the divide and conquer approach only works on Prime fields >= 3
      fieldType <- gets (FieldInfo.fieldTypeData . cmField)
      case fieldType of
        Binary _ -> linearFold vars
        Prime 2 -> linearFold vars
        Prime _ -> divideAndConquer vars
    else return $ Right False -- short circuit
  where
    linearFold :: (GaloisField n, Integral n) => [RefB] -> M n (Either RefB Bool)
    linearFold =
      foldM
        ( \acc var -> case acc of
            Right True -> return $ Left var
            Right False -> return $ Right False
            Left accVar -> Left <$> andB accVar var
        )
        (Right True)

    --  rewrite as an inequality instead:
    --       if all operands are 1           then 1 else 0
    --   =>  if the sum of operands is N     then 1 else 0
    --   =>  the sum of operands is N
    divideAndConquer :: (GaloisField n, Integral n) => [RefB] -> M n (Either RefB Bool)
    divideAndConquer [] = return $ Right True
    divideAndConquer [var] = return $ Left var
    divideAndConquer [var1, var2] = Left <$> andB var1 var2
    divideAndConquer (var : vars) = do
      -- split operands into pieces in case that the order of field is too small
      -- each pieces has at most (order - 1) operands
      order <- gets (FieldInfo.fieldOrder . cmField)

      let pieces = List.chunksOf (fromInteger order - 1) (var : vars)
      let seqToLC piece = mconcat (fmap (\x -> 1 @ B x) (toList piece)) <> neg (Constant (fromIntegral (length piece)))
      mapM (eqZero True . seqToLC) pieces >>= andBs

    -- 2 operands only, works on both Prime and Binary fields
    -- x * y = out
    andB :: (GaloisField n, Integral n) => RefB -> RefB -> M n RefB
    andB var1 var2 = do
      out <- freshRefB
      writeMul
        (0, [(B var1, 1)])
        (0, [(B var2, 1)])
        (0, [(B out, 1)])
      return out

-- | XOR, O(lg n) on prime fields and O(1) on binary fields
--
--    There are two ways of calculating consecutive XORs on Prime fields:
--      * O(n)    linear fold       : a + b - 2ab
--      * O(lg n) divide and conquer: if the sum of operands is odd then 1 else 0
--
--      Cost of these two approaches:
--        arity     linear fold       divide and conquer
--        2         1             <   2
--        3         2             =   2
--        4         3             =   3
--        5         4             >   3
--
--    One way of calculating consecutive XORs on Binary fields:
--      * O(1)    linear fold       : a + b + ... + z
xorBs :: (GaloisField n, Integral n) => [Either RefB Bool] -> M n (Either RefB Bool)
xorBs xs = do
  -- separate the operands into variables and constants
  let (vars, constants) = Either.partitionEithers xs
  let constant = odd (length (filter id constants)) -- if number of True is odd
  resultFromVars <- do
    fieldType <- gets (FieldInfo.fieldTypeData . cmField)
    case fieldType of
      Binary _ -> constantFold vars
      Prime 2 -> linearFold vars
      Prime _ -> divideAndConquer vars

  if constant
    then flipResult resultFromVars
    else return resultFromVars
  where
    -- special case for binary fields, simply sum up all operands
    constantFold :: (GaloisField n, Integral n) => [RefB] -> M n (Either RefB Bool)
    constantFold [] = return $ Right False
    constantFold [x] = return $ Left x
    constantFold vars = do
      out <- freshRefB
      -- compose the LC for the sum
      let sumOfVars = mconcat (fmap (\x -> 1 @ B x) vars)
      writeAddWithLC $ sumOfVars <> neg (1 @ B out)
      return $ Left out

    -- for Prime 2 fields, we can't use the divide and conquer approach
    linearFold :: (GaloisField n, Integral n) => [RefB] -> M n (Either RefB Bool)
    linearFold =
      foldM
        ( \acc var -> case acc of
            Right True -> flipResult (Left var)
            Right False -> return $ Left var
            Left accVar -> Left <$> xorB accVar var
        )
        (Right False)

    -- rewrite as even/odd relationship instead:
    --      if the sum of all operands is even then 0 else 1
    divideAndConquer :: (GaloisField n, Integral n) => [RefB] -> M n (Either RefB Bool)
    divideAndConquer vars = do
      -- split operands into chunks in case that the order of field is too small
      -- each chunk can only has at most `(2 ^ fieldWidth) - 1` operands
      fieldWidth <- gets (FieldInfo.fieldWidth . cmField)
      let lists =
            -- trying to avoid having to compute `2 ^ fieldWidth - 1` most of the time
            let len = length vars
             in if length vars <= fieldWidth || len < 256 && fieldWidth >= 8
                  then [vars]
                  else List.chunksOf (fromInteger (2 ^ fieldWidth - 1)) vars
      let nonEmptyChunks = Data.Maybe.mapMaybe NonEmpty.nonEmpty lists
      case nonEmptyChunks of
        [] -> return $ Right False
        [var NonEmpty.:| []] -> return $ Left var
        _ -> mapM compileChunk nonEmptyChunks >>= divideAndConquer

    compileChunk :: (GaloisField n, Integral n) => NonEmpty RefB -> M n RefB
    compileChunk (var1 NonEmpty.:| []) = return var1
    compileChunk (var1 NonEmpty.:| [var2]) = xorB var1 var2
    compileChunk (var1 NonEmpty.:| [var2, var3]) = xorB var1 var2 >>= xorB var3
    compileChunk (var1 NonEmpty.:| [var2, var3, var4]) = xorB var1 var2 >>= xorB var3 >>= xorB var4
    compileChunk (var NonEmpty.:| vars') = do
      let vars = var : vars'
      -- devise an unsigned integer for expressing the sum of vars
      let width = widthOfInteger (toInteger (length vars))
      refU <- freshRefU width
      let limb = Limb.new refU width 0 (Left True)
      -- compose the LC for the sum
      let sumOfVars = mconcat (fmap (\x -> 1 @ B x) vars)
      -- equate the LC with the unsigned integer
      writeAddWithLCAndLimbs sumOfVars 0 [(limb, -1)]
      -- check if the sum is even or odd by checking the least significant bit of the unsigned integer
      return $ RefUBit width refU 0

    flipResult :: (GaloisField n, Integral n) => Either RefB Bool -> M n (Either RefB Bool)
    flipResult (Right False) = return $ Right True
    flipResult (Right True) = return $ Right False
    flipResult (Left var) = do
      out <- freshRefB
      writeRefBNEq var out
      return $ Left out

    xorB :: (GaloisField n, Integral n) => RefB -> RefB -> M n RefB
    xorB x y = do
      -- 2 x * y = x + y - out
      out <- freshRefB
      writeMul
        (0, [(B x, 2)])
        (0, [(B y, 1)])
        (0, [(B x, 1), (B y, 1), (B out, -1)])
      return out

-- | Basically specialized version of `xorBs`
eqB :: (GaloisField n, Integral n) => Either RefB Bool -> Either RefB Bool -> M n (Either RefB Bool)
eqB (Right x) (Right y) = return $ Right $ x == y
eqB (Right True) (Left y) = return $ Left y
eqB (Right False) (Left y) = do
  out <- freshRefB
  writeRefBNEq out y
  return $ Left out
eqB (Left x) (Right y) = eqB (Right y) (Left x)
eqB (Left x) (Left y) = do
  fieldType <- gets (FieldInfo.fieldTypeData . cmField)
  case fieldType of
    Binary _ -> binary
    Prime 2 -> binary
    Prime _ -> prime
  where
    binary :: (GaloisField n, Integral n) => M n (Either RefB Bool)
    binary = do
      --  1 + x + y = out
      out <- freshRefB
      writeAdd 1 [(B x, 1), (B y, 1), (B out, -1)]
      return (Left out)

    prime :: (GaloisField n, Integral n) => M n (Either RefB Bool)
    prime = do
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

computeLTEUVarConst :: (GaloisField n, Integral n) => RefU -> U -> M n (Either RefB Bool)
computeLTEUVarConst x y = do
  let width = widthOf x
  case toInteger y of
    0 -> do
      -- see if x is 0
      fieldInfo <- gets cmField
      let chunks = LC.fromRefU2 fieldInfo (Left x)
      mapM (eqZero True) chunks >>= andBs
    _ -> do
      -- starting from the least significant bit
      let pairs = [(RefUBit width x i, Data.Bits.testBit y i) | i <- [0 .. width - 1]]
      foldM compileLTEUVarConstPrim (Right True) pairs

computeLTEUConstVar :: (GaloisField n, Integral n) => U -> RefU -> M n (Either RefB Bool)
computeLTEUConstVar x y = do
  let width = widthOf y
  -- starting from the least significant bit
  let pairs = [(Data.Bits.testBit x i, RefUBit width y i) | i <- [0 .. width - 1]]
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
-- on prime fields:
--    output = 2abx + b + x - bx - ab - ax
--      =>
--        1. z = bx
--        2. output - z = (1-a)(b + x - 2z)
-- on binary fields:
--    output = b + x + bx + ab + ax
--      =>
--        1. z = bx
--        2. output + b + x + z = (a)(b + x)
compileLTEUVarVarPrim :: (GaloisField n, Integral n) => Width -> RefU -> RefU -> RefB -> Int -> M n RefB
compileLTEUVarVarPrim width x y acc i = do
  let xBit = B (RefUBit width x i)
      yBit = B (RefUBit width y i)

  -- yacc = y[i] * acc
  yacc <- freshRefB
  writeMul (0, [(yBit, 1)]) (0, [(B acc, 1)]) (0, [(B yacc, 1)])

  characteristic <- gets (FieldInfo.fieldChar . cmField)
  if characteristic == 2
    then do
      -- result + yacc + y[i] + acc = (x[i]) * (y[i] + acc)
      result <- freshRefB
      writeMul (0, [(xBit, 1)]) (0, [(yBit, 1), (B acc, 1)]) (0, [(B result, 1), (B yacc, 1), (yBit, 1), (B acc, 1)])
      return result
    else do
      -- result - yacc = (1 - x[i]) * (y[i] + acc - 2 * yacc)
      result <- freshRefB
      writeMul (1, [(xBit, -1)]) (0, [(yBit, 1), (B acc, 1), (B yacc, -2)]) (0, [(B result, 1), (B yacc, -1)])
      return result

computeLTUVarConst :: (GaloisField n, Integral n) => RefU -> U -> M n (Either RefB Bool)
computeLTUVarConst x y = do
  let width = widthOf x
  -- starting from the least significant bit
  let pairs = [(RefUBit width x i, Data.Bits.testBit y i) | i <- [0 .. width - 1]]
  foldM compileLTEUVarConstPrim (Right False) pairs

computeLTUConstVar :: (GaloisField n, Integral n) => U -> RefU -> M n (Either RefB Bool)
computeLTUConstVar x y = do
  let width = widthOf y
  -- starting from the least significant bit
  let pairs = [(Data.Bits.testBit x i, RefUBit width y i) | i <- [0 .. width - 1]]
  foldM compileLTEUConstVarPrim (Right False) pairs

compileLTEUVarConstPrim :: (GaloisField n, Integral n) => Either RefB Bool -> (RefB, Bool) -> M n (Either RefB Bool)
compileLTEUVarConstPrim (Left acc) (x, True) = do
  -- acc' - acc = (1 - x[i]) * (1 - acc)
  acc' <- freshRefB
  writeMul (1, [(B x, -1)]) (1, [(B acc, -1)]) (0, [(B acc', 1), (B acc, -1)])
  return $ Left acc'
compileLTEUVarConstPrim (Left acc) (x, False) = do
  -- acc' = (1 - x[i]) * acc
  acc' <- freshRefB
  writeMul (1, [(B x, -1)]) (0, [(B acc, 1)]) (0, [(B acc', 1)])
  return $ Left acc'
compileLTEUVarConstPrim (Right True) (_, True) = return $ Right True
compileLTEUVarConstPrim (Right True) (x, False) = do
  acc <- freshRefB
  writeRefBNEq acc x
  return $ Left acc
compileLTEUVarConstPrim (Right False) (x, True) = do
  acc <- freshRefB
  writeRefBNEq acc x
  return $ Left acc
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
