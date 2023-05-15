module Keelung.Compiler.Compile.Field where

import Data.Field.Galois (GaloisField)
import Keelung.Compiler.Compile.Util
import Keelung.Compiler.Constraint

-- | Equalities are compiled with inequalities and inequalities with CNEQ constraints.
--    introduce a new variable m
--    if diff = 0 then m = 0 else m = recip diff
--    Equality:
--      (x - y) * m = 1 - out
--      (x - y) * out = 0
--    Inequality:
--      (x - y) * m = out
--      (x - y) * (1 - out) = 0
eqFU :: (GaloisField n, Integral n) => Bool -> Either Ref n -> Either Ref n -> M n (Either RefB Bool)
eqFU isEq (Right x) (Right y) = return $ Right $ if isEq then x == y else x /= y
eqFU isEq (Right x) (Left y) = do
  m <- freshRefF
  out <- freshRefB
  if isEq
    then do
      --  1. (x - y) * m = 1 - out
      --  2. (x - y) * out = 0
      writeMul
        (x, [(y, -1)])
        (0, [(F m, 1)])
        (1, [(B out, -1)])
      writeMul
        (x, [(y, -1)])
        (0, [(B out, 1)])
        (0, [])
    else do
      --  1. (x - y) * m = out
      --  2. (x - y) * (1 - out) = 0
      writeMul
        (x, [(y, -1)])
        (0, [(F m, 1)])
        (0, [(B out, 1)])
      writeMul
        (x, [(y, -1)])
        (1, [(B out, -1)])
        (0, [])
  --  keep track of the relation between (x - y) and m
  addEqZeroHint x [(y, -1)] m
  return (Left out)
eqFU isEq (Left x) (Right y) = eqFU isEq (Right y) (Left x)
eqFU isEq (Left x) (Left y) = do
  m <- freshRefF
  out <- freshRefB
  if isEq
    then do
      --  1. (x - y) * m = 1 - out
      --  2. (x - y) * out = 0
      writeMul
        (0, [(x, 1), (y, -1)])
        (0, [(F m, 1)])
        (1, [(B out, -1)])
      writeMul
        (0, [(x, 1), (y, -1)])
        (0, [(B out, 1)])
        (0, [])
    else do
      --  1. (x - y) * m = out
      --  2. (x - y) * (1 - out) = 0
      writeMul
        (0, [(x, 1), (y, -1)])
        (0, [(F m, 1)])
        (0, [(B out, 1)])
      writeMul
        (0, [(x, 1), (y, -1)])
        (1, [(B out, -1)])
        (0, [])
  --  keep track of the relation between (x - y) and m
  addEqZeroHint 0 [(x, 1), (y, -1)] m
  return (Left out)
