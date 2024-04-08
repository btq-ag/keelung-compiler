module Keelung.Compiler.Compile.Field.Conditional (compileIfF) where
import Keelung.Data.LC ( LC(..), (@), neg )
import Data.Field.Galois
import Keelung.Data.Reference
import Keelung.Compiler.Compile.Monad

-- | Conditional
--  out = p * x + (1 - p) * y
--      =>
--  out = p * x + y - p * y
--      =>
--  (out - y) = p * (x - y)
compileIfF :: (GaloisField n, Integral n) => Either RefB Bool -> LC n -> LC n -> M n (LC n)
compileIfF (Right True) x _ = return x
compileIfF (Right False) _ y = return y
compileIfF (Left p) (Constant x) (Constant y) = do
  if x == y
    then return $ Constant x
    else do
      out <- freshRefF
      -- (x - y) * p - out + y = 0
      let result = 1 @ F out
      writeAddWithLC $ (x - y) @ B p <> result <> Constant y
      return result
compileIfF (Left p) (Constant x) (Polynomial y) = do
  out <- freshRefF
  -- p * (x - y) = (out - y)
  let result = 1 @ F out
  writeMulWithLC
    (1 @ B p) -- p
    (Constant x <> neg (Polynomial y)) -- (x - y)
    (result <> neg (Polynomial y)) -- (out - y)
  return result
compileIfF (Left p) (Polynomial x) (Constant y) = do
  out <- freshRefF
  -- p * (x - y) = (out - y)
  let result = 1 @ F out
  writeMulWithLC
    (1 @ B p) -- p
    (Polynomial x <> neg (Constant y)) -- (x - y)
    (result <> neg (Constant y)) -- (out - y)
  return result
compileIfF (Left p) (Polynomial x) (Polynomial y) = do
  out <- freshRefF
  -- p * (x - y) = out - y
  let result = 1 @ F out
  writeMulWithLC
    (1 @ B p) -- p
    (Polynomial x <> neg (Polynomial y)) -- (x - y)
    (result <> neg (Polynomial y)) -- (out - y)
  return result
