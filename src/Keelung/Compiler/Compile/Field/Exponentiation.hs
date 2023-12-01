module Keelung.Compiler.Compile.Field.Exponentiation (compile) where

import Data.Field.Galois
import Keelung.Compiler.Compile.Monad
import Keelung.Data.LC
import Keelung.Data.PolyL qualified as PolyL
import Keelung.Data.Reference

compile :: (GaloisField n, Integral n) => LC n -> Integer -> M n (LC n)
compile = fastExp 1

-- compile :: (GaloisField n, Integral n) => LC n -> Integer -> M n (LC n)
-- compile base power = do
--   ord <- gets (FieldInfo.fieldOrder . cmField)
--   compile_ base ord power

-- compile_ :: (GaloisField n, Integral n) => LC n -> Integer -> Integer -> M n (LC n)
-- compile_ base ord power
--   | power == 0 = return $ Constant 1
--   | power == 1 = return base
--   | power < ord - 1 = fastExp 1 base power -- most common case
--   | power == ord - 1 = return $ Constant 1
--   | power == ord = return base
--   | power < (ord * ord) - 1 = fastExp 1 base power -- second most common case
--   | power == (ord * ord) - 1 = return $ Constant 1
--   | power == (ord * ord) = return base
--   | otherwise = fastExp 1 base power -- no optimization after this point
--   where 
--     -- if base == 0 && power > 0
--     --    then 0
--     --    else OTHERWISE
--     whenBaseIsZero other = do 
--       notZero <- eqZero False base
--       case notZero of
--         Left _ -> return $ Constant 1
--         Right False -> return $ Constant 1 -- 0 ^ 0 = 1
--         Right True -> return $ Constant 1

-- | Fast exponentiation on field
fastExp :: (GaloisField n, Integral n) => n -> LC n -> Integer -> M n (LC n)
fastExp acc _ 0 = return $ Constant acc
fastExp acc (Constant base) e = return $ Constant $ (base ^ e) * acc
fastExp acc (Polynomial base) e =
  let (q, r) = e `divMod` 2
   in if r == 1
        then do
          result <- fastExp acc (Polynomial base) (e - 1)
          mul result (Polynomial base)
        else do
          result <- fastExp acc (Polynomial base) q
          mul result result
  where
    -- \| Compute the multiplication of two variables
    mul :: (GaloisField n, Integral n) => LC n -> LC n -> M n (LC n)
    mul (Constant x) (Constant y) = return $ Constant (x * y)
    mul (Constant x) (Polynomial ys) = return $ fromPolyL $ PolyL.multiplyBy x ys
    mul (Polynomial xs) (Constant y) = return $ fromPolyL $ PolyL.multiplyBy y xs
    mul (Polynomial xs) (Polynomial ys) = do
      out <- freshRefF
      let result = 1 @ F out
      writeMulWithLC (Polynomial xs) (Polynomial ys) result
      return result
