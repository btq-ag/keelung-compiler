{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RebindableSyntax #-}

module Basic where

import AggregateSignature.Program.Keelung (aggregateSignature)
import AggregateSignature.Util
import Keelung

--------------------------------------------------------------------------------

identity :: Comp GF181 'Num
identity = Var <$> freshInput

add3 :: Comp GF181 'Num
add3 = do
  x <- freshInput
  return $ Var x + 3

eq1 :: Comp GF181 'Bool
eq1 = do
  x <- freshInput
  return $ Var x `Eq` 3

cond :: Comp GF181 'Num
cond = do
  x <- freshInput
  if Var x `Eq` 3
    then return 12
    else return 789

loop1 :: Comp GF181 'Num
loop1 = do
  arr <- freshInputs 4
  reduce 0 [0 .. 3] $ \accum i -> do
    x <- access arr i
    return $ accum + Var x

loop2 :: Comp GF181 'Bool
loop2 = do
  arr <- freshInputs 2
  arr2 <- freshInputs 2
  arrayEq 2 arr (arr2 :: (Ref ('A ('V 'Num))))

aggSig :: Comp GF181 'Bool
aggSig = do
  let settings = Settings True True True True True
  let setup = makeSetup 1 1 42 settings
  aggregateSignature setup

--------------------------------------------------------------------------------

comp :: (GaloisField n, Erase ty, Bounded n, Integral n) => Comp n ty -> Either String (ConstraintSystem n)
comp program = fmap compile (elaborate program)

run :: GaloisField b => Comp b ty -> [b] -> Either String b
run program input = elaborate program >>= (`interpret` input)