{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RebindableSyntax #-}

module Basic where

import AggregateSignature.Program.Keelung (aggregateSignature)
import AggregateSignature.Util
import Keelung

--------------------------------------------------------------------------------

identity :: Comp 'Num GF181
identity = Var <$> freshInput

identityB :: Comp 'Bool GF181
identityB = Var <$> freshInput

add3 :: Comp 'Num GF181
add3 = do
  x <- freshInput
  return $ Var x + 3

eq1 :: Comp 'Bool GF181
eq1 = do
  x <- freshInput
  return $ Var x `Eq` 3

cond :: Comp 'Num GF181
cond = do
  x <- freshInput
  if Var x `Eq` 3
    then return 12
    else return 789

loop1 :: Comp 'Num GF181
loop1 = do
  arr <- freshInputs 4
  reduce 0 [0 .. 3] $ \accum i -> do
    x <- access arr i
    return $ accum + Var x

loop2 :: Comp 'Bool GF181
loop2 = do
  arr <- freshInputs 2
  arr2 <- freshInputs 2
  arrayEq 2 arr (arr2 :: (Ref ('A ('V 'Num))))

aggSig :: Int -> Int -> Comp 'Bool GF181
aggSig dim num = do
  let settings = Settings True True True True True
  let setup = makeSetup dim num 42 settings
  aggregateSignature setup

--------------------------------------------------------------------------------

comp :: (GaloisField n, Erase ty, Bounded n, Integral n) => Comp ty n -> Either String (ConstraintSystem n)
comp program = fmap (compile . eraseType) (elaborate program)

optm :: (GaloisField n, Erase ty, Bounded n, Integral n) => Comp ty n -> Either String (ConstraintSystem n)
optm program = optimise <$> comp program

-- run :: GaloisField n => Comp ty n -> [n] -> Either String n
-- run program input = elaborate program >>= (`interpret` input)

exec :: GaloisField n => Comp ty n -> [n] -> Either String n
exec program input = elaborate program >>= (`interpret` input)