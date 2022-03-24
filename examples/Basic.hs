{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RebindableSyntax #-}

module Basic where

import AggregateSignature.Program.Keelung (aggregateSignature, computeAggregateSignature)
import AggregateSignature.Util
import Keelung
import qualified Keelung.Optimiser.ConstantPropagation as ConstantPropagation

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
  let settings = Settings True False False False False
  -- let settings = Settings True True True True True
  let setup = makeSetup dim num 42 settings


  aggregateSignature setup

q1 :: Comp 'Bool GF181
q1 = aggSig 1 1

q2 :: Comp 'Bool GF181
q2 = aggSig 1 10

checkSig :: Comp 'Bool GF181 
checkSig = do
  let settings = Settings True False False False False
  let Setup dimension _ publicKey signatures _ _ = makeSetup 1 10 42 settings
  expectedAggSig <- freshInputs dimension
  actualAggSig <- computeAggregateSignature publicKey signatures
  arrayEq dimension expectedAggSig actualAggSig

--------------------------------------------------------------------------------


-- elab :: (GaloisField n, Erase ty, Bounded n, Integral n) => Comp ty n -> Either String (ConstraintSystem n)
elab :: (Erase ty, Num n) => Comp ty n -> Either String (TypeErased n)
elab program = fmap eraseType (elaborate program)

cp :: (Erase ty, Num n) => Comp ty n -> Either String (TypeErased n)
cp program = ConstantPropagation.run <$> elab program



comp :: (GaloisField n, Erase ty, Bounded n, Integral n) => Comp ty n -> Either String (ConstraintSystem n)
comp program = fmap (compile . eraseType) (elaborate program)

optm :: (GaloisField n, Erase ty, Bounded n, Integral n) => Comp ty n -> Either String (ConstraintSystem n)
optm program = optimise <$> comp program


exec :: GaloisField n => Comp ty n -> [n] -> Either String n
exec program input = elaborate program >>= (`interpret` input)
