{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RebindableSyntax #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use <&>" #-}

module Basic where

import qualified AggregateSignature.Program.Keelung as Keelung 
import AggregateSignature.Util
import qualified Data.IntMap as IntMap
import qualified Data.Set as Set
import Keelung 
import qualified Keelung.Optimiser.ConstantPropagation as ConstantPropagation

--------------------------------------------------------------------------------

constant1 :: Comp 'Num GF181
constant1 = do
  return $ 1 + 1

identity :: Comp 'Num GF181
identity = Var <$> freshInput

identityB :: Comp 'Bool GF181
identityB = Var <$> freshInput

add3 :: Comp 'Num GF181
add3 = do
  x <- freshInput
  return $ Var x + 3

-- takes an input and see if its equal to 3
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
  Keelung.aggregateSignature setup

checkSig :: Int -> Int -> Comp 'Bool GF181
checkSig dimension n = do
  let settings = Settings True False False False False
  let Setup _ _ publicKey signatures _ _ = makeSetup dimension n 42 settings
  expectedAggSig <- freshInputs dimension
  actualAggSig <- Keelung.computeAggregateSignature publicKey signatures
  arrayEq dimension expectedAggSig actualAggSig

-- checkBitBoolean :: Int -> Int -> [GF181] 
-- checkBitBoolean dimension n =
--   let settings = Settings False False True False False
--       setup = makeSetup dimension n 42 settings
--   in  genInputFromSetup setup

checkSquares :: Int -> Int -> Comp 'Bool GF181
checkSquares dimension n = do
  let settings = Settings False False False True False
  let Setup _ _ _ signatures _ _ = makeSetup dimension n 42 settings
  sigSquares <- freshInputs2 n dimension
  Keelung.checkSquares n dimension signatures sigSquares

checkSigSize :: Int -> Int -> Comp 'Bool GF181
checkSigSize dimension n = do
  let settings = Settings False False False True False
  let Setup _ _ _ signatures _ _ = makeSetup dimension n 42 settings
  sigBitStrings <- freshInputs3 n dimension 14

  
  Keelung.checkSignaturesBitStringSize dimension signatures sigBitStrings

checkSigLength :: Int -> Int -> Comp 'Bool GF181
checkSigLength dimension n = do
  sigSquares <- freshInputs2 n dimension
  sigLengths <- freshInputs n
  Keelung.checkLength n dimension sigSquares sigLengths

--------------------------------------------------------------------------------

bench :: Comp 'Bool GF181 -> Settings -> Int -> Int -> Either String (Int, Int, Int)
bench program settings dimension n = do 
  let input = genInputFromSetup (makeSetup dimension n 42 settings)
  cs <- comp program
  cs' <- optm program
  (_, cs'') <- optmWithInput program input
  return (Set.size (csConstraints cs), Set.size (csConstraints cs'), Set.size (csConstraints cs''))
      
-- #1
runCheckSig :: Int -> Int -> Either String (Int, Int, Int)
runCheckSig dimension n = do 
  let settings = Settings True False False False False
  bench (checkSig dimension n) settings dimension n

-- #2
runCheckSigSize :: Int -> Int -> Either String (Int, Int, Int)
runCheckSigSize dimension n = do 
  let settings = Settings False True False False False
  bench (checkSigSize dimension n) settings dimension n

-- #4
runCheckSquares :: Int -> Int -> Either String (Int, Int, Int)
runCheckSquares dimension n = do 
  let settings = Settings False False False True False
  bench (checkSquares dimension n) settings dimension n
      
-- #5
runCheckLength :: Int -> Int -> Either String (Int, Int, Int)
runCheckLength dimension n = do 
  let settings = Settings False False False True True
  bench (checkSigLength dimension n) settings dimension n
      
--------------------------------------------------------------------------------

-- elaborate & erase type
elab :: (Erase ty, Num n) => Comp ty n -> Either String (TypeErased n)
elab program = fmap eraseType (elaborate program)

-- elaborate & erase type & propagate constants
cp :: (Erase ty, Num n) => Comp ty n -> Either String (TypeErased n)
cp program = ConstantPropagation.run <$> elab program

comp :: (GaloisField n, Erase ty, Bounded n, Integral n) => Comp ty n -> Either String (ConstraintSystem n)
comp program = elaborate program >>= return . compile . ConstantPropagation.run . eraseType

optm :: (GaloisField n, Erase ty, Bounded n, Integral n) => Comp ty n -> Either String (ConstraintSystem n)
optm program = optimise <$> comp program

-- partial evaluation with inputs
optmWithInput :: (GaloisField n, Bounded n, Integral n, Erase ty) => Comp ty n -> [n] -> Either String ([(Var, DebugGF n)], ConstraintSystem n)
optmWithInput program input = do
  cs <- optm program
  let (witness', cs') = optimiseWithInput input cs
  return (IntMap.toList $ fmap DebugGF witness', cs')
