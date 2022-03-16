{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RebindableSyntax #-}

module Basic where

import AggregateSignature.Program (aggregateSignature)
import AggregateSignature.Util
import Keelung

--------------------------------------------------------------------------------

identity :: Comp GF181 'Num
identity = Var <$> freshInput

add3 :: Comp GF181 'Num
-- add3 :: M GF181 ('Ref ('Var 'Num)) (Reference ('Var 'Num))
add3 = do
  x <- freshInput
  return $ Var x + 3

cond :: Comp GF181 'Num
cond = do
  x <- freshInput
  if Var x `Eq` 3
    then return 12
    else return 789

cond2 :: Comp GF181 'Bool
cond2 = do
  x <- freshInput
  return $ Var x `Eq` 3

loop1 :: Comp GF181 'Num
loop1 = do
  arr <- freshInputs 4
  reduce 0 [0 .. 3] $ \accum i -> do 
    x <- access arr i 
    return $ accum + Var x


aggSig :: Comp GF181 'Bool
aggSig = do
  let settings = Settings False True False False False
  let setup = makeSetup 1 1 42 settings
  aggregateSignature setup

--------------------------------------------------------------------------------

-- run :: Either String (Elaborated Type GF181)
-- run = elaborate

-- com ::
--   GaloisField f =>
--   Comp ty f ->
--   Either String (ConstraintSystem f)
-- com = fmap compile . elaborate
