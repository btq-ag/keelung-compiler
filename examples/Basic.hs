-- {-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE DataKinds #-}

module Basic where

import Keelung

--------------------------------------------------------------------------------

identity :: M GF181 (Ref ('V 'Num))
identity = freshInput

add3 :: Comp GF181 'Num
-- add3 :: M GF181 ('Ref ('Var 'Num)) (Reference ('Var 'Num))
add3 = do
  x <- freshInput
  return $ Var x + 3

-- cond :: Comp GF181 'Num
-- cond = do
--   x <- freshInput
--   let p = x `eq` 3
--   if p
--     then return 12
--     else return 789

-- cond2 :: M GF181 ty (TExpr TBool GF181)
-- cond2 = do
--   x <- freshInput
--   return $ x `eq` 3

--------------------------------------------------------------------------------

-- run :: Either String (Elaborated Type GF181)
-- run = elaborate

-- com ::
--   GaloisField f =>
--   Comp ty f ->
--   Either String (ConstraintSystem f)
-- com = fmap compile . elaborate
