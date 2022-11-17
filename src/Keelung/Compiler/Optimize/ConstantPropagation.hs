module Keelung.Compiler.Optimize.ConstantPropagation (run) where

import Data.Field.Galois (GaloisField)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Keelung.Compiler.Syntax.Untyped
import Keelung.Types (Var)

--------------------------------------------------------------------------------

-- | "Bindings" are assignments with constant values on the RHS
data Bindings n = Bindings
  { bindingsF :: IntMap (Width, n), -- Field elements
    bindingsB :: IntMap n, -- Booleans
    bindingsU :: IntMap (Width, n) -- Unsigned integers
  }

addBindingF :: Var -> (Width, n) -> Bindings n -> Bindings n
addBindingF var n (Bindings fs bs us) = Bindings (IntMap.insert var n fs) bs us

addBindingB :: Var -> n -> Bindings n -> Bindings n
addBindingB var n (Bindings fs bs us) = Bindings fs (IntMap.insert var n bs) us

addBindingU :: Var -> (Width, n) -> Bindings n -> Bindings n
addBindingU var n (Bindings fs bs us) = Bindings fs bs (IntMap.insert var n us)

toAssignments :: Bindings n -> [Assignment n]
toAssignments (Bindings fs bs us) =
  [Assignment var (Number fw val) | (var, (fw, val)) <- IntMap.toList fs]
    ++ [Assignment var (Boolean val) | (var, val) <- IntMap.toList bs]
    ++ [Assignment var (UInt w val) | (var, (w, val)) <- IntMap.toList us]

--------------------------------------------------------------------------------

-- 1. Propagate constant in assignments
-- 2. Propagate constant in the expression and assertions
run :: (Integral n, GaloisField n) => TypeErased n -> TypeErased n
run (TypeErased expr counters assertions assignments numBinReps customBinReps) =
  let (bindings, assignments') = propagateInAssignments assignments
      expr' = propagateConstant bindings <$> expr
      assertions' = map (propagateConstant bindings) assertions
   in -- bindings are converted back to assignments
      TypeErased expr' counters assertions' (assignments' <> toAssignments bindings) numBinReps customBinReps

-- Propagate constant in assignments and return the bindings for later use
propagateInAssignments :: (Integral n, GaloisField n) => [Assignment n] -> (Bindings n, [Assignment n])
propagateInAssignments xs =
  let (bindings, assignments) = extractBindings xs
      assignments' =
        map
          ( \(Assignment var expr) ->
              Assignment var (propagateConstant bindings expr)
          )
          assignments
   in (bindings, assignments')

-- Extract bindings of constant values and collect them as an IntMap
-- and returns the rest of the assignments
extractBindings :: [Assignment n] -> (Bindings n, [Assignment n])
extractBindings = go (Bindings mempty mempty mempty) []
  where
    go :: Bindings n -> [Assignment n] -> [Assignment n] -> (Bindings n, [Assignment n])
    go bindings rest [] = (bindings, rest)
    go bindings rest (Assignment var (Number w val) : xs) =
      go (addBindingF var (w, val) bindings) rest xs
    go bindings rest (Assignment var (UInt w val) : xs) =
      go (addBindingU var (w, val) bindings) rest xs
    go bindings rest (Assignment var (Boolean val) : xs) =
      go (addBindingB var val bindings) rest xs
    go bindings rest (others : xs) = go bindings (others : rest) xs

-- constant propogation
propagateConstant :: (GaloisField n, Integral n) => Bindings n -> Expr n -> Expr n
propagateConstant bindings = propogate
  where
    propogate e = case e of
      Number _ _ -> e
      UInt _ _ -> e
      Boolean _ -> e
      Var bw var -> case bw of
        BWNumber w -> case IntMap.lookup var (bindingsF bindings) of
          Nothing -> Var bw var
          Just (_, val) -> Number w val
        BWBoolean -> case IntMap.lookup var (bindingsB bindings) of
          Nothing -> Var bw var
          Just val -> Boolean val
        BWUInt w -> case IntMap.lookup var (bindingsU bindings) of
          Nothing -> Var bw var
          Just (_, val) -> UInt w val
      UVar w var -> case IntMap.lookup var (bindingsU bindings) of
        Nothing -> Var (BWUInt w) var
        Just (_, val) -> UInt w val
      Rotate w n x -> Rotate w n (propogate x)
      NAryOp w op x y es -> NAryOp w op (propogate x) (propogate y) (fmap propogate es)
      BinaryOp w op x y -> BinaryOp w op (propogate x) (propogate y)
      If w p x y -> If w (propogate p) (propogate x) (propogate y)