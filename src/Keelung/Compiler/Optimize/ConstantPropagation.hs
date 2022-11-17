module Keelung.Compiler.Optimize.ConstantPropagation (run) where

import Data.Field.Galois (GaloisField)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Keelung.Compiler.Syntax.Untyped
import qualified Keelung.Constraint.Polynomial as Poly
import Keelung.Constraint.R1C (R1C (..))

--------------------------------------------------------------------------------

-- 1. Propagate constant in assignments
-- 2. Propagate constant in the expression and assertions
run :: (Integral n, GaloisField n) => TypeErased n -> TypeErased n
run (TypeErased expr counters assertions assignments numBinReps customBinReps) =
  let (bindings, assignments') = propagateInAssignments assignments
      expr' = propagateConstant bindings <$> expr
      assertions' = map (propagateConstant bindings) assertions

      assignments'' =
        assignments'
          <> map
            ( \(var, (bw, val)) -> Assignment var $ case bw of
                BWNumber w -> Number w val
                BWUInt w -> UInt w val
                BWBoolean -> Boolean val
            )
            (IntMap.toList bindings)
   in TypeErased expr' counters assertions' assignments'' numBinReps customBinReps

-- Propagate constant in assignments and return the bindings for later use
propagateInAssignments :: (Integral n, GaloisField n) => [Assignment n] -> (IntMap (BitWidth, n), [Assignment n])
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
extractBindings :: [Assignment n] -> (IntMap (BitWidth, n), [Assignment n])
extractBindings = go IntMap.empty []
  where
    go :: IntMap (BitWidth, n) -> [Assignment n] -> [Assignment n] -> (IntMap (BitWidth, n), [Assignment n])
    go bindings rest [] = (bindings, rest)
    go bindings rest (Assignment var (Number w val) : xs) =
      go (IntMap.insert var (BWNumber w, val) bindings) rest xs
    go bindings rest (Assignment var (UInt w val) : xs) =
      go (IntMap.insert var (BWUInt w, val) bindings) rest xs
    go bindings rest (Assignment var (Boolean val) : xs) =
      go (IntMap.insert var (BWBoolean, val) bindings) rest xs
    go bindings rest (others : xs) = go bindings (others : rest) xs

-- constant propogation
propagateConstant :: (GaloisField n, Integral n) => IntMap (BitWidth, n) -> Expr n -> Expr n
propagateConstant bindings = propogate
  where
    propogate e = case e of
      Number _ _ -> e
      UInt _ _ -> e
      Boolean _ -> e
      Var bw var -> case IntMap.lookup var bindings of
        Nothing -> Var bw var
        Just (BWNumber w, val) -> Number w val
        Just (BWUInt w, val) -> UInt w val
        Just (BWBoolean, val) -> Boolean val
      UVar w var -> case IntMap.lookup var bindings of
        Nothing -> UVar w var
        Just (BWNumber w', val) -> Number w' val
        Just (BWUInt _, val) -> UInt w val
        Just (BWBoolean, val) -> Boolean val
      Rotate w n x -> Rotate w n (propogate x)
      NAryOp w op x y es -> NAryOp w op (propogate x) (propogate y) (fmap propogate es)
      BinaryOp w op x y -> BinaryOp w op (propogate x) (propogate y)
      If w p x y -> If w (propogate p) (propogate x) (propogate y)
      EmbedR1C w r1c -> EmbedR1C w (propagateR1C r1c)

    propagateR1C (R1C a b c) = R1C (a >>= propogatePoly) (b >>= propogatePoly) (c >>= propogatePoly)

    propogatePoly xs =
      let (constant, coeffs) = Poly.view xs
          (constant', coeffs') = foldl go (constant, mempty) (IntMap.toList coeffs)
       in Poly.buildEither constant' coeffs'
      where
        go (constant, coeffs) (var, coeff) = case IntMap.lookup var bindings of
          Nothing -> (constant, (var, coeff) : coeffs)
          Just (_, val) -> (constant + coeff * val, coeffs)
