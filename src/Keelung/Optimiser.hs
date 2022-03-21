{-# LANGUAGE BangPatterns #-}

module Keelung.Optimiser where

import Control.Monad
import Data.Field.Galois (GaloisField)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Keelung.Constraint
import Keelung.Constraint.CoeffMap (CoeffMap (..))
import qualified Keelung.Constraint.CoeffMap as CoeffMap
import Keelung.Optimiser.Monad
import Keelung.Syntax.Common

--------------------------------------------------------------------------------

-- | Smart constructor for the CAdd constraint
cadd :: GaloisField n => n -> [(Var, n)] -> Constraint n
cadd !c !xs = CAdd c (CoeffMap.fromList xs)

-- | Normalize constraints by substituting roots/constants
-- for the variables that appear in the constraint. Note that, when
-- normalizing a multiplicative constraint, it may be necessary to
-- convert it into an additive constraint.
substConstraint :: GaloisField n => Constraint n -> OptiM n (Constraint n)
substConstraint !constraint = case constraint of
  CAdd constant coeffMap -> do
    (constant', coeffMap') <- foldM go (constant, mempty) (CoeffMap.toList coeffMap)
    return $ CAdd constant' (CoeffMap coeffMap')
    where
      go :: GaloisField n => (n, IntMap n) -> (Var, n) -> OptiM n (n, IntMap n)
      go (accConstant, accMapping) (var, coeff) = do
        -- see if we can substitute a variable with some constant
        result <- lookupVar var
        case result of
          Left _ -> do
            -- it's okay if we cannot substitute a variable with some constant
            -- we can still replace the variable with its root
            var' <- rootOfVar var
            return (accConstant, IntMap.insert var' coeff accMapping)
          Right val -> do
            let val' = val * coeff
            -- if `value * coeff` is 0 then we should remove it
            if val' == 0
              then return (accConstant, accMapping)
              else return (accConstant + val', accMapping)
  CMul (c, x) (d, y) !ez -> do
    bx <- lookupVar x
    by <- lookupVar y
    bz <- lookupTerm ez
    case (bx, by, bz) of
      (Left rx, Left ry, Left (e, rz)) ->
        return
          $! CMul (c, rx) (d, ry) (e, Just rz)
      (Left rx, Left ry, Right e) ->
        return
          $! CMul (c, rx) (d, ry) (e, Nothing)
      (Left rx, Right d0, Left (e, rz)) ->
        return
          $! cadd 0 [(rx, c * d * d0), (rz, - e)]
      (Left rx, Right d0, Right e) ->
        return
          $! cadd (- e) [(rx, c * d * d0)]
      (Right c0, Left ry, Left (e, rz)) ->
        return
          $! cadd 0 [(ry, c0 * c * d), (rz, - e)]
      (Right c0, Left ry, Right e) ->
        return
          $! cadd (- e) [(ry, c0 * c * d)]
      (Right c0, Right d0, Left (e, rz)) ->
        return
          $! cadd (c * c0 * d * d0) [(rz, - e)]
      (Right c0, Right d0, Right e) ->
        return
          $! cadd (c * c0 * d * d0 - e) []
    where
      lookupTerm (e, Nothing) = return (Right e)
      lookupTerm (e, Just z) = do
        result <- lookupVar z
        case result of
          Left rz -> return (Left (e, rz))
          Right e0 -> return (Right (e * e0))
