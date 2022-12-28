{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Keelung.Compiler.Interpret.Kinded2 where

-- import Control.Monad.Except
-- import Control.Monad.Reader
-- import Control.Monad.State
-- import Data.Field.Galois (GaloisField)
-- import Data.Foldable (toList)
-- import qualified Data.IntMap.Strict as IntMap
-- import Keelung hiding (interpret)
-- import Keelung.Compiler.Error
-- import Keelung.Compiler.Interpret.Monad
-- import qualified Keelung.Compiler.Interpret.Monad as Monad
-- import Keelung.Compiler.Syntax.Inputs (Inputs (..))
-- import qualified Keelung.Compiler.Syntax.Inputs as Inputs
-- import Keelung.Data.Bindings (OIX (..), Partial, Struct (..), Witness)
-- import Keelung.Syntax.Counters
-- import Data.Semiring (Semiring(..))
-- import Keelung.Types

-- | Interpret a program with inputs and return outputs along with the witness
-- run' :: (FreeVar t, Interpret (Error n) t n, GaloisField n, Integral n) => Elaborated t -> Inputs n -> Either (Typed.Error n) ([n], Witness n)
-- run' (Elaborated expr comp) inputs = Monad.runM inputs undefined

-- -- run2 :: (FreeVar t, Interpret t n, GaloisField n, Integral n) => Elaborated t -> Inputs n -> Either (Error n) ([n], Witness n)
-- -- run2

-- type M2 n = ExceptT (Error n) (ReaderT (Inputs n) (State (Partial n)))

-- -- liftI :: M n a -> M2 n a
-- -- liftI = withExceptT InterpretError

-- runM2 :: Inputs n -> M2 n a -> Either (Error n) (a, Witness n)
-- runM2 inputs p =
--   let counters = Inputs.varCounters inputs
--       -- construct the initial partial Bindings from Inputs
--       initBindings =
--         OIX
--           { ofO =
--               Struct
--                 { structF = (getCount OfOutput OfField counters, mempty),
--                   structB = (getCount OfOutput OfBoolean counters, mempty),
--                   structU = IntMap.mapWithKey (\w _ -> (getCount OfOutput (OfUInt w) counters, mempty)) (Inputs.uintInputs inputs)
--                 },
--             ofI =
--               Struct
--                 { structF = (getCount OfInput OfField counters, IntMap.fromList $ zip [0 ..] (toList (Inputs.numInputs inputs))),
--                   structB = (getCount OfInput OfBoolean counters, IntMap.fromList $ zip [0 ..] (toList (Inputs.boolInputs inputs))),
--                   structU = IntMap.mapWithKey (\w bindings -> (getCount OfInput (OfUInt w) counters, IntMap.fromList $ zip [0 ..] (toList bindings))) (Inputs.uintInputs inputs)
--                 },
--             ofX =
--               Struct
--                 { structF = (getCount OfIntermediate OfField counters, mempty),
--                   structB = (getCount OfIntermediate OfBoolean counters, mempty),
--                   structU = IntMap.mapWithKey (\w _ -> (getCount OfIntermediate (OfUInt w) counters, mempty)) (Inputs.uintInputs inputs)
--                 }
--           }
--    in do
--         let (result, partialBindings) = runState (runReaderT (runExceptT p) inputs) initBindings
--         -- make the partial Bindings total
--         case Typed.toTotal partialBindings of
--           Left unbound -> Left (InterpretError (Typed.VarUnassignedError unbound))
--           Right bindings -> case result of
--             Left err -> Left err
--             Right value -> Right (value, bindings)

-- --------------------------------------------------------------------------------

-- instance GaloisField n => Interpret (Error n) Integer n where
--   interpret x = return [fromIntegral x]


-- instance GaloisField n => Interpret (Error n) Rational n where
--   interpret x = return [fromRational x]

-- instance GaloisField n => Interpret (Error n) Bool n where
--   interpret True = return [one]
--   interpret False = return [zero]

-- -- lookupF :: (MonadState (Partial n) m, MonadError (Error n) m, GaloisField n, Integral n) => Var -> m n
-- -- lookupF var = withExceptT InterpretError $ Typed.lookupF va

-- -- instance (GaloisField n, Integral n) => Interpret (Error n) Field n where
-- --   interpret val = case val of
-- --     Integer n -> interpret n
-- --     Rational n -> interpret n
-- --     VarF var -> pure <$> lookupF var
-- --     VarFI var -> pure <$> lookupVarFI var
-- --     Add x y -> zipWith (+) <$> interpret x <*> interpret y
-- --     Sub x y -> zipWith (-) <$> interpret x <*> interpret y
-- --     Mul x y -> zipWith (*) <$> interpret x <*> interpret y
-- --     Div x y -> zipWith (/) <$> interpret x <*> interpret y
-- --     IfF p x y -> do
-- --       p' <- interpret p
-- --       case p' of
-- --         [0] -> interpret y
-- --         _ -> interpret x
-- --     BtoF x -> interpret x