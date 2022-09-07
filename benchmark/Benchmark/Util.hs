{-# LANGUAGE DataKinds #-}

module Benchmark.Util
  ( elaborate,
    compile,
    optimize1,
    optimize2,
    optimize3,
  )
where

import Keelung (Comp, GF181, Val)
import qualified Keelung as Language
import qualified Keelung.Compiler as Compiler
import qualified Keelung.Error as Language
import Keelung.Syntax.Typed (Elaborated)

-- import Data.ByteString (ByteString)
-- import Data.Serialize (Serialize, encode)
-- import Keelung (elaborate, GF181)
-- import Keelung.Compiler
-- import Keelung.Compiler.Optimize (elaborateAndRewrite)
-- import Keelung.Monad (Comp)
-- import Keelung.Syntax (Val)

-- | Elaborate
elaborate :: Comp (Val t) -> Either Language.ElabError Elaborated
elaborate = Language.elaborate

-- | Compile only (without constant propagation or any other optimizations)
compile :: Comp (Val t) -> Either (Compiler.Error GF181) (Compiler.ConstraintSystem GF181)
compile = Compiler.compile

-- | Compile + constant propagation
optimize1 :: Comp (Val t) -> Either (Compiler.Error GF181) (Compiler.ConstraintSystem GF181)
optimize1 = Compiler.optimize1

-- | Compile + constant propagation + optimization I
optimize2 :: Comp (Val t) -> Either (Compiler.Error GF181) (Compiler.ConstraintSystem GF181)
optimize2 = Compiler.optimize2

-- | Compile + constant propagation + optimization I + optimization II
optimize3 :: Comp (Val t) -> Either (Compiler.Error GF181) (Compiler.ConstraintSystem GF181)
optimize3 = Compiler.optimize3

-- benchElaborate :: Comp (Val t) -> ByteString
-- benchElaborate = encode . elaborate

-- benchRewrite :: Comp (Val t) -> ByteString
-- benchRewrite = encode . elaborateAndRewrite

-- benchInterpret :: (GaloisField n, Integral n, Serialize n) => Comp (Val t) -> [n] -> ByteString
-- benchInterpret prog = encode . interpret prog

-- benchEraseType :: Comp (Val t) -> String
-- benchEraseType prog = show (erase prog :: Either (Error GF181) (TypeErased GF181))

-- benchCompile :: Comp (Val t) -> String
-- benchCompile prog = show (compile prog :: Either (Error GF181) (ConstraintSystem GF181))

-- benchPropogateConstant :: Comp (Val t) -> String
-- benchPropogateConstant prog = show (optimize1 prog :: Either (Error GF181) (ConstraintSystem GF181))

-- benchOptimize2 :: Comp (Val t) -> String
-- benchOptimize2 prog = show (optimize2 prog :: Either (Error GF181) (ConstraintSystem GF181))

-- benchOptimize3 :: Comp (Val t) -> String
-- benchOptimize3 prog = show (optimize3 prog :: Either (Error GF181) (ConstraintSystem GF181))

-- benchOptimizeWithInput :: (GaloisField n, Bounded n, Integral n) => Comp (Val t) -> [n] -> String
-- benchOptimizeWithInput prog = show . optimizeWithInput prog
