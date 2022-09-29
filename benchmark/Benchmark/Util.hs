{-# LANGUAGE DataKinds #-}

module Benchmark.Util
  ( elaborate,
    compile,
    optimize0,
    optimize1,
    optimize2,
  )
where

import Keelung (Comp, GF181)
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
elaborate :: Language.Elaborable t => Comp t -> Either Language.ElabError Elaborated
elaborate = Language.elaborate

-- | Compile only (without constant propagation or any other optimizations)
compile :: Language.Elaborable t => Comp t -> Either (Compiler.Error GF181) (Compiler.ConstraintSystem GF181)
compile = Compiler.compile

-- | Compile + constant propagation
optimize0 :: Language.Elaborable t => Comp t -> Either (Compiler.Error GF181) (Compiler.ConstraintSystem GF181)
optimize0 = Compiler.optimize0

-- | Compile + constant propagation + optimization I
optimize1 :: Language.Elaborable t => Comp t -> Either (Compiler.Error GF181) (Compiler.ConstraintSystem GF181)
optimize1 = Compiler.optimize1

-- | Compile + constant propagation + optimization I + optimization II
optimize2 :: Language.Elaborable t => Comp t -> Either (Compiler.Error GF181) (Compiler.ConstraintSystem GF181)
optimize2 = Compiler.optimize2

-- benchElaborate :: Comp t -> ByteString
-- benchElaborate = encode . elaborate

-- benchRewrite :: Comp t -> ByteString
-- benchRewrite = encode . elaborateAndRewrite

-- benchInterpret :: (GaloisField n, Integral n, Serialize n) => Comp t -> [n] -> ByteString
-- benchInterpret prog = encode . interpret prog

-- benchEraseType :: Comp t -> String
-- benchEraseType prog = show (erase prog :: Either (Error GF181) (TypeErased GF181))

-- benchCompile :: Comp t -> String
-- benchCompile prog = show (compile prog :: Either (Error GF181) (ConstraintSystem GF181))

-- benchPropogateConstant :: Comp t -> String
-- benchPropogateConstant prog = show (optimize0 prog :: Either (Error GF181) (ConstraintSystem GF181))

-- benchOptimize2 :: Comp t -> String
-- benchOptimize2 prog = show (optimize2 prog :: Either (Error GF181) (ConstraintSystem GF181))

-- benchOptimize3 :: Comp t -> String
-- benchOptimize3 prog = show (optimize3 prog :: Either (Error GF181) (ConstraintSystem GF181))

-- benchOptimizeWithInput :: (GaloisField n, Bounded n, Integral n) => Comp t -> [n] -> String
-- benchOptimizeWithInput prog = show . optimizeWithInput prog
