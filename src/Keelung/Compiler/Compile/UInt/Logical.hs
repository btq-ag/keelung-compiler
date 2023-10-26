{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use lambda-case" #-}
module Keelung.Compiler.Compile.UInt.Logical (compileXorUs) where

import Control.Monad
import Data.Bits qualified
import Data.Field.Galois
import Keelung.Compiler.Compile.Boolean qualified as Boolean
import Keelung.Compiler.Compile.Monad
import Keelung.Compiler.Syntax.Internal
import Keelung.Data.Reference
import Keelung.Data.U (U)

-- | Compile a consecutive sequence of XORs
compileXorUs :: (GaloisField n, Integral n) => Width -> RefU -> [Either RefU U] -> M n ()
compileXorUs width out xs = do
  forM_ [0 .. width - 1] $ \i -> do
    let column =
          map
            ( \x -> case x of
                Left refU -> Left (RefUBit width refU i)
                Right value -> Right (value `Data.Bits.testBit` i)
            )
            xs
    result <- Boolean.xorBs column
    case result of
      Left var -> writeRefBEq (RefUBit width out i) var
      Right val -> writeRefBVal (RefUBit width out i) val