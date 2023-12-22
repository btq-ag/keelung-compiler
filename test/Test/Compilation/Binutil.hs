module Test.Compilation.Binutil where

import Keelung hiding (elaborateAndEncode)
import Keelung.Compiler
import Keelung.Data.FieldInfo
import Data.ByteString.Lazy (ByteString)
import qualified Keelung.Compiler.Linker as Linker
import Keelung.CircuitFormat (Format(Snarkjs))
import Keelung.Encode (serializeR1CS, serializeInputAndWitnessToBin)

genCircuit :: (Encode t, GaloisField n, Integral n) => FieldInfo -> Comp t -> Either (Error n) ByteString
genCircuit fieldInfo prog = do
    elaborated <- elaborateAndEncode prog
    r1cs <- toR1CS . Linker.linkConstraintModule <$> compileO1Elab fieldInfo elaborated
    return $ serializeR1CS Snarkjs r1cs

genWtns :: (Encode t, GaloisField n, Integral n) => FieldInfo -> Comp t -> [Integer] -> [Integer] -> Either (Error n) ByteString
genWtns fieldInfo prog rawPublicInputs rawPrivateInputs = do
  elaborated <- elaborateAndEncode prog
  (_, _, witnesses) <- generateWitnessElab fieldInfo elaborated rawPublicInputs rawPrivateInputs
  return $ serializeInputAndWitnessToBin (fieldOrder fieldInfo) witnesses
