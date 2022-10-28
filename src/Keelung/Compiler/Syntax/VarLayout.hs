-- {-# LANGUAGE DeriveAnyClass #-}
-- {-# LANGUAGE DeriveGeneric #-}

module Keelung.Compiler.Syntax.VarLayout where 
--   ( VarLayout,
--     layoutVarCounters,
--     makeVarLayout,
--     bumpIntermediateVar,
--     updateIntermediateVarSize,
--     boolVarsRange,
--     pinnedVarsRange,
--     outputVarsRange,
--     totalVarSize
--   )

-- import Control.DeepSeq (NFData)
-- import GHC.Generics (Generic)
-- import Keelung.Syntax.VarCounters hiding (totalVarSize)
-- import Keelung.Types (Var)

-- data VarLayout = VarLayout
--   { -- | Counters for each group of variables
--     layoutVarCounters :: !VarCounters,
--     -- | Bit width of a field element
--     layoutFieldBitWidth :: !Int
--   }
--   deriving (Show, Eq, Generic, NFData)

-- -- | Constructor for 'VarLayout'
-- makeVarLayout :: VarCounters -> Int -> VarLayout
-- makeVarLayout = VarLayout

-- bumpIntermediateVar :: VarLayout -> (VarLayout, Var)
-- bumpIntermediateVar (VarLayout counters numWidth) =
--   let var = intermediateVarSize counters
--    in ( VarLayout (bumpIntermediateVar counters) numWidth,
--         var
--       )

-- updateIntermediateVarSize :: VarLayout -> Int -> VarLayout
-- updateIntermediateVarSize (VarLayout counters numWidth) size =
--   VarLayout (setIntermediateVarSize size counters) numWidth

-- -- | Range of output variables
-- outputVarsRange :: VarLayout -> (Int, Int)
-- outputVarsRange (VarLayout counters _) = (0, outputVarSize counters - 1)

-- -- | Range of variables that should not be optimized away
-- pinnedVarsRange :: VarLayout -> (Int, Int)
-- pinnedVarsRange (VarLayout counters numWidth) =
--   let end =
--         outputVarSize counters
--           + numInputVarSize counters
--           + boolInputVarSize counters
--           + numWidth * numInputVarSize counters
--    in (0, end)

-- -- | Range of Boolean variables
-- boolVarsRange :: VarLayout -> (Int, Int)
-- boolVarsRange (VarLayout counters numWidth) =
--   let start =
--         outputVarSize counters
--           + numInputVarSize counters
--       end =
--         start
--           + boolInputVarSize counters
--           + numWidth * numInputVarSize counters
--    in (start, end)

-- totalVarSize :: VarLayout -> Int
-- totalVarSize (VarLayout counters numWidth) =
--   outputVarSize counters
--     + numInputVarSize counters
--     + boolInputVarSize counters
--     + numWidth * numInputVarSize counters
--     + intermediateVarSize counters