module Hash.Poseidon (hash) where

import Control.Monad (when)
import Data.Foldable (foldlM)
import Data.Vector (Vector, (!))
import qualified Hash.Poseidon.Constant as Constant
import Prelude hiding (round)


import Keelung

-- | "AddRoundConstants"
arc :: Vector Field -> Int -> [Field] -> [Field]
arc c it = mapI (\i x -> x + c ! (it + i))

-- | "SubWords"
sbox :: Int -> Int -> Int -> [Field] -> [Field]
sbox f p r = mapI go
  where
    go 0 = fullSBox
    go _ = if r < f `div` 2 || r >= f `div` 2 + p then fullSBox else id
    -- Full S-box of x⁵
    fullSBox x = x `pow` 5

-- | "MixLayer"
mix :: Vector (Vector Field) -> [Field] -> [Field]
mix m state =
    map
      (\i -> sum (mapI (\j x -> x * (m ! i ! j)) state))
      [0 .. length state - 1]

-- | The Poseidon hash function
hash :: [Field] -> Comp Field
hash msg = do
  -- check message length
  when
    (null msg || length msg > 6)
    (error "Invalid message length")
  -- constants
  let t = length msg + 1
  let roundsP = [56, 57, 56, 60, 60, 63, 64, 63]
  let f = 8
  let p = roundsP !! (t - 2)
  let c = Constant.c ! (t - 2)
  let m = Constant.m ! (t - 2)
  -- initialize state with 0 as the first element and message as the rest
  let initState = 0 : msg
  -- the round function consists of 3 components
  let round r = mix m . sbox f p r . arc c (r * t)
  -- apply the round function for `p` times on the initial state
  result <- foldlM (\state r -> reuse (round r state)) initState [0 .. f + p - 1]
  return $ head result