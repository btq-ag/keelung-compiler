{-# LANGUAGE DataKinds #-}

module Array where

import Keelung

echo :: Comp (Val ('Arr 'Num))
echo = inputs 4

modify :: Comp (Val ('Arr 'Num))
modify = do
    xs <- inputs 4 >>= thaw

    updateM xs 0 0
    updateM xs 1 1

    freeze xs

init :: Comp (Val ('Arr 'Bool))
init = do
    let xs = toArray $ replicate 4 false
    return xs

initM :: Comp (Val ('ArrM 'Bool))
initM = toArrayM $ replicate 4 false

initM2 :: Comp (Val ('Arr 'Bool))
initM2 = do
    xs <- toArrayM $ replicate 4 false
    freeze xs