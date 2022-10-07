module Main where

import qualified Array.Immutable as M
-- import qualified Array.Mutable as M
import Control.Monad
import qualified Data.IntSet as IntSet
import Keelung (GF181)
import Keelung.Compiler
import Keelung.Constraint.R1CS

asGF181' :: Either (Error GF181) a -> IO a
asGF181' (Left err) = error $ show err
asGF181' (Right x) = return x

printR1CS :: Bool -> R1CS GF181 -> IO ()
printR1CS printConstraints r1cs = do
  let constraints = r1csConstraints r1cs

  if printConstraints
    then do
      -- forM_ constraints $ \constraint -> do
      --   print $ fmap N constraint
      print r1cs
      putStrLn "========="
    else do
      print $ length constraints + IntSet.size (r1csBoolVars r1cs)

main :: IO ()
main = do
  -- putStrLn "Number of constriants: fromString"
  -- forM_ [1, 2, 4, 8] $ \i -> do
  --   asGF181' (compile (return $ fromString (replicate i 'A'))) >>= print . Set.size . csConstraints

  putStrLn "O0: fullAdder"
  forM_ [1, 2, 4, 8, 16, 32] $ \i -> do
    asGF181' (optimize0 (M.fullAdderT i)) >>= printR1CS False . toR1CS

  putStrLn "O1: fullAdder"
  forM_ [1, 2, 4, 8, 16, 32] $ \i -> do
    asGF181' (optimize1 (M.fullAdderT i)) >>= printR1CS False . toR1CS

  putStrLn "O2: fullAdder"
  forM_ [1, 2, 4, 8, 16, 32] $ \i -> do
    asGF181' (optimize2 (M.fullAdderT i)) >>= printR1CS False . toR1CS

  putStrLn "O0: multiplier"
  forM_ [1, 2, 4, 8, 16, 32] $ \n -> do
    asGF181' (optimize0 (M.multiplierT n 3)) >>= printR1CS False . toR1CS

  putStrLn "O1: multiplier"
  forM_ [1, 2, 4, 8, 16, 32] $ \n -> do
    asGF181' (optimize1 (M.multiplierT n 3)) >>= printR1CS False . toR1CS

  putStrLn "O2: multiplier"
  forM_ [1, 2, 4, 8, 16, 32] $ \n -> do
    asGF181' (optimize2 (M.multiplierT n 3)) >>= printR1CS False . toR1CS

-- fa :: IO ()
-- fa = do
--   putStrLn "fullAdder"
--   cs <- asGF181' (optimize1 (fullAdderT 2))
--   let constraints = csConstraints cs

--   putStrLn "before"
--   print $ Set.size constraints
--   forM_ (Set.toList constraints) $ \constraint -> do
--     print $ fmap N constraint

--   let cs' = Optimizer.optimize cs
--   let constraints' = csConstraints cs'

--   putStrLn "after"
--   print $ Set.size constraints'
--   forM_ (Set.toList constraints') $ \constraint -> do
--     print $ fmap N constraint

--   let cs'' = Optimizer.optimize1 cs'
--   let constraints'' = csConstraints cs''

--   putStrLn "after"
--   print $ Set.size constraints''
--   forM_ (Set.toList constraints'') $ \constraint -> do
--     print $ fmap N constraint

--   putStrLn "complete"

--   print cs''
