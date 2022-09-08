module Main where

import Array.Immutable
import Control.Monad
import qualified Data.Set as Set
import Keelung (GF181, N (N))
import Keelung.Compiler

asGF181 :: Either (Error GF181) a -> IO a
asGF181 (Left err) = error $ show err
asGF181 (Right x) = return x

printCS :: Bool -> ConstraintSystem GF181 -> IO ()
printCS printConstraints cs = do
  let constraints = csConstraints cs
  print $ Set.size constraints
  when printConstraints $ do
    forM_ (Set.toList constraints) $ \constraint -> do
      print $ fmap N constraint
    putStrLn "========="

main :: IO ()
main = do
  -- putStrLn "Number of constriants: fromString"
  -- forM_ [1, 2, 4, 8] $ \i -> do
  --   asGF181 (compile (return $ fromString (replicate i 'A'))) >>= print . Set.size . csConstraints

  putStrLn "O0: fullAdder"
  forM_ [1, 2] $ \i -> do
    asGF181 (optimize1 (fullAdderT i)) >>= printCS True

  -- putStrLn "O1: fullAdder"
  -- forM_ [1, 2, 4, 8, 16, 32] $ \i -> do
  --   asGF181 (optimize2 (fullAdderT i)) >>= printCS False

  -- putStrLn "O2: fullAdder"
  -- forM_ [1, 2, 4, 8, 16, 32] $ \i -> do
  --   asGF181 (optimize3 (fullAdderT i)) >>= printCS False

  -- putStrLn "O0: multiplier"
  -- forM_ [1, 2, 4, 8, 16, 32] $ \n -> do
  --   asGF181 (optimize1 (multiplierT n 3)) >>= printCS False

  -- putStrLn "O1: multiplier"
  -- forM_ [1, 2, 4, 8, 16, 32] $ \n -> do
  --   asGF181 (optimize2 (multiplierT n 3)) >>= printCS False

  -- putStrLn "O2: multiplier"
  -- forM_ [1, 2, 4, 8, 16, 32] $ \n -> do
  --   asGF181 (optimize3 (multiplierT n 3)) >>= printCS False

-- fa :: IO ()
-- fa = do
--   putStrLn "fullAdder"
--   cs <- asGF181 (optimize2 (fullAdderT 2))
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

--   let cs'' = Optimizer.optimize2 cs'
--   let constraints'' = csConstraints cs''

--   putStrLn "after"
--   print $ Set.size constraints''
--   forM_ (Set.toList constraints'') $ \constraint -> do
--     print $ fmap N constraint

--   putStrLn "complete"

--   print cs''
