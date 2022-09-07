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

  putStrLn "Number of constriants: fullAdder"
  forM_ [1, 2, 4, 8] $ \i -> do
    asGF181 (optimize2 (fullAdderT i)) >>= printCS False

  forM_ [1, 2, 4, 8] $ \n -> do
    putStrLn $ "Number of constriants: multiplier " <> show n
    forM_ [1, 2, 4, 8] $ \i -> do
      asGF181 (optimize2 (multiplierT n i)) >>= printCS False

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
