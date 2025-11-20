{-# OPTIONS_GHC -Wno-missing-export-lists #-}
module Utils where

nTimes :: (Num b, Eq b) => b -> (a -> a) -> (a -> a)
nTimes 0 _ = id
nTimes n f = f . nTimes (n-1) f

(&&?) :: Monad m => m Bool -> m Bool -> m Bool
p &&? q = do
  b <- p
  if b then q else return False
