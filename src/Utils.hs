{-# OPTIONS_GHC -Wno-missing-export-lists #-}
module Utils where
import Data.List

nTimes :: (Num b, Eq b) => b -> (a -> a) -> (a -> a)
nTimes 0 _ = id
nTimes n f = f . nTimes (n-1) f

zip' :: [a] -> [b] -> [(a, b)]
zip' [] [] = []
zip' (a:as) (b:bs) = (a,b) : zip' as bs
zip' _ _ = error "zip': uneven lists"

allUnique :: Ord a => [a] -> Bool
allUnique = all ( (==) 1 . length) . group . sort

showList__ :: (a -> ShowS) -> [a] -> ShowS
showList__ _     []     s = "[]" ++ s
showList__ showx (x:xs) s = '[' : showx x (showl xs)
  where
    showl []     = ']' : s
    showl (y:ys) = ", " ++ showx y (showl ys)
