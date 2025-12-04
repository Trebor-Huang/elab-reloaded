{-# OPTIONS_GHC -Wno-missing-export-lists #-}
module Utils where
import Data.List
import qualified Data.Graph as G
import qualified Data.Array as A

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

hasCycle :: G.Graph -> Bool
hasCycle g = any (uncurry (==)) (G.edges g) || any (\c -> length c > 1) (G.scc g)

insertNode :: G.Graph -> Int -> [Int] -> G.Graph
insertNode g i k = g A.// [(i, k)]

newNode :: G.Graph -> (Int, G.Graph)
newNode g = let (l, r) = A.bounds g in
  (r+1, A.array (l,r+1) ((r+1,[]):[(i, g A.! i) | i <- A.range (l,r)]))
