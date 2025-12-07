{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
module Main (main) where
import Raw
import TypeCheck

main :: IO ()
main = do
  src <- readFile "./test/test-flip.tt"
  putStrLn "Read file."
  (decl, expr) <- parseString src
  putStrLn "Parsed file."
  case execTyckM $ processFile decl expr of
    Left err -> putStrLn err
    Right ((ty, tm, ntm), memv) -> do
      putStr "Meta Env: "
      print memv
      putStrLn ""
      putStr "Type: "
      print ty
      putStr "Term: "
      print tm
      putStr "Normalized: "
      print ntm
