{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
module Main (main) where
import Unbound.Generics.LocallyNameless
import Raw
import Syntax
import NbE
import TypeCheck
import Data.Either (fromRight)

x = s2n "x"
y = s2n "y"
n = s2n "n"
n' = s2n "n'"
r = s2n "r"
r' = s2n "r'"

add :: Term
add = Lam $ bind x $ Lam $ bind y $
  NatElim (bind x Nat) (Var y) (bind (n , r) $ Suc (Var r)) (Var x)

mul :: Term
mul = Lam $ bind x $ Lam $ bind y $
  NatElim (bind x Nat) Zero (bind (n , r) $ App (App add (Var r)) (Var y)) (Var x)

ack :: Term
ack = Lam $ bind x $ NatElim
  (bind x $ Pi Nat $ bind x Nat)
  (Lam $ bind y $ Suc (Var y)) -- zero
  (bind (n, r) $ Lam $ bind y $ NatElim
    (bind x Nat)
    (App (Var r) $ Suc Zero)
    (bind (n', r') $ App (Var r) (Var r'))
    (Var y)
  ) -- succ
  (Var x)

acks :: String
acks = unlines [
    "λx. elim(_. _ -> _,",
    "{- zero -}     λx. suc(x),",
    "{- suc -} x r. λx.",
      "elim(_. _, r suc(zero), m s. r s, x),",
    "x)"
  ]

ackty :: String
ackty = "Nat -> Nat -> Nat"

rnum :: Int -> Raw
rnum 0 = RZero
rnum k = RSuc (rnum (k-1))

idterm :: Raw
idterm = RThe
  (RPi RUniverse $ bind x $ RPi (RVar x) $ bind y $ RVar x)
  (RLam $ bind x $ RLam $ bind y $ RVar y)

inferSuccess :: Raw -> (Term, Type)
inferSuccess raw = fromRight (error "Unsuccessful") $ evalTyckM do
  (tm, vty) <- infer raw
  vty' <- forceTy vty
  ty <- quoteTy vty'
  ztm <- zonk tm
  zty <- zonkTy ty
  return (ztm, zty)

main :: IO ()
main = do
  racc <- parseString acks
  -- rty <- parseString ackty
  let rterm = RApp (RApp racc (rnum 3)) (rnum 2)
  -- print $ runTyckM $ infer rterm
  putStrLn "Ready"
  let (tm, ty) = inferSuccess rterm
  print tm
  print ty
  print $ nf emptyEnv tm
  print $ nfSubst tm
