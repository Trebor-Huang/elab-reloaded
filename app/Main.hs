module Main (main) where
import Unbound.Generics.LocallyNameless
import Syntax
import TypeCheck

x = s2n "x"
y = s2n "y"
n = s2n "n"
n' = s2n "n'"
r = s2n "r"
r' = s2n "r'"

add :: Term
add = Lam $ bind x $ Lam $ bind y $
  NatElim (Var y) (bind (n , r) $ Suc (Var r)) (Var x)

mul :: Term
mul = Lam $ bind x $ Lam $ bind y $
  NatElim Zero (bind (n , r) $ App (App add (Var r)) (Var y)) (Var x)

ack :: Term
ack = Lam $ bind x $ NatElim
  (Lam $ bind y $ Suc (Var y)) -- zero
  (bind (n, r) $ Lam $ bind y $ NatElim
    (App (Var r) $ Suc Zero)
    (bind (n', r') $ App (Var r) (Var r'))
    (Var y)
  ) -- succ
  (Var x)

two :: Term
two = Suc (Suc Zero)

three :: Term
three = Suc (Suc (Suc Zero))

four :: Term
four = App (App add (Suc (Suc Zero))) (Suc (Suc Zero))

testterm :: Term
testterm = App (App ack three) two

normterm :: Term
normterm = nfSubst testterm

nbeterm :: Term
nbeterm = nf [] testterm

idterm :: Raw
idterm = RThe
  (RPi RUniverse $ bind x $ RPi (RVar x) $ bind y $ RVar x)
  (RLam $ bind x $ RLam $ bind y $ RVar y)

inferres = let Right (tm, vty) = runTyckM $ infer idterm in
  (tm, runFreshM $ quoteTy vty)

main :: IO ()
main = do
  print testterm
  print normterm
  print nbeterm
  print inferres
