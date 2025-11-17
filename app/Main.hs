module Main (main) where
import Unbound.Generics.LocallyNameless
import Syntax

add :: Term
add = Lam $ bind x $ Lam $ bind y $
  NatElim (Var y) (bind (n , r) $ Suc (Var r)) (Var x)
  where
    x = s2n "x"
    y = s2n "y"
    n = s2n "n"
    r = s2n "r"

mul :: Term
mul = Lam $ bind x $ Lam $ bind y $
  NatElim Zero (bind (n , r) $ App (App add (Var r)) (Var y)) (Var x)
  where
    x = s2n "x"
    y = s2n "y"
    n = s2n "n"
    r = s2n "r"

ack :: Term
ack = Lam $ bind x $ NatElim
  (Lam $ bind y $ Suc (Var y)) -- zero
  (bind (n, r) $ Lam $ bind y $ NatElim
    (App (Var r) $ Suc Zero)
    (bind (n', r') $ App (Var r) (Var r'))
    (Var y)
  ) -- succ
  (Var x)
  where
    x = s2n "x"
    y = s2n "y"
    n = s2n "n"
    n' = s2n "n'"
    r = s2n "r"
    r' = s2n "r'"

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

main :: IO ()
main = do
  print testterm
  print normterm
  print nbeterm
