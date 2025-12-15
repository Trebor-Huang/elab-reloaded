# elab-reloaded

Yet another implementation of dependent type theory.

```hs
-- Use the eliminator to define ack
define
  ⊢ ack : Nat -> Nat -> Nat
  = λy. elim(_. _, -- motive is inferred by the typechecker
    {- zero -}     λx. suc(x),
    {- suc -} n r. λx.
      elim(_. _, r suc(zero), m s. r s, x),
    y)

-- Postulate the identity type
postulate
  A : U ; x y : A ⊢ Id : U

postulate
  A : U ; x : A ⊢ refl : Id(A, x, x)

-- Proving a theorem unfolding previous definitions
define unfolding {ack}
  ⊢ thm : Id(Nat, ack 3 4, 125)
  = refl(_, _)

-- Evaluating terms
eval ack 3 4
```
