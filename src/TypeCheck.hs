module TypeCheck where
import Unbound.Generics.LocallyNameless

import Syntax

conv :: Val -> Val -> FreshM Bool
conv (VVar x) (VVar y) = return (x == y)

conv (VLam f) (VLam g) = do
  (x, s) <- f $$ \x -> [(x, VVar x)]
  (_, t) <- g $$ \y -> [(y, VVar x)] -- ???
  conv s t
conv (VLam f) g = do
  (x, s) <- f $$ \x -> [(x, VVar x)]
  conv s (VApp g (VVar x))
conv g (VLam f) = do
  (x, s) <- f $$ \x -> [(x, VVar x)]
  conv s (VApp g (VVar x))
conv (VApp s1 t1) (VApp s2 t2) = do
  p <- conv s1 s2
  q <- conv t1 t2
  return (p && q)

conv (VPair s1 t1) (VPair s2 t2) = do
  p <- conv s1 s2
  q <- conv t1 t2
  return (p && q)
conv (VPair s t) m = do
  p <- conv s (VFst m)
  q <- conv t (VSnd m)
  return (p && q)
conv m (VPair s t) = do
  p <- conv s (VFst m)
  q <- conv t (VSnd m)
  return (p && q)
conv (VFst s) (VFst t) = conv s t
conv (VSnd s) (VSnd t) = conv s t

conv VZero VZero = return True
conv (VSuc n t) (VSuc m s) = (&&) (n == m) <$> conv t s
conv (VRec z s n) (VRec z' s' n') = do
  (_, vz) <- z $$ \() -> []
  (_, vz') <- z' $$ \() -> []
  p <- conv vz vz'
  ((m, k), vs) <- s $$ \(m, k) -> [(m, VVar m), (k, VVar k)]
  (_, vs') <- s' $$ \(m', k') -> [(m', VVar m), (k', VVar k)]
  q <- conv vs vs'
  r <- conv n n'
  return (p && q && r)

-- vquote
conv (VQuote ty1) (VQuote ty2) = convTy ty1 ty2
conv (VQuote ty) tm = convTy ty (VEl tm) -- Is this necessary?
conv tm (VQuote ty) = convTy ty (VEl tm)

conv _ _ = return False

convTy :: TyVal -> TyVal -> FreshM Bool
convTy (VSigma ty c) (VSigma ty' c') = do
  p <- convTy ty ty'
  (x, s) <- c $$- \x -> [(x, VVar x)]
  (_, t) <- c' $$- \y -> [(y, VVar x)]
  q <- convTy s t
  return (p && q)
convTy (VPi ty c) (VPi ty' c') = do
  p <- convTy ty ty'
  (x, s) <- c $$- \x -> [(x, VVar x)]
  (_, t) <- c' $$- \y -> [(y, VVar x)]
  q <- convTy s t
  return (p && q)
convTy VNat VNat = return True
convTy VUniverse VUniverse = return True
convTy (VEl t1) (VEl t2) = conv t1 t2
convTy _ _ = return False
