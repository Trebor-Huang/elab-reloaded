module TypeCheck where
import Control.Monad
import Control.Monad.Except
import Control.Monad.Reader
import Unbound.Generics.LocallyNameless
import Data.Coerce (coerce)

import Syntax
import Raw

data Context = Context {
  env :: Env,
  vars :: [(RVar, TyVal)]
}

newVar :: RVar -> Var -> TyVal -> Context -> Context
newVar vraw var ty ctx = ctx {
  env = (var, VVar var) : env ctx,
  vars = (vraw, ty) : vars ctx
}

bindEnv :: Var -> Val -> Context -> Context
bindEnv var val ctx = ctx {
  env = (var, val) : env ctx
}

class (MonadError String m, MonadReader Context m, Fresh m) => Tyck m

evalM :: (MonadReader Context m, Fresh m) => Term -> m Val
evalM tm = do
  e <- asks env
  eval e tm

evalTyM :: (MonadReader Context m, Fresh m) => Type -> m TyVal
evalTyM ty = do
  e <- asks env
  evalTy e ty

type TyckM = ReaderT Context (ExceptT String FreshM)
instance Tyck TyckM
runTyckM :: TyckM a -> Either String a
runTyckM m = runFreshM $ runExceptT $ runReaderT m
  Context {
    env = [],
    vars = []
  }

check :: Tyck m => Raw -> TyVal -> m Term
check (RLam f) (VPi dom cod) = do
  (x, t) <- unbind f
  let x' = coerce x :: Var
  (_, ty) <- cod $$- \y -> [(y, VVar x')]
  t' <- local (newVar x x' dom) $ check t ty
  return $ Lam $ bind x' t'

check (RPair s1 s2) (VSigma t1 t2) = do
  s1' <- check s1 t1
  v1 <- evalM s1'
  (_, t2') <- t2 $$- \y -> [(y, v1)]
  s2' <- check s2 t2'
  return $ Pair s1' s2'

-- Do we need these?
check RZero VNat = return Zero
check (RSuc t) VNat = Suc <$> check t VNat

check tm ty = do
  (tm', ty') <- infer tm
  p <- convTy ty ty'
  unless p do
    throwError "Expected ..."
  return tm'

checkTy :: Tyck m => Raw -> m Type  -- this should give a level too?
checkTy (RPi rdom rc) = do
  dom <- checkTy rdom
  vdom <- evalTyM dom
  (x, rcod) <- unbind rc
  let x' = coerce x :: Var
  cod <- local (newVar x x' vdom) $ checkTy rcod
  return (Pi dom (bind x' cod)) -- ?
checkTy (RSigma rty1 rc) = do
  ty1 <- checkTy rty1
  vty1 <- evalTyM ty1
  (x, rty2) <- unbind rc
  let x' = coerce x :: Var
  ty2 <- local (newVar x x' vty1) $ checkTy rty2
  return (Sigma ty1 (bind x' ty2))
checkTy RNat = return Nat
checkTy RUniverse = return Universe
checkTy rtm = do
  tm' <- check rtm VUniverse
  return (El tm')

infer :: Tyck m => Raw -> m (Term, TyVal)
infer (RThe rty rtm) = do
  ty <- checkTy rty
  vty <- evalTyM ty
  tm <- check rtm vty
  return (tm, vty)

infer (RVar x) = do
  vs <- asks vars
  case lookup x vs of
    Just y -> return (Var (coerce x), y)
    Nothing -> throwError $ "Variable out of scope: " ++ show x

infer (RApp rfun rarg) = do
  (fun, ty) <- infer rfun
  case ty of
    VPi dom cod -> do
      arg <- check rarg dom
      varg <- evalM arg
      (_, vcod) <- cod $$- \y -> [(y, varg)]
      return (App fun arg, vcod)
    _ -> throwError $ "Expected Pi type: " ++ show ty
infer (RLam _) = throwError "Unable to infer type of lambda"
infer rty@RPi {} = do
  ty <- checkTy rty
  return (Quote ty, VUniverse)

infer (RFst r) = do
  (t, ty) <- infer r
  case ty of
    VSigma ty1 _ -> return (Fst t, ty1)
    _ -> throwError "Expected Sigma type"
infer (RSnd r) = do
  (t, ty) <- infer r
  case ty of
    VSigma _ ty2 -> do
      varg <- evalM (Fst t)
      (_, sty2) <- ty2 $$- \y -> [(y, varg)]
      return (Snd t, sty2)
    _ -> throwError "Expected Sigma type"
infer (RPair _ _) = throwError "Unable to infer type of pairs"
infer rty@RSigma {} = do
  ty <- checkTy rty
  return (Quote ty, VUniverse)

infer RZero = return (Zero, VNat)
infer (RSuc r) = do
  t <- check r VNat
  return (Suc t, VNat)
infer (RElim rmc rz rsc rarg) = do
  -- check argument
  arg <- check rarg VNat
  -- check motive
  (n, rm) <- unbind rmc
  let n' = coerce n :: Var
  tym <- local (newVar n n' VNat) $ checkTy rm
  -- check zero argument
  tym_z <- local (bindEnv n' VZero) $ evalTyM tym
  tz <- check rz tym_z
  -- check suc argument
  ((x, r), rs) <- unbind rsc
  let x' = coerce x :: Var
  let r' = coerce r :: Var
  tyr_s <- local (bindEnv n' (VVar x')) $ evalTyM tym
  tym_s <- local (bindEnv n' (VSuc 1 (VVar x'))) $ evalTyM tym
  ts <- local (newVar x x' VNat . newVar r r' tyr_s) $ check rs tym_s
  -- evaluate the type
  varg <- evalM arg
  ty <- local (bindEnv n' varg) $ evalTyM tym
  return (NatElim (bind n' tym) tz (bind (x', r') ts) arg, ty)
infer RNat = return (Quote Nat, VUniverse) -- since it's just one step we can inline it

infer RUniverse = return (Quote Universe, VUniverse) -- todo add universe constraint (i.e. don't inline this)

conv :: (Fresh m) => Val -> Val -> m Bool
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
conv (VRec _ z s n) (VRec _ z' s' n') = do
  -- since we are assuming they have the same type,
  -- conversion should not depend on the motive
  (_, vz) <- z $$ \() -> []
  (_, vz') <- z' $$ \() -> []
  p <- conv vz vz'
  ((m, k), vs) <- s $$ \(m, k) -> [(m, VVar m), (k, VVar k)]
  (_, vs') <- s' $$ \(m', k') -> [(m', VVar m), (k', VVar k)]
  q <- conv vs vs'
  r <- conv n n'
  return (p && q && r)

conv (VQuote ty1) (VQuote ty2) = convTy ty1 ty2
conv (VQuote ty) tm = convTy ty (VEl tm) -- Is this necessary?
conv tm (VQuote ty) = convTy ty (VEl tm)

conv _ _ = return False

convTy :: Fresh m => TyVal -> TyVal -> m Bool
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
