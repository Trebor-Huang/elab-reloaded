{-# OPTIONS_GHC -Wno-name-shadowing #-}
module TypeCheck (
  TyckM, runTyckM, evalTyckM, emptyContext,
  check, checkTy, infer, conv, convTy,
  zonk, zonkTy
) where
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Reader
import Unbound.Generics.LocallyNameless hiding (close)
import qualified Data.IntMap as IM
import Data.Coerce (coerce)

import Raw
import Syntax
import NbE
import Utils

data Context = Context {
  env :: !Env,  -- environment for evaluation
  vars :: [(RVar, Thunk TyVal)]  -- types of raw variables
} deriving Show

emptyContext :: Context
emptyContext = Context emptyEnv []

newVar :: RVar -> Var -> Thunk TyVal -> Context -> Context
newVar vraw var ty ctx = ctx {
  env = bindLocal [(var, VVar var)] (env ctx),
  vars = (vraw, ty) : vars ctx
}

bindEnv :: Var -> Val -> Context -> Context
bindEnv var val ctx = ctx {
  env = bindLocal [(var, val)] (env ctx)
}

class (MonadError String m, MonadReader Context m, MonadMEnv m) => Tyck m

-- Prepare some primitive operations
evalM :: (MonadReader Context m, MonadMEnv m) => Term -> m Val
evalM tm = do
  e <- asks env
  eval e tm

evalTyM :: (MonadReader Context m, MonadMEnv m) => Type -> m TyVal
evalTyM ty = do
  e <- asks env
  evalTy e ty

-- freshMeta :: MonadMEnv m => String -> [a] -> m (MetaVar a)
-- freshMeta name env = do
--   state <- get
--   put state { nextMVar = nextMVar state + 1 }
--   return $ MetaVar name (nextMVar state) env

freshAnonMeta :: Tyck m => m (MetaVar Term)
freshAnonMeta = do
  vs <- asks vars
  state <- get
  let ix = nextMVar state
  put state { nextMVar = ix + 1 }
  return $ MetaVar
    ("?" ++ show ix) (nextMVar state) (map (Var . coerce . fst) vs)

insertTermSol :: MonadMEnv m => Int -> Closure [Var] Term -> m ()
insertTermSol i s = do
  -- todo debug check if metavariables are repeated
  modify \menv -> menv {
    termSol = IM.insert i s (termSol menv)
  }

insertTypeSol :: MonadMEnv m => Int -> Closure [Var] Type -> m ()
insertTypeSol i s = do
  modify \menv -> menv {
    typeSol = IM.insert i s (typeSol menv)
  }

close :: (Tyck m, Alpha a) => a -> Thunk Val -> m (Closure a Term)
close a th = do
  t <- force th
  tm <- reify t
  e <- asks env
  return (Closure e (bind a tm))

closeTy :: (Tyck m, Alpha a) => a -> Thunk TyVal -> m (Closure a Type)
closeTy a th = do
  t <- forceTy th
  ty <- reifyTy t
  e <- asks env
  return (Closure e (bind a ty))

check :: Tyck m => Raw -> TyVal -> m Term
check RHole _ = -- todo typed holes
  MVar <$> freshAnonMeta

check (RLam f) (VPi thdom cod) = do
  (x, t) <- unbind f
  let x' = coerce x :: Var
  ty <- cod $$: \y -> [(y, VVar x')]
  t' <- local (newVar x x' thdom) $ check t ty
  return $ Lam $ bind x' t'

check (RPair s1 s2) (VSigma th1 t2) = do
  t1 <- forceTy th1
  s1' <- check s1 t1
  v1 <- evalM s1'
  t2' <- t2 $$: \y -> [(y, v1)]
  s2' <- check s2 t2'
  return $ Pair s1' s2'

-- Do we need these?
check RZero VNat = return Zero
check (RSuc t) VNat = Suc <$> check t VNat

check tm ty = do
  (tm', thty') <- infer tm
  unify [Right (Thunk ty, thty')]
  return tm'

checkTy :: Tyck m => Raw -> m Type  -- this should give a level too?
checkTy (RPi rdom rc) = do
  dom <- checkTy rdom
  vdom <- evalTyM dom
  (x, rcod) <- unbind rc
  let x' = coerce x :: Var
  cod <- local (newVar x x' (Thunk vdom)) $ checkTy rcod
  return (Pi dom (bind x' cod)) -- ?
checkTy (RSigma rty1 rc) = do
  ty1 <- checkTy rty1
  vty1 <- evalTyM ty1
  (x, rty2) <- unbind rc
  let x' = coerce x :: Var
  ty2 <- local (newVar x x' (Thunk vty1)) $ checkTy rty2
  return (Sigma ty1 (bind x' ty2))
checkTy RNat = return Nat
checkTy RUniverse = return Universe
checkTy RHole = MTyVar <$> freshAnonMeta
checkTy rtm = do
  tm' <- check rtm VUniverse
  return (El tm')

infer :: Tyck m => Raw -> m (Term, Thunk TyVal)
infer RHole = do -- todo typed holes
  m <- freshAnonMeta
  mty <- freshAnonMeta
  vty <- evalTyM (MTyVar mty)
  return (MVar m, Thunk vty)

infer (RThe rty rtm) = do
  ty <- checkTy rty
  vty <- evalTyM ty
  tm <- check rtm vty
  return (The ty tm, Thunk vty)

infer (RVar x) = do
  vs <- asks vars
  case lookup x vs of
    Just y -> return (Var (coerce x), y)
    Nothing -> throwError $ "Variable out of scope: " ++ show x

infer (RApp rfun rarg) = do
  (fun, thty) <- infer rfun
  ty <- forceTy thty
  (dom, cod) <- case ty of
    VPi thdom cod -> do
      dom <- forceTy thdom
      return (dom, cod)
    _ -> expectPiSigma True ty
  arg <- check rarg dom
  varg <- evalM arg
  vcod <- cod $$: \y -> [(y, varg)]
  return (App fun arg, Thunk vcod)
infer (RLam f) = do
  mdom <- freshAnonMeta
  vdom <- Thunk <$> evalTyM (MTyVar mdom)
  (x, rt) <- unbind f
  let x' = coerce x :: Var
  (t, vcod) <- local (newVar x x' vdom) $ infer rt
  cod <- closeTy x' vcod
  return (Lam $ bind x' t, Thunk $ VPi vdom cod)
infer rty@RPi {} = do
  ty <- checkTy rty
  return (Quote ty, Thunk VUniverse)

infer (RFst r) = do
  (t, th) <- infer r
  ty <- forceTy th
  case ty of
    VSigma ty1 _ -> return (Fst t, ty1)
    _ -> do
      (ty1, _) <- expectPiSigma False ty
      return (Fst t, Thunk ty1)
infer (RSnd r) = do
  (t, th) <- infer r
  ty <- forceTy th
  ty2 <- case ty of
    VSigma _ ty2 -> return ty2
    _ -> snd <$> expectPiSigma False ty
  varg <- evalM (Fst t)
  sty2 <- ty2 $$: \y -> [(y, varg)]
  return (Snd t, Thunk sty2)
infer (RPair t1 t2) = do
  mt1 <- freshAnonMeta
  ty1 <- evalTyM (MTyVar mt1)
  z <- fresh (s2n "z")
  bt2 <- local (bindEnv z (VVar z)) do
    mt2 <- freshAnonMeta
    evalTyM (MTyVar mt2)
  ty2 <- closeTy z (Thunk bt2)
  let ty = VSigma (Thunk ty1) ty2
  t <- check (RPair t1 t2) ty
  return (t, Thunk ty)
infer rty@RSigma {} = do
  ty <- checkTy rty
  return (Quote ty, Thunk VUniverse)

infer RZero = return (Zero, Thunk VNat)
infer (RSuc r) = do
  t <- check r VNat
  return (Suc t, Thunk VNat)
infer (RNatElim rmc rz rsc rarg) = do
  -- check argument
  arg <- check rarg VNat
  -- check motive
  (n, rm) <- unbind rmc
  let n' = coerce n :: Var
  tym <- local (newVar n n' (Thunk VNat)) $ checkTy rm
  -- check zero argument
  tym_z <- local (bindEnv n' VZero) $ evalTyM tym
  tz <- check rz tym_z
  -- check suc argument
  ((x, r), rs) <- unbind rsc
  let x' = coerce x :: Var
  let r' = coerce r :: Var
  tyr_s <- local (bindEnv n' (VVar x')) $ evalTyM tym
  tym_s <- local (bindEnv n' (VSuc 1 (Thunk (VVar x')))) $ evalTyM tym
  ts <- local (newVar x x' (Thunk VNat) . newVar r r' (Thunk tyr_s))
    $ check rs tym_s
  -- evaluate the type
  varg <- evalM arg
  ty <- local (bindEnv n' varg) $ evalTyM tym
  return (NatElim (bind n' tym) tz (bind (x', r') ts) arg, Thunk ty)
infer RNat = return (Quote Nat, Thunk VUniverse)
  -- since it's just one step we can inline it

infer RUniverse = return (Quote Universe, Thunk VUniverse)
  -- todo add universe constraint (i.e. don't inline this)

expectPiSigma :: Tyck m => Bool -> TyVal -> m (TyVal, Closure Var Type)
expectPiSigma b ty = do
  mdom <- freshAnonMeta
  dom <- evalTyM (MTyVar mdom)
  z <- fresh (s2n "z")
  bcod <- local (bindEnv z (VVar z)) do
    mcod <- freshAnonMeta
    evalTyM (MTyVar mcod)
  cod <- closeTy z (Thunk bcod)
  unify [Right (Thunk ty,
    Thunk $ (if b then VPi else VSigma) (Thunk dom) cod)]
  return (dom, cod)

----- Unification algorithm -----
-- the `conv` family of functions output Nothing when it should be postponed,
-- error when it is definitely not true, and outputs a list of equations otherwise

convSp :: Tyck m => [Spine] -> [Spine] -> m [Equation]
convSp [] [] = return []
convSp (s:sp) (s':sp') = (++) <$> convSp sp sp' <*> case (s, s') of
  (VApp th, VApp th') -> return [Left (th, th')]
  (VFst, VFst) -> return []
  (VSnd, VSnd) -> return []
  (VNatElim _ z s, VNatElim _ z' s') -> do
    -- since we are assuming they have the same type,
    -- conversion should not depend on the motive
    vz <- z $$ \() -> []
    vz' <- z' $$ \() -> []

    ((m, k), vs) <- s $$+ \(m, k) -> [(m, VVar m), (k, VVar k)]
    vs' <- s' $$ \(m', k') -> [(m', VVar m), (k', VVar k)]

    return [Left (Thunk vz, Thunk vz'), Left (Thunk vs, Thunk vs')]
  p -> throwError $ "Not convertible: " ++ show p
convSp p q = throwError $ "Not convertible: " ++ show p ++ show q

conv :: Tyck m => Val -> Val -> m (Maybe [Equation])
-- rigid-rigid
conv (VRigid v sp) (VRigid v' sp') =
  if v == v' then
    Just <$> convSp sp sp'
  else
    throwError $ "Not convertible: " ++ show v ++ " /= " ++ show v'
-- rigid-flex and flex-rigid
conv (VFlex m sp) v =
  (\b -> if b then Just [] else Nothing) <$> solve m sp v
conv v m@VFlex {} = conv m v

conv (VLam f) (VLam g) = do
  -- We can use a fresh variable, but that loses the name information
  -- so we use this slighly cursed leaking implementation
  (x, s) <- f $$+ \x -> [(x, VVar x)]
  t <- g $$ \y -> [(y, VVar x)]
  s' <- force (Thunk s)
  t' <- force (Thunk t)
  conv s' t'
conv (VLam f) g = do
  (x, s) <- f $$+ \x -> [(x, VVar x)]
  t <- vApp g (VVar x)
  s' <- force (Thunk s)
  t' <- force (Thunk t)
  conv s' t'
conv g f@VLam {} = conv f g

conv (VPair ths1 tht1) (VPair ths2 tht2) =
  return $ Just [Left (ths1, ths2), Left (tht1, tht2)]
conv (VPair ths tht) m =
  return $ Just [Left (ths, Thunk (vFst m)), Left (tht, Thunk (vSnd m))]
conv m n@VPair {} = conv n m

conv VZero VZero = return (Just [])
conv (VSuc n th) (VSuc m th') =
  if n == m then do
    t <- force th
    t' <- force th'
    conv t t'
  else
    throwError $ show n ++ " /= " ++ show m

conv (VQuote th1) (VQuote th2) = do
  ty1 <- forceTy th1
  ty2 <- forceTy th2
  convTy ty1 ty2
conv (VQuote th) tm = do -- Is this necessary?
  ty <- forceTy th
  convTy ty (VEl (Thunk tm))
conv tm tm'@VQuote {} = conv tm' tm

conv p q = throwError $ "Not convertible: " ++ show p ++ " /= " ++ show q

convTy :: Tyck m => TyVal -> TyVal -> m (Maybe [Equation])
convTy (VMTyVar m) t =
  (\b -> if b then Just [] else Nothing) <$> solveTy m t
convTy t t'@VMTyVar {} = convTy t' t

convTy (VSigma ty c) (VSigma ty' c') = do
  (x, s) <- c $$:+ \x -> [(x, VVar x)]
  t <- c' $$: \y -> [(y, VVar x)]
  return $ Just [Right (ty, ty'), Right (Thunk s, Thunk t)]
convTy (VPi ty c) (VPi ty' c') -- small hack to reduce repeat
  = convTy (VSigma ty c) (VSigma ty' c')
convTy VNat VNat = return (Just [])
convTy VUniverse VUniverse = return (Just [])
convTy (VEl th1) (VEl th2) = do
  t1 <- force th1
  t2 <- force th2
  conv t1 t2
convTy (VEl th1) ty = do
  t1 <- force th1
  conv t1 (VQuote (Thunk ty))
convTy ty ty'@VEl {} = convTy ty' ty
convTy p q = throwError $ "Not convertible: " ++ show p ++ " /= " ++ show q

-- Searches if the substitution and the spine constitutes
-- a linear set of variables, and if so adds the solution
solve :: Tyck m => MetaVar Val -> [Spine] -> Val -> m Bool
solve (MetaVar _ mid subs) sp v = do
  vsp <- mapM spine sp
  let vars' = sequence (map toVar subs ++ map (toVar =<<) vsp)
  case vars' of
    Nothing -> return False
    Just vars -> if allUnique vars then do
      -- todo occurs check
      sol <- close vars (Thunk v)
      insertTermSol mid sol
      return True
    else
      return False
  where
    spine :: MonadMEnv m => Spine -> m (Maybe Val)
    spine (VApp s) = Just <$> force s
    spine _ = return Nothing

solveTy :: Tyck m => MetaVar Val -> TyVal -> m Bool
solveTy (MetaVar _ mid subs) v = do
  let vars' = mapM toVar subs
  case vars' of
    Nothing -> return False
    Just vars -> if allUnique vars then do
      -- todo occurs check
      sol <- reifyTy v
      e <- asks env
      insertTypeSol mid (Closure e $ bind vars sol)
      return True
    else
      return False


-- Attempt to solve the equation, which either postpones it or
-- splits into zero or more smaller equations, without recursively solving
-- (unless it's straightforward to do so)
attempt :: Tyck m => Equation -> m (Maybe [Equation])
attempt (Left (th1, th2)) = do
  t1 <- force th1
  t2 <- force th2
  conv t1 t2
attempt (Right (th1, th2)) = do
  t1 <- forceTy th1
  t2 <- forceTy th2
  convTy t1 t2

-- The postponing logic
unify :: Tyck m => [Equation] -> m ()
unify [] = return ()
unify (eq:eqs) = do
  result <- attempt eq
  case result of
    Just eqs' -> do
      menv <- get
      put menv {
        equations = []  -- todo filter only the relevant ones
      }
      unify (eqs' ++ eqs ++ equations menv)
    Nothing -> do
      -- ? use snoc list
      modify \menv -> menv { equations = eq : equations menv }
      unify eqs

-- Tools to substitute in the solutions and display the final results
zonkMeta :: Tyck m => Closure [Var] Term -> [Term] -> m Term
zonkMeta sol subs = do
  vsubs <- mapM evalM subs
  val <- sol $$ (`zip'` vsubs)
  tm <- reify val
  zonk tm

zonkMetaTy :: Tyck m => Closure [Var] Type -> [Term] -> m Type
zonkMetaTy sol subs = do
  vsubs <- mapM evalM subs
  val <- sol $$: (`zip'` vsubs)
  reifyTy val

zonk :: Tyck m => Term -> m Term
zonk m@(MVar (MetaVar _ mid subs)) = do
  sol <- gets (IM.lookup mid . termSol)
  case sol of
    Just s -> zonkMeta s subs
    Nothing -> return m
zonk (Var v) = return $ Var v
zonk (Lam f) = do
  (x, f') <- unbind f
  zf <- local (bindEnv x (VVar x)) $ zonk f'
  return $ Lam $ bind x zf
zonk (App s t) = App <$> zonk s <*> zonk t
zonk (Pair s t) = Pair <$> zonk s <*> zonk t
zonk (Fst s) = Fst <$> zonk s
zonk (Snd s) = Snd <$> zonk s
zonk Zero = return Zero
zonk (Suc s) = Suc <$> zonk s
zonk (NatElim m z s c) = do
  (x, m') <- unbind m
  zm <- local (bindEnv x (VVar x)) $ zonkTy m'
  zz <- zonk z
  ((n, r), s') <- unbind s
  zs <- local (bindEnv n (VVar n) . bindEnv r (VVar r)) $ zonk s'
  zc <- zonk c
  return $ NatElim (bind x zm) zz (bind (n, r) zs) zc
zonk (Quote ty) = Quote <$> zonkTy ty
zonk (The ty tm) = The <$> zonkTy ty <*> zonk tm

zonkTy :: Tyck m => Type -> m Type
zonkTy m@(MTyVar (MetaVar _ mid subs)) = do
  sol <- gets (IM.lookup mid . typeSol)
  case sol of
    Just s -> zonkMetaTy s subs
    Nothing -> return m
zonkTy (Sigma ty f) = do
  zty <- zonkTy ty
  (x, f') <- unbind f
  zf <- local (bindEnv x (VVar x)) $ zonkTy f'
  return $ Sigma zty $ bind x zf
zonkTy (Pi ty f) = do
  zty <- zonkTy ty
  (x, f') <- unbind f
  zf <- local (bindEnv x (VVar x)) $ zonkTy f'
  return $ Pi zty $ bind x zf
zonkTy Nat = return Nat
zonkTy Universe = return Universe
zonkTy (El tm) = El <$> zonk tm

----- Example monad to use functions ----
type TyckM = StateT MetaEnv (ReaderT Context (ExceptT String FreshM))
instance MonadMEnv TyckM
instance Tyck TyckM
runTyckM :: TyckM a -> Either String (a, MetaEnv)
runTyckM m = runFreshM $
  runExceptT $
  runReaderT (runStateT m emptyMetaEnv)
    emptyContext

evalTyckM :: TyckM a -> Either String a
evalTyckM m = runFreshM $
  runExceptT $
  runReaderT (evalStateT m emptyMetaEnv)
    emptyContext
