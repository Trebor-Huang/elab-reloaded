{-# OPTIONS_GHC -Wno-name-shadowing #-}
module TypeCheck (
  runTyckM, emptyContext,
  check, checkTy, infer, conv, convTy
) where
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Reader
import Unbound.Generics.LocallyNameless
import qualified Data.Map as M
import qualified Data.IntMap as IM
import Data.Coerce (coerce)

import Raw
import Syntax
import NbE
import Utils

data Context = Context {
  env :: Env,  -- environment for evaluation
  vars :: [(RVar, TyVal)]  -- types of raw variables
}

emptyContext :: Context
emptyContext = Context M.empty []

newVar :: RVar -> Var -> TyVal -> Context -> Context
newVar vraw var ty ctx = ctx {
  env = M.insert var (VVar var) (env ctx),
  vars = (vraw, ty) : vars ctx
}

bindEnv :: Var -> Val -> Context -> Context
bindEnv var val ctx = ctx {
  env = M.insert var val (env ctx)
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

freshMeta :: MonadMEnv m => String -> [a] -> m (MetaVar a)
freshMeta name env = do
  state <- get
  put state { nextMVar = nextMVar state + 1 }
  return $ MetaVar name (nextMVar state) env

freshAnonMeta :: MonadMEnv m => [a] -> m (MetaVar a)
freshAnonMeta env = do
  state <- get
  let ix = nextMVar state
  put state { nextMVar = ix + 1 }
  return $ MetaVar ("?" ++ show ix) (nextMVar state) env

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

check :: Tyck m => Raw -> TyVal -> m Term
check RHole vty = error "todo"

check (RLam f) (VPi thdom cod) = do
  (x, t) <- unbind f
  let x' = coerce x :: Var
  ty <- cod $$: \y -> [(y, VVar x')]
  t' <- local (newVar x x' thdom) $ check t ty
  return $ Lam $ bind x' t'

check (RPair s1 s2) (VSigma t1 t2) = do
  s1' <- check s1 t1
  v1 <- evalM s1'
  t2' <- t2 $$: \y -> [(y, v1)]
  s2' <- check s2 t2'
  return $ Pair s1' s2'

-- Do we need these?
check RZero VNat = return Zero
check (RSuc t) VNat = Suc <$> check t VNat

check tm ty = do
  (tm', ty') <- infer tm
  unify [Right (ty, ty')]
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
infer RHole = error "todo"

infer (RThe rty rtm) = do
  ty <- checkTy rty
  vty <- evalTyM ty
  tm <- check rtm vty
  return (The ty tm, vty)

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
      vcod <- cod $$: \y -> [(y, varg)]
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
      sty2 <- ty2 $$: \y -> [(y, varg)]
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
infer (RNatElim rmc rz rsc rarg) = do
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
  tym_s <- local (bindEnv n' (VSuc 1 (Thunk (VVar x')))) $ evalTyM tym
  ts <- local (newVar x x' VNat . newVar r r' tyr_s)
    $ check rs tym_s
  -- evaluate the type
  varg <- evalM arg
  ty <- local (bindEnv n' varg) $ evalTyM tym
  return (NatElim (bind n' tym) tz (bind (x', r') ts) arg, ty)
infer RNat = return (Quote Nat, VUniverse) -- since it's just one step we can inline it

infer RUniverse = return (Quote Universe, VUniverse) -- todo add universe constraint (i.e. don't inline this)


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
  _ -> throwError "not convertible"
convSp _ _ = throwError "not convertible"

conv :: Tyck m => Val -> Val -> m (Maybe [Equation])
-- rigid-rigid
conv (VNeutral (Right v) sp) (VNeutral (Right v') sp') =
  if v == v' then
    Just <$> convSp sp sp'
  else
    throwError "not convertible"
-- rigid-flex and flex-rigid
conv (VNeutral (Left m) sp) v =
  (\b -> if b then Just [] else Nothing) <$> solve m sp v
conv v m@(VNeutral (Left _) _) = conv m v

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
    throwError "Not convertible"

conv (VQuote ty1) (VQuote ty2) = convTy ty1 ty2
conv (VQuote ty) tm = -- Is this necessary?
  convTy ty (VEl (Thunk tm))
conv tm tm'@VQuote {} = conv tm' tm

conv _ _ = throwError "Not convertible"

convTy :: Tyck m => TyVal -> TyVal -> m (Maybe [Equation])
convTy (VMTyVar m) t =
  (\b -> if b then Just [] else Nothing) <$> solveTy m t
convTy t t'@VMTyVar {} = convTy t' t

convTy (VSigma ty c) (VSigma ty' c') = do
  (x, s) <- c $$:+ \x -> [(x, VVar x)]
  t <- c' $$: \y -> [(y, VVar x)]
  return $ Just [Right (ty, ty'), Right (s, t)]
convTy (VPi ty c) (VPi ty' c') = do
  (x, s) <- c $$:+ \x -> [(x, VVar x)]
  t <- c' $$: \y -> [(y, VVar x)]
  return $ Just [Right (ty, ty'), Right (s, t)]
convTy VNat VNat = return (Just [])
convTy VUniverse VUniverse = return (Just [])
convTy (VEl th1) (VEl th2) = do
  t1 <- force th1
  t2 <- force th2
  conv t1 t2
convTy _ _ = throwError "not convertible"

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
      sol <- quote v
      e <- asks env
      insertTermSol mid (Closure e $ bind vars sol)
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
      sol <- quoteTy v
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
attempt (Right (ty1, ty2)) = convTy ty1 ty2

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

----- Example monad to use functions ----
type TyckM = StateT MetaEnv (ReaderT Context (ExceptT String FreshM))
instance MonadMEnv TyckM
instance Tyck TyckM
runTyckM :: TyckM a -> Either String a
runTyckM m = runFreshM $
  runExceptT $
  runReaderT (evalStateT m emptyMetaEnv)
    emptyContext
