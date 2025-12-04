{-# OPTIONS_GHC -Wno-missing-signatures #-}
module NbE (
  GlobalEntry(..), Env(..), emptyEnv, CofEnv(..), emptyCofEnv,
  bindLocal, bindGlobal,
  Equation, MetaEnv(..), emptyMetaEnv,
  Closure, closeB, Spine(..),
  Val(.. {- exclude VNeutral -}, VVar), toVar,
  vApp, vFst, vSnd, -- vSuc, vNatElim, vSpine, vCon,
  TyVal(..), Thunk (Thunk), force, forceTy,
  eval, evalTy, ($$), ($$:), ($$+), ($$:+),
  reify, reifyTy, reflectSpine, nf,
  MonadMEnv, MetaEnvM, runMetaEnvM
) where

import qualified Data.IntMap as IM
import qualified Data.Map as M
import Control.Monad.State
import GHC.Generics
import Unbound.Generics.LocallyNameless

import Syntax
import Cofibration
import Utils
import Control.Monad ((<=<))
import Control.Lens (anyOf)

-- todo check if all the monad assumptions are required
--- Environment
-- TODO include cof assumptions, and definitions can destabilize
data GlobalEntry
  = Definition Type Term
  | Postulate Type
  | Hypothetic Type (Bind Var GlobalEntry)
  -- Global definitions can't be closures
  | Locked Cof GlobalEntry
  deriving (Generic, Show)
instance Alpha GlobalEntry

data Env = Env {
  localEnv :: M.Map Var Val,
  globalEnv :: M.Map String GlobalEntry
} deriving Show

emptyEnv :: Env
emptyEnv = Env M.empty M.empty

lookupLocal :: Env -> Var -> Val
lookupLocal e v = case M.lookup v (localEnv e) of
  Just val -> val
  Nothing -> error "lookupLocal: impossible"

bindLocal :: [(Var, Val)] -> Env -> Env
bindLocal bds e = e {
  localEnv = M.union (M.fromList bds) $ localEnv e
}

lookupGlobal :: Env -> String -> GlobalEntry
lookupGlobal e v = case M.lookup v (globalEnv e) of
  Just val -> val
  Nothing -> error $ "lookupGlobal: unknown constant " ++ v

bindGlobal :: String -> GlobalEntry -> Env -> Env
bindGlobal n v e = e {
  globalEnv = M.insert n v $ globalEnv e
}

data CofEnv = CofEnv {
  localTokens :: Cof,
  globalTokens :: World
} deriving Show

emptyCofEnv :: CofEnv
emptyCofEnv = CofEnv mempty emptyWorld

bindToken :: Cof -> CofEnv -> CofEnv
bindToken p cofEnv = cofEnv {
  localTokens = localTokens cofEnv <> p
}

-- cofIsTrue :: CofEnv -> Cof -> Bool
-- cofIsTrue e = implies (globalTokens e) (localTokens e)

cofSelect :: CofEnv -> Cases a -> Maybe a
cofSelect e = select (globalTokens e) (localTokens e)

--- Metavariable environment
type Equation = Either (Thunk Val, Thunk Val) (Thunk TyVal, Thunk TyVal)

data MetaEnv = MetaEnv {
  nextMVar :: Int,
  termSol :: IM.IntMap (Closure [Var] Term),
  typeSol :: IM.IntMap (Closure [Var] Type),
  equations :: [Equation]  -- postponed equations
} deriving Show

emptyMetaEnv :: MetaEnv
emptyMetaEnv = MetaEnv 0 IM.empty IM.empty []

class (Fresh m, MonadState MetaEnv m) => MonadMEnv m

-- A closure stores an environment.
-- TODO hide the constructor and implement pruning
data Closure r t = Closure Env CofEnv (Bind r t)
instance (Show r, Show t) => Show (Closure r t) where
  show (Closure _ _ b) = show b
closeB :: (Alpha r, Alpha t) => Env -> CofEnv -> Bind r t -> Closure r t
closeB env cofEnv b = Closure (env {
  localEnv = M.filterWithKey (\k _ -> anyOf fv (== k) b) (localEnv env)
}) cofEnv b

-- Some metavariables may have been solved; remind us to look up the newest one.
-- Principle: if we immediately want to case split on the variable, then
-- make the input type a Thunk. Generally always make the output Thunk.
newtype Thunk a = Thunk { unthunk :: a }
instance Show a => Show (Thunk a) where
  showsPrec i (Thunk a) = showsPrec i a
-- use unthunk to disregard this, and use force to make the update

-- Eliminators
data Spine
  = VApp {- -} (Thunk Val)
  | VFst {- -} | VSnd {- -}
  | VNatElim (Closure Var Type) (Closure () Term) (Closure (Var, Var) Term) {- -}
  | VUnlock {- -} Cof
  | VOutCof Cof (Thunk Val) {- -}
  deriving Show
-- There should be a TySpine in principle but it's just VEl by itself...

data Val
  -- todo these three leads to a lot of repeated clauses
  = VFlex (MetaVar (Thunk Val)) [Spine] !(Cases (Thunk Val))
  | VRigid Var [Spine] {- neutral stablizer -} !(Cases (Thunk Val))
  | VCon (Const (Thunk Val)) [Spine] {- unfolding result -} !(Cases (Thunk Val))

  -- Constructors
  | VLam (Closure Var Term)
  | VPair (Thunk Val) (Thunk Val)
  | VZero | VSuc Int (Thunk Val)
  | VLock Cof (Closure () Term)
  | VInCof Cof (Thunk Val)
  | VQuote (Thunk TyVal)
  deriving Show

data TyVal
  = VMTyVar (MetaVar (Thunk Val)) !(Cases (Thunk TyVal))
  | VEl Val
    -- this should be VTyNeutral,
    -- but the thunk inside can only be neutral terms to be type correct
    -- except VQuote which we deal with manually
    -- It doesn't modify the destabilization either so
  -- Type constructors
  | VSigma (Thunk TyVal) (Closure Var Type)
  | VPi (Thunk TyVal) (Closure Var Type)
  | VNat
  | VPushforward Cof (Closure () Type)
  | VExt (Thunk TyVal) Cof (Closure () Term)
  -- Ext
  | VUniverse
  deriving Show

-- Patterns for constructing values.
-- These should not look under metas, so they use "unthunk"
pattern VVar :: Var -> Val
pattern VVar x = VRigid x [] EmptyCases

toVar :: Val -> Maybe Var
toVar (VVar v) = Just v
toVar _ = Nothing

vMeta :: MonadMEnv m => [Spine] -> Cases (Thunk Val) -> MetaVar (Thunk Val) -> m Val
vMeta sp st m@(MetaVar _ mid subs) = do
  sol <- gets (IM.lookup mid . termSol)
  case sol of
    Just b -> do
      b' <- b $$ (`zip'` map unthunk subs)
      vsol <- vSpine sp b'
      let unfoldCase = SingleCase mempty (Thunk vsol)
        -- todo add back unfolding meta
      return $ VFlex m sp $ unfoldCase <> st
    Nothing -> return $ VFlex m sp EmptyCases

vMetaTy :: MonadMEnv m => Cases (Thunk TyVal) -> MetaVar (Thunk Val) -> m TyVal
vMetaTy st m@(MetaVar _ mid subs) = do
  sol <- gets (IM.lookup mid . typeSol)
  case sol of
    Just b -> do
      vsol <- b $$: (`zip'` map unthunk subs)
      let unfoldCase = SingleCase mempty (Thunk vsol)
      return $ VMTyVar m $ unfoldCase <> st
    Nothing -> return $ VMTyVar m st

-- TODO does this need stabilization info?
vCon :: MonadMEnv m => Env -> CofEnv -> [Spine] -> Const (Thunk Val) -> m Val
vCon env cofEnv sp c@(Const name subs) = do
  -- this does not use emptyEnv and emptyCofEnv, because
  -- the innermost evaluation needs this for the substitution to make sense
  result <- vCon' env cofEnv (lookupGlobal env name) (map unthunk subs)
  VCon c sp <$> mapM (\x -> Thunk <$> vSpine sp (unthunk x)) result

vCon' :: MonadMEnv m =>
  Env -> CofEnv -> GlobalEntry -> [Val] -> m (Cases (Thunk Val))
vCon' env cofEnv (Hypothetic _ bg) (v:subs) = do
  (x, g) <- unbind bg
  vCon' (bindLocal [(x, v)] env) cofEnv g subs
vCon' env cofEnv (Locked p g) subs
  -- Huh, the substitution doesn't seem to need these tokens
  = vCon' env (bindToken p cofEnv) g subs
vCon' env cofEnv (Definition _ tm) [] = do
  v <- eval env cofEnv tm
  return $ SingleCase mempty (Thunk v) -- do I use the cofEnv?
vCon' _ _ (Postulate _) [] = return EmptyCases
vCon' _ _ _ _ = error "Impossible"

vSpine :: MonadMEnv m => [Spine] -> Val -> m Val
vSpine [] v = return v
vSpine (c:sp) v0 = do
  v <- vSpine sp v0
  case c of
    VApp th -> vApp v (unthunk th)
    VFst -> return $ vFst v
    VSnd -> return $ vSnd v
    VNatElim m z s -> vNatElim m z s v
    VUnlock p -> vUnlock v p
    VOutCof p u -> return $ vOutCof p u v

vApp :: MonadMEnv m => Val -> Val -> m Val
vApp fun arg = case fun of
  VLam t' -> t' $$ \x -> [(x, arg)]
  VFlex mv sp st ->
    VFlex mv (VApp (Thunk arg) : sp) <$> mapM (thApp arg) st
  VRigid v sp st ->
    VRigid v (VApp (Thunk arg) : sp) <$> mapM (thApp arg) st
  VCon c sp st ->
    VCon c (VApp (Thunk arg) : sp) <$> mapM (thApp arg) st
  u -> error $ "vApp: Impossible " ++ show u

thApp arg fun = Thunk <$> vApp (unthunk fun) arg

vUnlock :: MonadMEnv m => Val -> Cof -> m Val
vUnlock t p = case t of
  VLock q t' -> t' $$? q
  VFlex mv sp st ->
    VFlex mv (VUnlock p : sp) <$> mapM (thUnlock p) st
  VRigid v sp st ->
    VRigid v (VUnlock p : sp) <$> mapM (thUnlock p) st
  VCon c sp st ->
    VCon c (VUnlock p : sp) <$> mapM (thUnlock p) st
  _ -> error "Impossible"

thUnlock p x = Thunk <$> vUnlock (unthunk x) p

vOutCof :: Cof -> Thunk Val -> Val -> Val
vOutCof _ _ (VInCof _ t) = unthunk t
vOutCof p u (VFlex mv sp st)
  = VFlex mv (VOutCof p u:sp) $ SingleCase p u <> (thOutCof p u <$> st)
vOutCof p u (VRigid v sp st)
  = VRigid v (VOutCof p u:sp) $ SingleCase p u <> (thOutCof p u <$> st)
vOutCof p u (VCon c sp st)
  = VCon c (VOutCof p u:sp) $ SingleCase p u <> (thOutCof p u <$> st)
vOutCof _ _ _ = error "Impossible"

thOutCof p u = Thunk . vOutCof p u . unthunk

vFst, vSnd, vSuc :: Val -> Val
vFst (VPair t _) = unthunk t
vFst (VFlex mv sp st) = VFlex mv (VFst:sp) $ thFst <$> st
vFst (VRigid v sp st) = VRigid v (VFst:sp) $ thFst <$> st
vFst (VCon c sp st) = VCon c (VFst:sp) $ thFst <$> st
vFst _ = error "Impossible"

thFst = Thunk . vFst . unthunk

vSnd (VPair _ t) = unthunk t
vSnd (VFlex mv sp st) = VFlex mv (VSnd:sp) $ thSnd <$> st
vSnd (VRigid v sp st) = VRigid v (VSnd:sp) $ thSnd <$> st
vSnd (VCon c sp st) = VCon c (VSnd:sp) $ thSnd <$> st
vSnd u = error $ "vSnd: Impossible " ++ show u

thSnd = Thunk . vSnd . unthunk

vSuc (VSuc k v') = VSuc (k+1) v'
vSuc v = VSuc 1 (Thunk v)

vEl :: Val -> TyVal
vEl (VQuote ty) = unthunk ty
vEl v = VEl v

vNatElim :: MonadMEnv m
  => Closure Var Type
  -> Closure () Term
  -> Closure (Var, Var) Term
  -> Val -> m Val
vNatElim m z s = \case
  VZero -> z $$ \() -> []
  VSuc _ (Thunk (VSuc _ _)) -> error "Internal error: stacked VSuc"
  VSuc k (Thunk v) -> go k =<< vNatElim m z s v
    where
      go 0 v = return v
      go k v = do
        v' <- go (k-1) v
        s $$ \(n,r) -> [(n, VSuc k (Thunk VZero)), (r, v')]
  VFlex mv sp st ->
    VFlex mv (VNatElim m z s : sp) <$> mapM (thNatElim m z s) st
  VRigid v sp st ->
    VRigid v (VNatElim m z s : sp) <$> mapM (thNatElim m z s) st
  VCon c sp st ->
    VCon c (VNatElim m z s : sp) <$> mapM (thNatElim m z s) st
  _ -> error "Impossible"

thNatElim m z s x = Thunk <$> vNatElim m z s (unthunk x)

-- If the neutral form destablizes, fetch the resulting value
-- If the metavariable produced a solution, fetch the solution too
force :: MonadMEnv m => CofEnv -> Thunk Val -> m Val
force cofEnv (Thunk m@(VFlex (MetaVar _ mid subs) sp st)) = do
  sol <- gets (IM.lookup mid . termSol)
  case sol of
    Just b -> vSpine sp =<< b $$ (`zip'` map unthunk subs)
    Nothing -> case cofSelect cofEnv st of
      Just x -> force cofEnv x
      Nothing -> return m
force cofEnv (Thunk (VRigid _ _ st))
  | Just x <- cofSelect cofEnv st = force cofEnv x
force cofEnv (Thunk (VCon _ _ st))
  | Just x <- cofSelect cofEnv st = force cofEnv x
force _ (Thunk a) = return a

forceTy :: MonadMEnv m => CofEnv -> Thunk TyVal -> m TyVal
forceTy cofEnv (Thunk m@(VMTyVar (MetaVar _ mid subs) st)) = do
  sol <- gets (IM.lookup mid . typeSol)
  case sol of
    Just b -> b $$: (`zip'` map unthunk subs)
    Nothing -> case cofSelect cofEnv st of
      Just x -> forceTy cofEnv x
      Nothing -> return m
forceTy cofEnv (Thunk (VEl t)) = VEl <$> force cofEnv (Thunk t)
forceTy _ (Thunk a) = return a

------ Normalization by evaluation ------

eval :: MonadMEnv m => Env -> CofEnv -> Term -> m Val
eval env cofEnv = \case
  Var x -> return $ lookupLocal env x
  MVar (MetaVar name mid subs)
    -> vMeta [] EmptyCases . MetaVar name mid . map Thunk =<<
      mapM (eval env cofEnv) subs
  Con (Const name subs)
    -> vCon env cofEnv [] . Const name . map Thunk =<<
      mapM (eval env cofEnv) subs
  -- Let name clause body
  --   -> eval (bindGlobal name _ env) body

  Lam s -> return $ VLam $ closeB env cofEnv s
  App t1 t2 -> do
    v1 <- eval env cofEnv t1
    v2 <- eval env cofEnv t2
    vApp v1 v2

  Pair t1 t2 -> do
    v1 <- eval env cofEnv t1
    v2 <- eval env cofEnv t2
    return $ VPair (Thunk v1) (Thunk v2)
  Fst t -> vFst <$> eval env cofEnv t
  Snd t -> vSnd <$> eval env cofEnv t

  Zero -> return VZero
  Suc t -> vSuc <$> eval env cofEnv t
  NatElim m z s t -> do
    v <- eval env cofEnv t
    vNatElim
      (closeB env cofEnv m)
      (closeB env cofEnv (bind () z))
      (closeB env cofEnv s)
      v

  Lock p t -> return $ VLock p $ closeB env cofEnv (bind () t)
  Unlock t p -> do
    v <- eval env (bindToken p cofEnv) t
    vUnlock v p

  InCof p t -> do
    v <- eval env cofEnv t
    return $ VInCof p (Thunk v)
  OutCof p u t -> do
    vu <- eval env cofEnv u
    vt <- eval env cofEnv t
    return $ vOutCof p (Thunk vu) vt

  Quote ty -> VQuote . Thunk <$> evalTy env cofEnv ty
  The _ tm -> eval env cofEnv tm

evalTy :: MonadMEnv m => Env -> CofEnv -> Type -> m TyVal
evalTy env cofEnv = \case
  MTyVar (MetaVar name mid subs)
    -> vMetaTy EmptyCases . MetaVar name mid . map Thunk =<<
      mapM (eval env cofEnv) subs
  Sigma t1 t2 -> do
    v1 <- evalTy env cofEnv t1
    return $ VSigma (Thunk v1) (closeB env cofEnv t2)
  Pi t1 t2 -> do
    v1 <- evalTy env cofEnv t1
    return $ VPi (Thunk v1) (closeB env cofEnv t2)
  Nat -> return VNat
  Pushforward p ty -> return $ VPushforward p (closeB env cofEnv (bind () ty))
  Ext ty p tm -> do
    vty <- evalTy env cofEnv ty
    return $ VExt (Thunk vty) p (closeB env cofEnv (bind () tm))
  Universe -> return VUniverse
  El t -> vEl <$> eval env cofEnv t

-- Helpers for evaluating closures

($$+) :: (MonadMEnv m, Alpha p) => Closure p Term -> (p -> [(Var, Val)]) -> m (p, Val)
Closure env cofEnv t $$+ r = do
  (x, s) <- unbind t
  s' <- eval (bindLocal (r x) env) cofEnv s
  return (x, s')

($$) :: (MonadMEnv f, Alpha a) => Closure a Term -> (a -> [(Var, Val)]) -> f Val
t $$ r = snd <$> t $$+ r

($$?) :: (MonadMEnv m) => Closure () Term -> Cof -> m Val
Closure env cofEnv t $$? p = do
  (_, s) <- unbind t
  eval env (bindToken p cofEnv) s

($$:+) :: (MonadMEnv m, Alpha p) => Closure p Type -> (p -> [(Var, Val)]) -> m (p, TyVal)
Closure env cofEnv t $$:+ r = do
  (x, s) <- unbind t
  s' <- evalTy (bindLocal (r x) env) cofEnv s
  return (x, s')

($$:) :: (MonadMEnv f, Alpha a) => Closure a Type -> (a -> [(Var, Val)]) -> f TyVal
t $$: r = snd <$> t $$:+ r

---- Reflection
reflectSpine :: MonadMEnv m => CofEnv -> [Spine] -> Term -> m Term
reflectSpine _ [] val = return val
reflectSpine cofEnv (c:sp) val0 = do
  val <- reflectSpine cofEnv sp val0
  case c of
    VApp thunk -> App val <$> (reify cofEnv =<< force cofEnv thunk)
    VFst -> return $ Fst val
    VSnd -> return $ Snd val
    VNatElim cm cz cs -> do -- TODO should we not normalize the motive?
      tym <- cm $$:- \n -> [(n, VVar n)]
      tz <- cz $$- \() -> []
      (_, tz') <- unbind tz
      ts <- cs $$- \(k,r) -> [(k, VVar k), (r, VVar r)]
      -- instead of tym, directly use cm
      return $ NatElim tym tz' ts val
    VUnlock p -> return $ Unlock val p
    VOutCof p u -> do
      vu <- force cofEnv u
      tu <- reify cofEnv vu
      return $ OutCof p tu val

reify :: MonadMEnv m => CofEnv -> Val -> m Term
-- We assume these are already forced
reify cofEnv (VRigid v sp _) = reflectSpine cofEnv sp (Var v)
reify cofEnv (VFlex (MetaVar name mid subs) sp _)
  = reflectSpine cofEnv sp . MVar . MetaVar name mid =<<
    mapM (reify cofEnv <=< force cofEnv) subs
reify cofEnv (VCon (Const name subs) sp _)
  = reflectSpine cofEnv sp . Con . Const name =<<
    mapM (reify cofEnv <=< force cofEnv) subs

---- Reification
reify _ (VLam c) = Lam <$> c $$- \x -> [(x, VVar x)]
reify cofEnv (VPair th1 th2) = do
  v1 <- force cofEnv th1
  v2 <- force cofEnv th2
  Pair <$> reify cofEnv v1 <*> reify cofEnv v2

reify _ VZero = return Zero
reify cofEnv (VSuc k th) = nTimes k Suc <$> (reify cofEnv =<< force cofEnv th)

reify _ (VLock p c) = Lock p <$> c $$?- p

reify cofEnv (VInCof p th) = InCof p <$> (reify cofEnv =<< force cofEnv th)

reify cofEnv (VQuote thty) = Quote <$> (reifyTy cofEnv =<< forceTy cofEnv thty)

reifyTy :: MonadMEnv m => CofEnv -> TyVal -> m Type
-- reflection
reifyTy cofEnv (VMTyVar (MetaVar name mid subs) _)
  = MTyVar . MetaVar name mid <$>
    mapM (reify cofEnv <=< force cofEnv) subs

-- reification
reifyTy cofEnv (VSigma thty c) = do
  ty <- reifyTy cofEnv =<< forceTy cofEnv thty
  t <- c $$:- \x -> [(x, VVar x)]
  return $ Sigma ty t
reifyTy cofEnv (VPi thty c) = do
  ty <- reifyTy cofEnv =<< forceTy cofEnv thty
  t <- c $$:- \x -> [(x, VVar x)]
  return $ Pi ty t
reifyTy _ VNat = return Nat
reifyTy _ (VPushforward p c) = Pushforward p <$> c $$:?- p
reifyTy cofEnv (VExt thty p c) = do
  ty <- reifyTy cofEnv =<< forceTy cofEnv thty
  Ext ty p <$> c $$?- p
reifyTy _ VUniverse = return Universe
reifyTy cofEnv (VEl tm) = El <$> reify cofEnv tm

($$-) :: (MonadMEnv m, Alpha p) => Closure p Term -> (p -> [(Var, Val)]) -> m (Bind p Term)
Closure env cofEnv t $$- r = do
  (x, s) <- unbind t
  s' <- eval (bindLocal (r x) env) cofEnv s
  t' <- reify cofEnv =<< force cofEnv (Thunk s')
  return (bind x t')

($$:-) :: (MonadMEnv m, Alpha p) => Closure p Type -> (p -> [(Var, Val)]) -> m (Bind p Type)
Closure env cofEnv t $$:- r = do
  (x, s) <- unbind t
  s' <- evalTy (bindLocal (r x) env) cofEnv s
  t' <- reifyTy cofEnv =<< forceTy cofEnv (Thunk s')
  return (bind x t')

($$?-) :: MonadMEnv m => Closure () Term -> Cof -> m Term
Closure env cofEnv t $$?- p = do
  (_, s) <- unbind t
  s' <- eval env (bindToken p cofEnv) s
  reify (bindToken p cofEnv) =<< force (bindToken p cofEnv) (Thunk s')

($$:?-) :: MonadMEnv m => Closure () Type -> Cof -> m Type
Closure env cofEnv t $$:?- p = do
  (_, s) <- unbind t
  s' <- evalTy env (bindToken p cofEnv) s
  reifyTy (bindToken p cofEnv) =<< forceTy (bindToken p cofEnv) (Thunk s')

---- Example monad to use the functions ----
type MetaEnvM = StateT MetaEnv FreshM
instance MonadMEnv MetaEnvM
runMetaEnvM :: MetaEnvM a -> a
runMetaEnvM m = runFreshM (evalStateT m emptyMetaEnv)

nf :: Env -> CofEnv -> Term -> Term
nf env cofEnv t = runMetaEnvM $ do
  v <- eval env cofEnv t
  reify cofEnv v
