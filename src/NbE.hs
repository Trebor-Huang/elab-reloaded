module NbE (
  GlobalEntry(..), Env(..), emptyEnv, bindLocal, lookupLocal, bindGlobal, lookupGlobal,
  Equation, MetaEnv(..), emptyMetaEnv,
  Closure(..), Spine(..),
  Val(.. {- exclude VNeutral -}, VVar), toVar,
  vApp, vFst, vSnd, vSuc, vNatElim, vSpine, vTop,
  TyVal(..), Thunk (Thunk), force, forceTy,
  eval, evalTy, ($$), ($$:), ($$+), ($$:+),
  Unfold(..), reify, reifyTy, reifySpine, nf,
  MonadMEnv, MetaEnvM, runMetaEnvM
) where

import qualified Data.IntMap as IM
import qualified Data.Map as M
import Control.Monad.State
import GHC.Generics
import Unbound.Generics.LocallyNameless

import Syntax
import Utils

--- Environment
data GlobalEntry
  = Definition Type Term
  | Postulate Type
  | Hypothetic Type (Bind Var GlobalEntry)
  -- Global definitions can't be closures
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
data Closure r t = Closure Env (Bind r t) deriving Show

-- Some metavariables may have been solved; remind us to look up the newest one.
-- Principle: if we immediately want to case split on the variable, then
-- make the input type a Thunk. Generally always make the output Thunk.
newtype Thunk a = Thunk { unthunk :: a } deriving Show
-- use unthunk to disregard this, and use force to make the update

-- Eliminators
data Spine
  = VApp {- -} (Thunk Val)
  | VFst {- -} | VSnd {- -}
  | VNatElim (Closure Var Type) (Closure () Term) (Closure (Var, Var) Term) {- -}
  deriving Show
-- There should be a TySpine in principle but it's just VEl by itself...

data Val
  = VFlex (MetaVar Val) [Spine]
  | VRigid Var [Spine]
  | VTop (Const Val) [Spine] !(Maybe (Thunk Val))
    -- the thunk should be lazy, but the Maybe should be strict
  -- Constructors
  | VLam (Closure Var Term)
  | VPair (Thunk Val) (Thunk Val)
  | VZero | VSuc Int (Thunk Val)
  | VQuote (Thunk TyVal)
  deriving Show

data TyVal
  = VMTyVar (MetaVar Val)
  | VEl (Thunk Val)
    -- this should be VTyNeutral,
    -- but none of the others would be type correct except VQuote
    -- which we deal with manually
  -- Type constructors
  | VSigma (Thunk TyVal) (Closure Var Type)
  | VPi (Thunk TyVal) (Closure Var Type)
  | VNat
  | VUniverse
  deriving Show

-- Patterns for constructing values.
-- These should not look under metas, so they use "unthunk"
pattern VVar :: Var -> Val
pattern VVar x = VRigid x []

toVar :: Val -> Maybe Var
toVar (VVar v) = Just v
toVar _ = Nothing

vMeta :: MonadMEnv m => [Spine] -> MetaVar Val -> m Val
vMeta sp m@(MetaVar _ mid subs) = do
  sol <- gets (IM.lookup mid . termSol)
  case sol of
    Just b -> vSpine sp =<< b $$ (`zip'` subs)
    Nothing -> return $ VFlex m sp

vMetaTy :: MonadMEnv m => MetaVar Val -> m TyVal
vMetaTy m@(MetaVar _ mid subs) = do
  sol <- gets (IM.lookup mid . typeSol)
  case sol of
    Just b -> b $$: (`zip'` subs)
    Nothing -> return $ VMTyVar m

vTop :: MonadMEnv m => Env -> [Spine] -> Const Val -> m Val
vTop env sp c@(Const name subs) = do
  result <- go env (lookupGlobal env name) subs
  case result of
    Just th -> VTop c sp . Just . Thunk <$> vSpine sp (unthunk th)
    Nothing -> return $ VTop c sp Nothing
  where
    go :: MonadMEnv m => Env -> GlobalEntry -> [Val] -> m (Maybe (Thunk Val))
    go env (Hypothetic _ bg) (v:subs) = do
      (x, g) <- unbind bg
      go (bindLocal [(x, v)] env) g subs
    go env (Definition _ tm) [] = Just . Thunk <$> eval env tm
    go _ (Postulate _) [] = return Nothing
    go _ _ _ = error "Impossible"

vSpine :: MonadMEnv m => [Spine] -> Val -> m Val
vSpine [] v = return v
vSpine (c:sp) v0 = do
  v <- vSpine sp v0
  case c of
    VApp th -> vApp (unthunk th) v
    VFst -> return $ vFst v
    VSnd -> return $ vSnd v
    VNatElim m z s -> vNatElim m z s v

vApp :: MonadMEnv m => Val -> Val -> m Val
vApp t u = case t of
  VLam t' -> t' $$ \x -> [(x, u)]
  VFlex mv sp -> return $ VFlex mv (VApp (Thunk u) : sp)
  VRigid v sp -> return $ VRigid v (VApp (Thunk u) : sp)
  VTop c sp v -> VTop c (VApp (Thunk u) : sp) <$>
    case v of
      Just th -> Just . Thunk <$> vApp (unthunk th) u
      Nothing -> return Nothing
  _ -> error "Impossible"

vFst, vSnd, vSuc :: Val -> Val
vFst (VPair t _) = unthunk t
vFst (VFlex mv sp) = VFlex mv (VFst:sp)
vFst (VRigid v sp) = VRigid v (VFst:sp)
vFst (VTop c sp v) = VTop c (VFst:sp) $ Thunk . vFst . unthunk <$> v
vFst _ = error "Impossible"

vSnd (VPair _ t) = unthunk t
vSnd (VFlex mv sp) = VFlex mv (VSnd:sp)
vSnd (VRigid v sp) = VRigid v (VSnd:sp)
vSnd (VTop c sp v) = VTop c (VSnd:sp) $ Thunk . vSnd . unthunk <$> v
vSnd _ = error "Impossible"

vSuc (VSuc k v') = VSuc (k+1) v'
vSuc v = VSuc 1 (Thunk v)

vEl :: Val -> TyVal
vEl (VQuote ty) = unthunk ty
vEl v = VEl (Thunk v)

vNatElim :: MonadMEnv m
  => Closure Var Type
  -> Closure () Term
  -> Closure (Var, Var) Term
  -> Val -> m Val
vNatElim m z s = \case
  VZero -> z $$ \() -> []
  VSuc _ (Thunk (VSuc _ _)) -> error "Internal error: stacked VSuc"
  VSuc k (Thunk v) -> go k =<< vNatElim m z s v
  VFlex mv sp -> return $ VFlex mv (VNatElim m z s : sp)
  VRigid v sp -> return $ VRigid v (VNatElim m z s : sp)
  _ -> error "Impossible"
  where
    go 0 v = return v
    go k v = do
      v' <- go (k-1) v
      s $$ \(n,r) -> [(n, VSuc k (Thunk VZero)), (r, v')]

-- Looking up the metavariables if there is one, lazily
force :: MonadMEnv m => Thunk Val -> m Val
force (Thunk (VFlex m sp)) = vMeta sp m
force (Thunk (VTop _ _ (Just val))) = force val
force (Thunk a) = return a

forceTy :: MonadMEnv m => Thunk TyVal -> m TyVal
forceTy (Thunk (VMTyVar m)) = vMetaTy m
forceTy (Thunk a) = return a

------ Normalization by evaluation ------

eval :: MonadMEnv m => Env -> Term -> m Val
eval env = \case
  Var x -> return $ lookupLocal env x
  MVar (MetaVar name mid subs)
    -> vMeta [] . MetaVar name mid =<< mapM (eval env) subs
  Top (Const name subs)
    -> vTop env [] . Const name =<< mapM (eval env) subs
  Lam s -> return $ VLam $ Closure env s
  App t1 t2 -> do
    v1 <- eval env t1
    v2 <- eval env t2
    vApp v1 v2
  Pair t1 t2 -> do
    v1 <- eval env t1
    v2 <- eval env t2
    return $ VPair (Thunk v1) (Thunk v2)
  Fst t -> vFst <$> eval env t
  Snd t -> vSnd <$> eval env t
  Zero -> return VZero
  Suc t -> vSuc <$> eval env t
  NatElim m z s t -> do
    v <- eval env t
    vNatElim (Closure env m) (Closure env (bind () z)) (Closure env s) v
  Quote ty -> VQuote . Thunk <$> evalTy env ty
  The _ tm -> eval env tm

evalTy :: MonadMEnv m => Env -> Type -> m TyVal
evalTy env = \case
  MTyVar (MetaVar name mid subs)
    -> vMetaTy . MetaVar name mid =<< mapM (eval env) subs
  Sigma t1 t2 -> do
    v1 <- evalTy env t1
    return $ VSigma (Thunk v1) (Closure env t2)
  Pi t1 t2 -> do
    v1 <- evalTy env t1
    return $ VPi (Thunk v1) (Closure env t2)
  Nat -> return VNat
  Universe -> return VUniverse
  El t -> vEl <$> eval env t

-- Helpers for evaluating closures

($$+) :: (MonadMEnv m, Alpha p) => Closure p Term -> (p -> [(Var, Val)]) -> m (p, Val)
($$+) (Closure env t) r = do
  (x, s) <- unbind t
  s' <- eval (bindLocal (r x) env) s
  return (x, s')

($$) :: (MonadMEnv f, Alpha a) => Closure a Term -> (a -> [(Var, Val)]) -> f Val
t $$ r = snd <$> t $$+ r

($$:+) :: (MonadMEnv m, Alpha p) => Closure p Type -> (p -> [(Var, Val)]) -> m (p, TyVal)
($$:+) (Closure env t) r = do
  (x, s) <- unbind t
  s' <- evalTy (bindLocal (r x) env) s
  return (x, s')

($$:) :: (MonadMEnv f, Alpha a) => Closure a Type -> (a -> [(Var, Val)]) -> f TyVal
t $$: r = snd <$> t $$:+ r

data Unfold = NoUnfold | UnfoldMeta | UnfoldDef deriving (Eq, Show)

reifySpine :: MonadMEnv m => Unfold -> [Spine] -> Term -> m Term
reifySpine _ [] val = return val
reifySpine b (c:sp) val0 = do
  val <- reifySpine b sp val0
  case c of
    VApp thunk -> App val <$> reify b (unthunk thunk)
    VFst -> return $ Fst val
    VSnd -> return $ Snd val
    VNatElim cm cz cs -> do -- TODO should we not normalize the motive?
      (n, vm) <- cm $$:+ \n -> [(n, VVar n)]
      tym <- reifyTy b vm
      vz <- cz $$ \() -> []
      tz <- reify b vz
      (p, vs) <- cs $$+ \(k,r) -> [(k, VVar k), (r, VVar r)]
      ts <- reify b vs
      -- instead of (bind n tym), directly use cm
      return $ NatElim (bind n tym) tz (bind p ts) val

reify :: MonadMEnv m => Unfold -> Val -> m Term
reify b (VRigid v sp) = reifySpine b sp (Var v)

reify b (VFlex m@(MetaVar name mid subs) sp) =
  case b of
    NoUnfold -> reifySpine b sp . MVar . MetaVar name mid =<< mapM (reify b) subs
    _ -> reify b =<< vMeta sp m

reify b (VTop (Const name subs) sp mval) =
  case (b, mval) of
    (UnfoldDef, Just val) -> reify b (unthunk val)
    _ -> reifySpine b sp . Top . Const name =<< mapM (reify b) subs

reify b (VLam c) = do
  (x, c') <- c $$+ \x -> [(x, VVar x)]
  t <- reify b c'
  return $ Lam (bind x t)
reify b (VPair th1 th2) =
  Pair <$> reify b (unthunk th1) <*> reify b (unthunk th2)

reify _ VZero = return Zero
reify b (VSuc k th) = nTimes k Suc <$> reify b (unthunk th)

reify b (VQuote thty) = Quote <$> reifyTy b (unthunk thty)

reifyTy :: MonadMEnv m => Unfold -> TyVal -> m Type
reifyTy b (VMTyVar (MetaVar name mid subs))
  = MTyVar . MetaVar name mid <$> mapM (reify b) subs
reifyTy b (VSigma thty c) = do
  ty <- reifyTy b (unthunk thty)
  (x, c') <- c $$:+ \x -> [(x, VVar x)]
  t <- reifyTy b c'
  return $ Sigma ty (bind x t)
reifyTy b (VPi thty c) = do
  ty <- reifyTy b (unthunk thty)
  (x, c') <- c $$:+ \x -> [(x, VVar x)]
  t <- reifyTy b c'
  return $ Pi ty (bind x t)
reifyTy _ VNat = return Nat
reifyTy _ VUniverse = return Universe
reifyTy b (VEl th) = El <$> reify b (unthunk th)

---- Example monad to use the functions ----
type MetaEnvM = StateT MetaEnv FreshM
instance MonadMEnv MetaEnvM
runMetaEnvM :: MetaEnvM a -> a
runMetaEnvM m = runFreshM (evalStateT m emptyMetaEnv)

nf :: Env -> Term -> Term
nf env t = runMetaEnvM $ do
  v <- eval env t
  reify UnfoldDef v
