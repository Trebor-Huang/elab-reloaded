module NbE (
  Equation, Env, emptyEnv, MetaEnv(..), emptyMetaEnv,
  Closure(..), Spine(..),
  Val(.. {- exclude VNeutral -}, VVar), toVar,
  vApp, vFst, vSnd, vSuc, vNatElim,
  TyVal(..), Thunk (Thunk), force,
  eval, evalTy, ($$), ($$:), ($$+), ($$:+),
  quote, quoteTy, nf,
  MonadMEnv, MetaEnvM, runMetaEnvM
) where

import Data.Maybe (fromJust)
import Data.Foldable (foldrM)
import qualified Data.IntMap as IM
import qualified Data.Map as M
import Control.Monad.State
import Unbound.Generics.LocallyNameless

import Syntax
import Utils

type Equation = Either (Thunk, Thunk) (TyVal, TyVal)

type Env = M.Map Var Val
emptyEnv :: Env
emptyEnv = M.empty
data MetaEnv = MetaEnv {
  nextMVar :: Int,
  termSol :: IM.IntMap (Closure [Var] Term),
  typeSol :: IM.IntMap (Closure [Var] Type),
  equations :: [Equation]  -- postponed equations
}
emptyMetaEnv :: MetaEnv
emptyMetaEnv = MetaEnv 0 IM.empty IM.empty []

class (Fresh m, MonadState MetaEnv m) => MonadMEnv m

data Closure r t = Closure Env (Bind r t) deriving Show

-- Some metavariables may have been solved; remind us to look up the newest one.
-- Principle: if we immediately want to case split on the variable, then
-- make the input type a Thunk. Generally always make the output Thunk.
newtype Thunk = Thunk { unthunk :: Val } deriving Show
-- use unthunk to disregard this, and use force to make the update
force :: MonadMEnv m => Thunk -> m Val
force (Thunk (VNeutral (Left m) sp)) = vMeta m sp
force (Thunk a) = return a

-- Eliminators
data Spine
  = VApp {- -} Thunk
  | VFst {- -} | VSnd {- -}
  | VNatElim (Closure Var Type) (Closure () Term) (Closure (Var, Var) Term) {- -}
  deriving Show
-- There should be a TySpine in principle but it's just VEl by itself...

data Val
  = VNeutral !(Either (MetaVar Val) Var) [Spine]
  -- Constructors
  | VLam (Closure Var Term)
  | VPair Thunk Thunk
  | VZero | VSuc Int Thunk
  | VQuote TyVal
  deriving Show

toVar :: Val -> Maybe Var
toVar (VVar v) = return v
toVar _ = Nothing

data TyVal
  = VMTyVar (MetaVar Val)
  | VEl Thunk
    -- todo this should be VNeutral,
    -- but none of the others would be type correct except VQuote
    -- which we deal with
  -- Type constructors
  | VSigma TyVal (Closure Var Type)
  | VPi TyVal (Closure Var Type)
  | VNat
  | VUniverse
  deriving Show

-- Patterns for constructing values.
-- These should not look under metas, so they use "unthunk"
pattern VVar :: Var -> Val
pattern VVar x = VNeutral (Right x) []

vMeta :: MonadMEnv m => MetaVar Val -> [Spine] -> m Val
vMeta m@(MetaVar _ mid subs) sp = do
  sol <- gets (IM.lookup mid . termSol)
  case sol of
    Just b -> do
      val <- b $$ (`zip'` subs)
      vSpine val sp
    Nothing -> return $ VNeutral (Left m) sp

vMetaTy :: MonadMEnv m => MetaVar Val -> m TyVal
vMetaTy m@(MetaVar _ mid subs) = do
  sol <- gets (IM.lookup mid . typeSol)
  case sol of
    Just b -> do
      b $$: (`zip'` subs)
    Nothing -> return $ VMTyVar m

vSpine :: MonadMEnv m => Val -> [Spine] -> m Val
vSpine v [] = return v
vSpine v (c:sp) = case c of
  VApp th -> do
    v' <- vApp (unthunk th) v
    vSpine v' sp
  VFst -> vSpine (vFst v) sp
  VSnd -> vSpine (vSnd v) sp
  VNatElim m z s -> do
    v' <- vNatElim m z s v
    vSpine v' sp

vApp :: MonadMEnv m => Val -> Val -> m Val
vApp t u = case t of
  VLam t' -> t' $$ \x -> [(x, u)]
  VNeutral v sp -> return $ VNeutral v (VApp (Thunk u) : sp)
  _ -> error "Impossible"

vFst, vSnd, vSuc :: Val -> Val
vFst (VPair t _) = unthunk t
vFst (VNeutral v sp) = VNeutral v (VFst:sp)
vFst _ = error "Impossible"

vSnd (VPair _ t) = unthunk t
vSnd (VNeutral v sp) = VNeutral v (VSnd:sp)
vSnd _ = error "Impossible"

vSuc (VSuc k v') = VSuc (k+1) v'
vSuc v = VSuc 1 (Thunk v)

vEl :: Val -> TyVal
vEl (VQuote ty) = ty
vEl v = VEl (Thunk v)

vNatElim :: MonadMEnv m
  => Closure Var Type
  -> Closure () Term
  -> Closure (Var, Var) Term
  -> Val -> m Val
vNatElim m z s = \case
  VZero -> z $$ \() -> []
  VSuc _ (Thunk (VSuc _ _)) -> error "Internal error: stacked VSuc"
  VSuc k (Thunk v) -> do
    vrec <- vNatElim m z s v
    go k vrec
  VNeutral v sp -> return $ VNeutral v (VNatElim m z s : sp)
  _ -> error "Impossible"
  where
    go 0 v = return v
    go k v = do
      v' <- go (k-1) v
      s $$ \(n,r) -> [(n, VSuc k (Thunk VZero)), (r, v')]

eval :: MonadMEnv m => Env -> Term -> m Val
eval env = \case
  Var x -> return $ fromJust $ M.lookup x env
  MVar (MetaVar name mid subs)
    -> (`vMeta` []) . MetaVar name mid =<< mapM (eval env) subs
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
  Quote ty -> VQuote <$> evalTy env ty
  The _ tm -> eval env tm

evalTy :: MonadMEnv m => Env -> Type -> m TyVal
evalTy env = \case
  MTyVar (MetaVar name mid subs)
    -> vMetaTy . MetaVar name mid =<< mapM (eval env) subs
  Sigma t1 t2 -> do
    v1 <- evalTy env t1
    return $ VSigma v1 (Closure env t2)
  Pi t1 t2 -> do
    v1 <- evalTy env t1
    return $ VPi v1 (Closure env t2)
  Nat -> return VNat
  Universe -> return VUniverse
  El t -> vEl <$> eval env t

($$+) :: (MonadMEnv m, Alpha p) => Closure p Term -> (p -> [(Var, Val)]) -> m (p, Val)
($$+) (Closure env t) r = do
  (x, s) <- unbind t
  s' <- eval (M.union (M.fromList (r x)) env) s
  return (x, s')

($$) :: (MonadMEnv f, Alpha a) => Closure a Term -> (a -> [(Var, Val)]) -> f Val
t $$ r = snd <$> t $$+ r

($$:+) :: (MonadMEnv m, Alpha p) => Closure p Type -> (p -> [(Var, Val)]) -> m (p, TyVal)
($$:+) (Closure env t) r = do
  (x, s) <- unbind t
  s' <- evalTy (M.union (M.fromList (r x)) env) s
  return (x, s')

($$:) :: (MonadMEnv f, Alpha a) => Closure a Type -> (a -> [(Var, Val)]) -> f TyVal
t $$: r = snd <$> t $$:+ r

quote :: MonadMEnv m => Val -> m Term
quote (VNeutral v sp) = do
  v' <- case v of
    Left (MetaVar name mid subs)
      -> MVar . MetaVar name mid <$> mapM quote subs
    Right v0 -> return $ Var v0
  foldrM go v' sp
  where
    go s val = case s of
      VApp thunk -> do
        arg <- force thunk
        App val <$> quote arg
      VFst -> return $ Fst val
      VSnd -> return $ Snd val
      VNatElim cm cz cs -> do -- TODO should we not normalize the motive?
        (n, vm) <- cm $$:+ \n -> [(n, VVar n)]
        tym <- quoteTy vm
        vz <- cz $$ \() -> []
        tz <- quote vz
        (p, vs) <- cs $$+ \(k,r) -> [(k, VVar k), (r, VVar r)]
        ts <- quote vs
        -- instead of (bind n tym), directly use cm
        return $ NatElim (bind n tym) tz (bind p ts) val

quote (VLam c) = do
  (x, c') <- c $$+ \x -> [(x, VVar x)]
  t <- quote c'
  return $ Lam (bind x t)
quote (VPair th1 th2) = do
  v1 <- force th1
  v2 <- force th2
  Pair <$> quote v1 <*> quote v2

quote VZero = return Zero
quote (VSuc k th) = do
  v <- force th
  nTimes k Suc <$> quote v

quote (VQuote ty) = Quote <$> quoteTy ty

quoteTy :: MonadMEnv m => TyVal -> m Type
quoteTy (VMTyVar (MetaVar name mid subs))
  = MTyVar . MetaVar name mid <$> mapM quote subs
quoteTy (VSigma vty c) = do
  ty <- quoteTy vty
  (x, c') <- c $$:+ \x -> [(x, VVar x)]
  t <- quoteTy c'
  return $ Sigma ty (bind x t)
quoteTy (VPi vty c) = do
  ty <- quoteTy vty
  (x, c') <- c $$:+ \x -> [(x, VVar x)]
  t <- quoteTy c'
  return $ Pi ty (bind x t)
quoteTy VNat = return Nat
quoteTy VUniverse = return Universe
quoteTy (VEl th) = do
  t <- force th
  El <$> quote t

---- Example monad to use the functions ----
type MetaEnvM = StateT MetaEnv FreshM
instance MonadMEnv MetaEnvM
runMetaEnvM :: MetaEnvM a -> a
runMetaEnvM m = runFreshM (evalStateT m emptyMetaEnv)

nf :: Env -> Term -> Term
nf env t = runMetaEnvM $ do
  v <- eval env t
  quote v
