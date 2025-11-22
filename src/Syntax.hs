module Syntax (
  Var, MetaVar(..), Term(..), Type(..),
  Env, MetaEnv(..), MonadEnv, emptyMetaEnv,
  Closure(..), Spine(..),
  Val(.. {- exclude VNeutral -}, VVar),
  vApp, vFst, vSnd, vSuc, vNatElim,
  TyVal(..), Thunk (Thunk), force,
  eval, evalTy, ($$), ($$-),
  quote, quoteTy,
  -- nf,
  nfSubst
) where
import Unbound.Generics.LocallyNameless
import GHC.Generics (Generic)
import Data.Maybe (fromJust)
import Data.Foldable (foldrM)
import qualified Data.IntMap as IM
import qualified Data.Map as M
import Control.Monad.State
import Control.Lens (anyOf)

import Utils

type Var = Name Term
data MetaVar a = MetaVar
  {- suggested name -} !String
  {- metavar id -} !Int
  {- stuck substitution -} ![a] deriving (Show, Generic)

data Term
  = Var Var | MVar (MetaVar Term)
  | Lam (Bind Var Term) | App Term Term
  | Pair Term Term | Fst Term | Snd Term
  | Zero | Suc Term
  | NatElim
    {- motive -} (Bind Var Type)
    {- zero -} Term
    {- suc -} (Bind (Var, Var) Term)
    {- arg -} Term
  | Quote Type
  | The Type Term
  deriving (Generic) -- TODO get a readback to raw terms and test roundtrip

showTermM :: Int -> Term -> LFreshM ShowS
showTermM i = \case
  Var x -> return (showsPrec i x)
  MVar (MetaVar name _ subs) ->
    (\tms -> shows name . showList (map (\x -> x "") tms)) <$>
    mapM (showTermM 0) subs
  Lam t -> lunbind t \(x, t') -> do
    s <- showTermM 0 t'
    return (showParen (i > 0) $
      showString "λ" . shows x . showString ". " . s)
  App t1 t2 -> do
    s1 <- showTermM 10 t1
    s2 <- showTermM 11 t2
    return (showParen (i > 10) $ s1 . showString " " . s2)
  Pair t1 t2 -> do
    s1 <- showTermM 0 t1
    s2 <- showTermM 0 t2
    return (showParen True $ s1 . showString ", " . s2)
  Fst t -> do
    s <- showTermM 0 t
    return (showString "fst" . showParen True s)
  Snd t -> do
    s <- showTermM 0 t
    return (showString "snd" . showParen True s)
  Zero -> return (showString "0")
  Suc t -> case acc 0 (Suc t) of
    (k, Zero) -> return (shows k)
    (k, t') -> do
      s <- showTermM 1 t'
      return $ showParen (i > 1) $ shows k . showString " + " . s
    where
      acc :: Int -> Term -> (Int, Term)
      acc k (Suc t0) = acc (k+1) t0
      acc k t0 = (k, t0)
  NatElim m z s t -> do
    sm <- lunbind m \(n, m') -> do
      sm <- showTypeM 0 m'
      return $ shows n . showString ". " . sm . showString ", "
    sz <- showTermM 0 z
    ss <- lunbind s \(x, s') -> do
      ss <- showTermM 0 s'
      return $ shows x . showString ". " . ss . showString ", "
    st <- showTermM 0 t
    return $ showString "elim" .
      showParen True (sm . sz . showString ", " . ss . st)
  Quote t -> showTypeM i t
  The ty tm -> do
    sty <- showTypeM 1 ty
    stm <- showTermM 1 tm
    return (showParen (i > 0) $ stm . showString " : " . sty)

instance Show Term where
  showsPrec i t = runLFreshM (showTermM i t)

data Type -- Note there is no type variables
  = Sigma Type (Bind Var Type)
  | Pi Type (Bind Var Type)
  | Nat
  | Universe
  | El Term
  deriving (Generic)

occurs :: Var -> Type -> Bool
occurs x = anyOf fv (== x)

showTypeM :: Int -> Type -> LFreshM ShowS
showTypeM i = \case
  Sigma t1 t2 -> do
    s1 <- showTypeM 0 t1
    lunbind t2 \(x, t') -> do
      s2 <- showTypeM 0 t'
      return (showParen (i > 0) $
        (if occurs x t' then
          showParen True (shows x . showString " : " . s1)
        else s1) .
        showString " × " . s2)
  Pi t1 t2 -> do
    s1 <- showTypeM 0 t1
    lunbind t2 \(x, t') -> do
      s2 <- showTypeM 0 t'
      return (showParen (i > 0) $
        (if occurs x t' then
          showParen True (shows x . showString " : " . s1)
        else s1) .
        showString " → " . s2)
  Nat -> return (showString "Nat")
  Universe -> return (showString "U")
  El t -> do
    s <- showTermM 0 t
    return (showString "El" . showParen True s)


instance Show Type where
  showsPrec i t = runLFreshM (showTypeM i t)

instance Alpha a => Alpha (MetaVar a)
instance Alpha Term
instance Alpha Type

instance Subst Term Term where
  isvar (Var x) = Just (SubstName x)
  isvar _ = Nothing

instance Subst Term Type

instance Subst Term (MetaVar Term)

----- Substitution based normalization -----
substnf :: Term -> FreshM Term
substnf (Var x) = return $ Var x
substnf (MVar (MetaVar name mid subs))
  = MVar . MetaVar name mid <$> mapM substnf subs
substnf (Lam t) = do
  (y, t') <- unbind t
  Lam . bind y <$> substnf t'
substnf (App t1 t2) = do
  n1 <- substnf t1
  case n1 of
    Lam t -> do
      n2 <- substnf t2
      substnf $ substBind t n2
    _ -> App n1 <$> substnf t2
substnf (Pair t1 t2) = Pair <$> substnf t1 <*> substnf t2
substnf (Fst t) = do
  n <- substnf t
  case n of
    Pair n1 _ -> return n1
    _ -> return $ Fst n
substnf (Snd t) = do
  n <- substnf t
  case n of
    Pair _ n2 -> return n2
    _ -> return $ Snd n
substnf Zero = return Zero
substnf (Suc t) = Suc <$> substnf t
substnf (NatElim m z s t) = do -- we don't deal with the motive
  n <- substnf t
  go n
  where
    go :: Term -> FreshM Term
    go Zero = substnf z
    go (Suc n) = do
      res <- go n
      substnf $ instantiate s [n, res]
    go r = return $ NatElim m z s r
substnf (Quote ty) = Quote <$> substnft ty
substnf (The _ tm) = substnf tm

substnft :: Type -> FreshM Type
substnft (Sigma t1 t2) = do
  (y, t2') <- unbind t2
  Sigma <$> substnft t1 <*> (bind y <$> substnft t2')
substnft (Pi t1 t2) = do
  (y, t2') <- unbind t2
  Pi <$> substnft t1 <*> (bind y <$> substnft t2')
substnft Nat = return Nat
substnft Universe = return Universe
substnft (El t) = El <$> substnf t

nfSubst :: Term -> Term
nfSubst = runFreshM . substnf

----- Normalization by Evaluation -----
type Env = M.Map Var Val
data MetaEnv = MetaEnv {
  nextMVar :: Int,
  solutions :: IM.IntMap (Closure [Var] Term) }
emptyMetaEnv :: MetaEnv
emptyMetaEnv = MetaEnv 0 IM.empty

class (Fresh m, MonadState MetaEnv m) => MonadEnv m

data Closure r t = Closure Env (Bind r t) deriving Show

-- Some metavariables may have been solved; remind us to look up the newest one.
-- Principle: if we immediately want to case split on the variable, then
-- make the input type a Thunk. Generally always make the output Thunk.
newtype Thunk = Thunk { unthunk :: Val } deriving Show
-- use unthunk to disregard this, and use force to make the update

data Spine
  = VApp {- -} Thunk
  | VFst {- -} | VSnd {- -}
  | VNatElim (Closure Var Type) (Closure () Term) (Closure (Var, Var) Term) {- -}
  deriving Show
-- There should be a TySpine in principle but it's just VEl by itself...

data Val
  = VNeutral !(Either (MetaVar Val) Var) [Spine]
  | VLam (Closure Var Term)
  | VPair Thunk Thunk
  | VZero | VSuc Int Thunk
  | VQuote TyVal
  deriving Show

data TyVal
  = VSigma TyVal (Closure Var Type)
  | VPi TyVal (Closure Var Type)
  | VNat
  | VUniverse
  | VEl Thunk
  deriving Show

-- Patterns for constructing values.
-- These should not look under metas, so they use "unthunk"
pattern VVar :: Var -> Val
pattern VVar x = VNeutral (Right x) []

vMeta :: MonadEnv m => MetaVar Val -> [Spine] -> m Val
vMeta m@(MetaVar _ mid subs) sp = do
  sol <- gets (IM.lookup mid . solutions)
  case sol of
    Just b -> do
      (_, val) <- b $$ (`zip'` subs)
      vSpine val sp
    Nothing -> return $ VNeutral (Left m) sp

vSpine :: MonadEnv m => Val -> [Spine] -> m Val
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

force :: MonadEnv m => Thunk -> m Val
force (Thunk (VNeutral (Left m) sp)) = vMeta m sp
force (Thunk a) = return a

vApp :: MonadEnv m => Val -> Val -> m Val
vApp t u = case t of
  VLam t' -> snd <$> t' $$ \x -> [(x, u)]
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

vNatElim :: MonadEnv m
  => Closure Var Type
  -> Closure () Term
  -> Closure (Var, Var) Term
  -> Val -> m Val
vNatElim m z s = \case
  VZero -> snd <$> z $$ \() -> []
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
      snd <$> s $$ \(n,r) -> [(n, VSuc k (Thunk VZero)), (r, v')]

-- Eval will unfold the (surface) metas, so we return `Val` not `Thunk`
eval :: MonadEnv m => Env -> Term -> m Val
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

evalTy :: MonadEnv m => Env -> Type -> m TyVal
evalTy env = \case
  Sigma t1 t2 -> do
    v1 <- evalTy env t1
    return $ VSigma v1 (Closure env t2)
  Pi t1 t2 -> do
    v1 <- evalTy env t1
    return $ VPi v1 (Closure env t2)
  Nat -> return VNat
  Universe -> return VUniverse
  El t -> vEl <$> eval env t

($$) :: (MonadEnv m, Alpha p) => Closure p Term -> (p -> [(Var, Val)]) -> m (p, Val)
($$) (Closure env t) r = do
  (x, s) <- unbind t
  s' <- eval (M.union (M.fromList (r x)) env) s
  return (x, s')

($$-) :: (MonadEnv m, Alpha p) => Closure p Type -> (p -> [(Var, Val)]) -> m (p, TyVal)
($$-) (Closure env t) r = do
  (x, s) <- unbind t
  s' <- evalTy (M.union (M.fromList (r x)) env) s
  return (x, s')

quote :: MonadEnv m => Val -> m Term
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
        (n, vm) <- cm $$- \n -> [(n, VVar n)]
        tym <- quoteTy vm
        (_, vz) <- cz $$ \() -> []
        tz <- quote vz
        (p, vs) <- cs $$ \(k,r) -> [(k, VVar k), (r, VVar r)]
        ts <- quote vs
        -- instead of (bind n tym), directly use cm
        return $ NatElim (bind n tym) tz (bind p ts) val

quote (VLam c) = do
  (x, c') <- c $$ \x -> [(x, VVar x)]
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

quoteTy :: MonadEnv m => TyVal -> m Type
quoteTy (VSigma vty c) = do
  ty <- quoteTy vty
  (x, c') <- c $$- \x -> [(x, VVar x)]
  t <- quoteTy c'
  return $ Sigma ty (bind x t)
quoteTy (VPi vty c) = do
  ty <- quoteTy vty
  (x, c') <- c $$- \x -> [(x, VVar x)]
  t <- quoteTy c'
  return $ Pi ty (bind x t)
quoteTy VNat = return Nat
quoteTy VUniverse = return Universe
quoteTy (VEl th) = do
  t <- force th
  El <$> quote t

-- nf :: Env -> Term -> Term
-- nf env t = runFreshM $ flip runReader env do
--   v <- eval t
--   lift $ quote v
