{-# OPTIONS_GHC -Wno-missing-signatures #-}
module NbE (
  GlobalEntry(..), Env(..), emptyEnv, CofEnv(..), emptyCofEnv,
  bindLocal, bindGlobal,
  Equation, MetaEnv(..), emptyMetaEnv,
  Closure, closeB, getClosureMetas, Spine(..),
  Val(.. {- exclude neutral constructors -}, Var), toVar,
  vApp, vFst, vSnd, vEl, -- vSuc, vNatElim, vSpine, vCon,
  TyVal(..), Thunk (Thunk), force, forceTy,
  eval, evalTy, ($$), ($$:), ($$+), ($$:+),
  reify, reifyTy, reifySp, nf,
  MonadMEnv, MetaEnvM, runMetaEnvM
) where

import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import qualified Data.Map as M
import qualified Data.Graph as G
import Control.Monad.State
import Control.Monad.Except
import Control.Monad ((<=<))
import Control.Lens (anyOf)
import GHC.Generics
import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Unsafe (unsafeUnbind)

import qualified Syntax as S
import Cofibration
import Utils

-- todo check if all the monad assumptions are required
--- Environment
-- TODO include cof assumptions, and definitions can destabilize
data GlobalEntry
  = Definition S.Type S.Term
  | Postulate S.Type
  | Hypothesis S.Type (Bind S.Var GlobalEntry)
  -- Global definitions can't be closures
  | Locked Cof GlobalEntry
  deriving (Generic, Show)
instance Alpha GlobalEntry

data Env = Env {
  localEnv :: M.Map S.Var Val,
  globalEnv :: M.Map String GlobalEntry
} deriving Show

emptyEnv :: Env
emptyEnv = Env M.empty M.empty

lookupLocal :: Env -> S.Var -> Val
lookupLocal e v = case M.lookup v (localEnv e) of
  Just val -> val
  Nothing -> error "lookupLocal: impossible"

bindLocal :: [(S.Var, Val)] -> Env -> Env
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
  termSol :: IM.IntMap (Closure [S.Var] S.Term),
  typeSol :: IM.IntMap (Closure [S.Var] S.Type),
  equations :: [Equation],  -- postponed equations
  graph :: G.Graph
} deriving Show

emptyMetaEnv :: MetaEnv
emptyMetaEnv = MetaEnv IM.empty IM.empty []
  (G.buildG (0,-1) [])

class (Fresh m, MonadState MetaEnv m, MonadError String m) => MonadMEnv m

-- A closure stores an environment.
-- TODO hide the constructor and implement pruning
data Closure r t = Closure Env CofEnv (Bind r t)
instance (Show r, Show t) => Show (Closure r t) where
  show (Closure _ _ b) = show b
closeB :: (Alpha r, Alpha t) => Env -> CofEnv -> Bind r t -> Closure r t
closeB env cofEnv b = Closure (env {
  localEnv = M.filterWithKey (\k _ -> anyOf fv (== k) b) (localEnv env)
}) cofEnv b
getClosureMetas :: (Alpha r, Alpha p) => (p -> IS.IntSet) -> Closure r p -> IS.IntSet
getClosureMetas f (Closure env _ b) =
  M.foldMapWithKey (const getMetas) (localEnv env) `IS.union`
  f (snd $ unsafeUnbind b)

-- Some metavariables may have been solved; remind us to look up the newest one.
-- Principle: if we immediately want to case split on the variable, then
-- make the input type a Thunk. Generally always make the output Thunk.
newtype Thunk a = Thunk { unthunk :: a }
instance Show a => Show (Thunk a) where
  showsPrec i (Thunk a) = showsPrec i a
-- use unthunk to disregard this, and use force to make the update

-- Eliminators
data Spine
  = App {- -} (Thunk Val)
  | Fst {- -} | Snd {- -}
  | NatElim (Closure S.Var S.Type) (Closure () S.Term) (Closure (S.Var, S.Var) S.Term) {- -}
  | Unlock {- -} Cof
  | OutCof Cof (Thunk Val) {- -}
  deriving Show
-- There should be a TySpine in principle but it's just El by itself...

getSpineMetas :: Spine -> IS.IntSet
getSpineMetas (App (Thunk v)) = getMetas v
getSpineMetas Fst = IS.empty
getSpineMetas Snd = IS.empty
getSpineMetas (NatElim c1 c2 c3) =
  getClosureMetas S.getTyMetas c1 `IS.union`
  getClosureMetas S.getMetas c2 `IS.union`
  getClosureMetas S.getMetas c3
getSpineMetas (Unlock _) = IS.empty
getSpineMetas (OutCof _ (Thunk v)) = getMetas v

data Val
  -- todo these three leads to a lot of repeated clauses
  = Flex (S.MetaVar (Thunk Val)) [Spine] !(Cases (Thunk Val))
  | Rigid S.Var [Spine] {- neutral stablizer -} !(Cases (Thunk Val))
  | Con (S.Const (Thunk Val)) [Spine] {- unfolding result -} !(Cases (Thunk Val))

  -- Constructors
  | Lam (Closure S.Var S.Term)
  | Pair (Thunk Val) (Thunk Val)
  | Zero | Suc Int (Thunk Val)
  | Lock Cof (Closure () S.Term)
  | InCof Cof (Thunk Val)
  | Quote (Thunk TyVal)
  deriving Show

getMetas :: Val -> IS.IntSet
getMetas (Flex (S.MetaVar _ mid _) sp _) =
  IS.singleton mid `IS.union`
  IS.unions (map getSpineMetas sp)
getMetas (Rigid _ sp _) = IS.unions (map getSpineMetas sp)
getMetas (Con (S.Const _ subs) sp _) =
  IS.unions (map (getMetas . unthunk) subs) `IS.union`
  IS.unions (map getSpineMetas sp)
getMetas (Lam c) = getClosureMetas S.getMetas c
getMetas (Pair (Thunk a) (Thunk b)) =
  getMetas a `IS.union` getMetas b
getMetas Zero = IS.empty
getMetas (Suc _ (Thunk v)) = getMetas v
getMetas (Lock _ c) = getClosureMetas S.getMetas c
getMetas (InCof _ (Thunk v)) = getMetas v
getMetas (Quote (Thunk v)) = getTyMetas v

data TyVal
  = MTyVar (S.MetaVar (Thunk Val)) !(Cases (Thunk TyVal))
  | El Val
    -- this should be TyNeutral,
    -- but the thunk inside can only be neutral terms to be type correct
    -- except Quote which we deal with manually
    -- It doesn't modify the destabilization either so
  -- Type constructors
  | Sigma (Thunk TyVal) (Closure S.Var S.Type)
  | Pi (Thunk TyVal) (Closure S.Var S.Type)
  | Nat
  | Pushforward Cof (Closure () S.Type)
  | Ext (Thunk TyVal) Cof (Closure () S.Term)
  | Universe
  deriving Show

getTyMetas :: TyVal -> IS.IntSet
getTyMetas (MTyVar (S.MetaVar _ mid _) _) = IS.singleton mid
getTyMetas (El v) = getMetas v
getTyMetas (Sigma (Thunk v) c) =
  getTyMetas v `IS.union` getClosureMetas S.getTyMetas c
getTyMetas (Pi (Thunk v) c) =
  getTyMetas v `IS.union` getClosureMetas S.getTyMetas c
getTyMetas Nat = IS.empty
getTyMetas (Pushforward _ c) = getClosureMetas S.getTyMetas c
getTyMetas (Ext (Thunk v) _ c) =
  getTyMetas v `IS.union` getClosureMetas S.getMetas c
getTyMetas Universe = IS.empty

-- Patterns for constructing values.
-- These should not look under metas, so they use "unthunk"
pattern Var :: S.Var -> Val
pattern Var x = Rigid x [] EmptyCases

toVar :: Val -> Maybe S.Var
toVar (Var v) = Just v
toVar _ = Nothing

vMeta :: MonadMEnv m => [Spine] -> Cases (Thunk Val) -> S.MetaVar (Thunk Val) -> m Val
vMeta sp st m@(S.MetaVar _ mid subs) = do
  sol <- gets (IM.lookup mid . termSol)
  case sol of
    Just b -> do
      b' <- b $$ (`zip'` map unthunk subs)
      vsol <- vSpine sp b'
      let unfoldCase = SingleCase mempty (Thunk vsol)
        -- todo add back unfolding meta
      return $ Flex m sp $ unfoldCase <> st
    Nothing -> return $ Flex m sp EmptyCases

vMetaTy :: MonadMEnv m => Cases (Thunk TyVal) -> S.MetaVar (Thunk Val) -> m TyVal
vMetaTy st m@(S.MetaVar _ mid subs) = do
  sol <- gets (IM.lookup mid . typeSol)
  case sol of
    Just b -> do
      vsol <- b $$: (`zip'` map unthunk subs)
      let unfoldCase = SingleCase mempty (Thunk vsol)
      return $ MTyVar m $ unfoldCase <> st
    Nothing -> return $ MTyVar m st

-- TODO does this need stabilization info?
vCon :: MonadMEnv m => Env -> CofEnv -> [Spine] -> S.Const (Thunk Val) -> m Val
vCon env cofEnv sp c@(S.Const name subs) = do
  -- this does not use emptyEnv and emptyCofEnv, because
  -- the innermost evaluation needs this for the substitution to make sense
  result <- vCon' env cofEnv (lookupGlobal env name) (map unthunk subs)
  Con c sp <$> mapM (\x -> Thunk <$> vSpine sp (unthunk x)) result

vCon' :: MonadMEnv m =>
  Env -> CofEnv -> GlobalEntry -> [Val] -> m (Cases (Thunk Val))
vCon' env cofEnv (Hypothesis _ bg) (v:subs) = do
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
    App th -> vApp v (unthunk th)
    Fst -> return $ vFst v
    Snd -> return $ vSnd v
    NatElim m z s -> vNatElim m z s v
    Unlock p -> vUnlock v p
    OutCof p u -> return $ vOutCof p u v

vApp :: MonadMEnv m => Val -> Val -> m Val
vApp fun arg = case fun of
  Lam t' -> t' $$ \x -> [(x, arg)]
  Flex mv sp st ->
    Flex mv (App (Thunk arg) : sp) <$> mapM (thApp arg) st
  Rigid v sp st ->
    Rigid v (App (Thunk arg) : sp) <$> mapM (thApp arg) st
  Con c sp st ->
    Con c (App (Thunk arg) : sp) <$> mapM (thApp arg) st
  u -> error $ "vApp: Impossible " ++ show u

thApp arg fun = Thunk <$> vApp (unthunk fun) arg

vUnlock :: MonadMEnv m => Val -> Cof -> m Val
vUnlock t p = case t of
  Lock q t' -> t' $$? q
  Flex mv sp st ->
    Flex mv (Unlock p : sp) <$> mapM (thUnlock p) st
  Rigid v sp st ->
    Rigid v (Unlock p : sp) <$> mapM (thUnlock p) st
  Con c sp st ->
    Con c (Unlock p : sp) <$> mapM (thUnlock p) st
  _ -> error "Impossible"

thUnlock p x = Thunk <$> vUnlock (unthunk x) p

vOutCof :: Cof -> Thunk Val -> Val -> Val
vOutCof _ _ (InCof _ t) = unthunk t
vOutCof p u (Flex mv sp st)
  = Flex mv (OutCof p u:sp) $ SingleCase p u <> (thOutCof p u <$> st)
vOutCof p u (Rigid v sp st)
  = Rigid v (OutCof p u:sp) $ SingleCase p u <> (thOutCof p u <$> st)
vOutCof p u (Con c sp st)
  = Con c (OutCof p u:sp) $ SingleCase p u <> (thOutCof p u <$> st)
vOutCof _ _ _ = error "Impossible"

thOutCof p u = Thunk . vOutCof p u . unthunk

vFst, vSnd, vSuc :: Val -> Val
vFst (Pair t _) = unthunk t
vFst (Flex mv sp st) = Flex mv (Fst:sp) $ thFst <$> st
vFst (Rigid v sp st) = Rigid v (Fst:sp) $ thFst <$> st
vFst (Con c sp st) = Con c (Fst:sp) $ thFst <$> st
vFst _ = error "Impossible"

thFst = Thunk . vFst . unthunk

vSnd (Pair _ t) = unthunk t
vSnd (Flex mv sp st) = Flex mv (Snd:sp) $ thSnd <$> st
vSnd (Rigid v sp st) = Rigid v (Snd:sp) $ thSnd <$> st
vSnd (Con c sp st) = Con c (Snd:sp) $ thSnd <$> st
vSnd u = error $ "vSnd: Impossible " ++ show u

thSnd = Thunk . vSnd . unthunk

vSuc (Suc k v') = Suc (k+1) v'
vSuc v = Suc 1 (Thunk v)

vEl :: Val -> TyVal
vEl (Quote ty) = unthunk ty
vEl v = El v

vNatElim :: MonadMEnv m
  => Closure S.Var S.Type
  -> Closure () S.Term
  -> Closure (S.Var, S.Var) S.Term
  -> Val -> m Val
vNatElim m z s = \case
  Zero -> z $$ \() -> []
  Suc _ (Thunk (Suc _ _)) -> error "Internal error: stacked Suc"
  Suc k (Thunk v) -> go k =<< vNatElim m z s v
    where
      go 0 v = return v
      go k v = do
        v' <- go (k-1) v
        s $$ \(n,r) -> [(n, Suc k (Thunk Zero)), (r, v')]
  Flex mv sp st ->
    Flex mv (NatElim m z s : sp) <$> mapM (thNatElim m z s) st
  Rigid v sp st ->
    Rigid v (NatElim m z s : sp) <$> mapM (thNatElim m z s) st
  Con c sp st ->
    Con c (NatElim m z s : sp) <$> mapM (thNatElim m z s) st
  _ -> error "Impossible"

thNatElim m z s x = Thunk <$> vNatElim m z s (unthunk x)

-- If the neutral form destablizes, fetch the resulting value
-- If the metavariable produced a solution, fetch the solution too
force :: MonadMEnv m => CofEnv -> Thunk Val -> m Val
force cofEnv (Thunk m@(Flex (S.MetaVar _ mid subs) sp st)) = do
  sol <- gets (IM.lookup mid . termSol)
  case sol of
    Just b -> vSpine sp =<< b $$ (`zip'` map unthunk subs)
    Nothing -> case cofSelect cofEnv st of
      Just x -> force cofEnv x
      Nothing -> return m
force cofEnv (Thunk (Rigid _ _ st))
  | Just x <- cofSelect cofEnv st = force cofEnv x
force cofEnv (Thunk (Con _ _ st))
  | Just x <- cofSelect cofEnv st = force cofEnv x
force _ (Thunk a) = return a

forceTy :: MonadMEnv m => CofEnv -> Thunk TyVal -> m TyVal
forceTy cofEnv (Thunk m@(MTyVar (S.MetaVar _ mid subs) st)) = do
  sol <- gets (IM.lookup mid . typeSol)
  case sol of
    Just b -> b $$: (`zip'` map unthunk subs)
    Nothing -> case cofSelect cofEnv st of
      Just x -> forceTy cofEnv x
      Nothing -> return m
forceTy cofEnv (Thunk (El t)) = vEl <$> force cofEnv (Thunk t)
forceTy _ (Thunk a) = return a

------ Normalization by evaluation ------

eval :: MonadMEnv m => Env -> CofEnv -> S.Term -> m Val
eval env cofEnv = \case
  S.Var x -> return $ lookupLocal env x
  S.MVar (S.MetaVar name mid subs)
    -> vMeta [] EmptyCases . S.MetaVar name mid . map Thunk =<<
      mapM (eval env cofEnv) subs
  S.Con (S.Const name subs)
    -> vCon env cofEnv [] . S.Const name . map Thunk =<<
      mapM (eval env cofEnv) subs
  -- Let name clause body
  --   -> eval (bindGlobal name _ env) body

  S.Lam s -> return $ Lam $ closeB env cofEnv s
  S.App t1 t2 -> do
    v1 <- eval env cofEnv t1
    v2 <- eval env cofEnv t2
    vApp v1 v2

  S.Pair t1 t2 -> do
    v1 <- eval env cofEnv t1
    v2 <- eval env cofEnv t2
    return $ Pair (Thunk v1) (Thunk v2)
  S.Fst t -> vFst <$> eval env cofEnv t
  S.Snd t -> vSnd <$> eval env cofEnv t

  S.Zero -> return Zero
  S.Suc t -> vSuc <$> eval env cofEnv t
  S.NatElim m z s t -> do
    v <- eval env cofEnv t
    vNatElim
      (closeB env cofEnv m)
      (closeB env cofEnv (bind () z))
      (closeB env cofEnv s)
      v

  S.Lock p t -> return $ Lock p $ closeB env cofEnv (bind () t)
  S.Unlock t p -> do
    v <- eval env (bindToken p cofEnv) t
    vUnlock v p

  S.InCof p t -> do
    v <- eval env cofEnv t
    return $ InCof p (Thunk v)
  S.OutCof p u t -> do
    vu <- eval env cofEnv u
    vt <- eval env cofEnv t
    return $ vOutCof p (Thunk vu) vt

  S.Quote ty -> Quote . Thunk <$> evalTy env cofEnv ty
  S.The _ tm -> eval env cofEnv tm

evalTy :: MonadMEnv m => Env -> CofEnv -> S.Type -> m TyVal
evalTy env cofEnv = \case
  S.MTyVar (S.MetaVar name mid subs)
    -> vMetaTy EmptyCases . S.MetaVar name mid . map Thunk =<<
      mapM (eval env cofEnv) subs
  S.Sigma t1 t2 -> do
    v1 <- evalTy env cofEnv t1
    return $ Sigma (Thunk v1) (closeB env cofEnv t2)
  S.Pi t1 t2 -> do
    v1 <- evalTy env cofEnv t1
    return $ Pi (Thunk v1) (closeB env cofEnv t2)
  S.Nat -> return Nat
  S.Pushforward p ty -> return $ Pushforward p (closeB env cofEnv (bind () ty))
  S.Ext ty p tm -> do
    vty <- evalTy env cofEnv ty
    return $ Ext (Thunk vty) p (closeB env cofEnv (bind () tm))
  S.Universe -> return Universe
  S.El t -> vEl <$> eval env cofEnv t

-- Helpers for evaluating closures

($$+) :: (MonadMEnv m, Alpha p) => Closure p S.Term -> (p -> [(S.Var, Val)]) -> m (p, Val)
Closure env cofEnv t $$+ r = do
  (x, s) <- unbind t
  s' <- eval (bindLocal (r x) env) cofEnv s
  return (x, s')

($$) :: (MonadMEnv f, Alpha a) => Closure a S.Term -> (a -> [(S.Var, Val)]) -> f Val
t $$ r = snd <$> t $$+ r

($$?) :: (MonadMEnv m) => Closure () S.Term -> Cof -> m Val
Closure env cofEnv t $$? p = do
  (_, s) <- unbind t
  eval env (bindToken p cofEnv) s

($$:+) :: (MonadMEnv m, Alpha p) => Closure p S.Type -> (p -> [(S.Var, Val)]) -> m (p, TyVal)
Closure env cofEnv t $$:+ r = do
  (x, s) <- unbind t
  s' <- evalTy (bindLocal (r x) env) cofEnv s
  return (x, s')

($$:) :: (MonadMEnv f, Alpha a) => Closure a S.Type -> (a -> [(S.Var, Val)]) -> f TyVal
t $$: r = snd <$> t $$:+ r

reifySp :: MonadMEnv m => CofEnv -> [Spine] -> S.Term -> m S.Term
reifySp _ [] val = return val
reifySp cofEnv (c:sp) val0 = do
  val <- reifySp cofEnv sp val0
  case c of
    App thunk -> S.App val <$> (reify cofEnv =<< force cofEnv thunk)
    Fst -> return $ S.Fst val
    Snd -> return $ S.Snd val
    NatElim cm cz cs -> do -- TODO should we not normalize the motive?
      tym <- cm $$:- \n -> [(n, Var n)]
      tz <- cz $$- \() -> []
      (_, tz') <- unbind tz
      ts <- cs $$- \(k,r) -> [(k, Var k), (r, Var r)]
      -- instead of tym, directly use cm
      return $ S.NatElim tym tz' ts val
    Unlock p -> return $ S.Unlock val p
    OutCof p u -> do
      vu <- force cofEnv u
      tu <- reify cofEnv vu
      return $ S.OutCof p tu val

reify :: MonadMEnv m => CofEnv -> Val -> m S.Term
-- We assume these are already forced
reify cofEnv (Rigid v sp _) = reifySp cofEnv sp (S.Var v)
reify cofEnv (Flex (S.MetaVar name mid subs) sp _)
  = reifySp cofEnv sp . S.MVar . S.MetaVar name mid =<<
    mapM (reify cofEnv <=< force cofEnv) subs
reify cofEnv (Con (S.Const name subs) sp _)
  = reifySp cofEnv sp . S.Con . S.Const name =<<
    mapM (reify cofEnv <=< force cofEnv) subs

reify _ (Lam c) = S.Lam <$> c $$- \x -> [(x, Var x)]
reify cofEnv (Pair th1 th2) = do
  v1 <- force cofEnv th1
  v2 <- force cofEnv th2
  S.Pair <$> reify cofEnv v1 <*> reify cofEnv v2

reify _ Zero = return S.Zero
reify cofEnv (Suc k th) = nTimes k S.Suc <$> (reify cofEnv =<< force cofEnv th)

reify _ (Lock p c) = S.Lock p <$> c $$?- p

reify cofEnv (InCof p th) = S.InCof p <$> (reify cofEnv =<< force cofEnv th)

reify cofEnv (Quote thty) = S.Quote <$> (reifyTy cofEnv =<< forceTy cofEnv thty)

reifyTy :: MonadMEnv m => CofEnv -> TyVal -> m S.Type
-- reflection
reifyTy cofEnv (MTyVar (S.MetaVar name mid subs) _)
  = S.MTyVar . S.MetaVar name mid <$>
    mapM (reify cofEnv <=< force cofEnv) subs

-- reification
reifyTy cofEnv (Sigma thty c) = do
  ty <- reifyTy cofEnv =<< forceTy cofEnv thty
  t <- c $$:- \x -> [(x, Var x)]
  return $ S.Sigma ty t
reifyTy cofEnv (Pi thty c) = do
  ty <- reifyTy cofEnv =<< forceTy cofEnv thty
  t <- c $$:- \x -> [(x, Var x)]
  return $ S.Pi ty t
reifyTy _ Nat = return S.Nat
reifyTy _ (Pushforward p c) = S.Pushforward p <$> c $$:?- p
reifyTy cofEnv (Ext thty p c) = do
  ty <- reifyTy cofEnv =<< forceTy cofEnv thty
  S.Ext ty p <$> c $$?- p
reifyTy _ Universe = return S.Universe
reifyTy cofEnv (El tm) = S.El <$> reify cofEnv tm

($$-) :: (MonadMEnv m, Alpha p) => Closure p S.Term -> (p -> [(S.Var, Val)]) -> m (Bind p S.Term)
Closure env cofEnv t $$- r = do
  (x, s) <- unbind t
  s' <- eval (bindLocal (r x) env) cofEnv s
  t' <- reify cofEnv =<< force cofEnv (Thunk s')
  return (bind x t')

($$:-) :: (MonadMEnv m, Alpha p) => Closure p S.Type -> (p -> [(S.Var, Val)]) -> m (Bind p S.Type)
Closure env cofEnv t $$:- r = do
  (x, s) <- unbind t
  s' <- evalTy (bindLocal (r x) env) cofEnv s
  t' <- reifyTy cofEnv =<< forceTy cofEnv (Thunk s')
  return (bind x t')

($$?-) :: MonadMEnv m => Closure () S.Term -> Cof -> m S.Term
Closure env cofEnv t $$?- p = do
  (_, s) <- unbind t
  s' <- eval env (bindToken p cofEnv) s
  reify (bindToken p cofEnv) =<< force (bindToken p cofEnv) (Thunk s')

($$:?-) :: MonadMEnv m => Closure () S.Type -> Cof -> m S.Type
Closure env cofEnv t $$:?- p = do
  (_, s) <- unbind t
  s' <- evalTy env (bindToken p cofEnv) s
  reifyTy (bindToken p cofEnv) =<< forceTy (bindToken p cofEnv) (Thunk s')

---- Example monad to use the functions ----
type MetaEnvM = StateT MetaEnv (ExceptT String FreshM)
instance MonadMEnv MetaEnvM
runMetaEnvM :: MetaEnvM a -> Either String a
runMetaEnvM m = runFreshM $ runExceptT (evalStateT m emptyMetaEnv)

nf :: Env -> CofEnv -> S.Term -> Either String S.Term
nf env cofEnv t = runMetaEnvM $ do
  v <- eval env cofEnv t
  reify cofEnv v
