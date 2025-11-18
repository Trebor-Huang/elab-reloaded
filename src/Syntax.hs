module Syntax (
  Var, Term(..), Type(..),
  Env, Closure(..), Val(..), TyVal(..),
  eval, evalTy, ($$), ($$-), quote, quoteTy, nf, nfSubst
) where
import Unbound.Generics.LocallyNameless
import GHC.Generics (Generic)
import Data.Maybe (fromJust)
import Control.Lens (anyOf)

type Var = Name Term

data Term
  = Var Var
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
  deriving (Generic)

showTermM :: Int -> Term -> FreshM ShowS
showTermM i = \case
  Var x -> return (showsPrec i x)
  Lam t -> do
    (x, t') <- unbind t
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
    (n, m') <- unbind m
    sm <- showTypeM 0 m'
    sz <- showTermM 0 z
    (x, s') <- unbind s
    ss <- showTermM 0 s'
    st <- showTermM 0 t
    return (showString "elim" . showParen True (
        shows n . showString ". " . sm . showString ", " .
        sz . showString ", " .
        shows x . showString ". " . ss . showString ", " .
        st
      ))
  Quote t -> showTypeM i t
  The ty tm -> do
    sty <- showTypeM 1 ty
    stm <- showTermM 1 tm
    return (showParen (i > 0) $ stm . showString " : " . sty)

instance Show Term where
  showsPrec i t = runFreshM (showTermM i t)

data Type -- Note there is no type variables
  = Sigma Type (Bind Var Type)
  | Pi Type (Bind Var Type)
  | Nat
  | Universe
  | El Term
  deriving (Generic)

occurs :: Var -> Type -> Bool
occurs x = anyOf fv (== x)

showTypeM :: Int -> Type -> FreshM ShowS
showTypeM i = \case
  Sigma t1 t2 -> do
    s1 <- showTypeM 0 t1
    (x, t') <- unbind t2
    s2 <- showTypeM 0 t'
    return (showParen (i > 0) $
      (if occurs x t' then
        showParen True (shows x . showString " : " . s1)
      else s1) .
      showString " × ". s2)
  Pi t1 t2 -> do
    s1 <- showTypeM 0 t1
    (x, t') <- unbind t2
    s2 <- showTypeM 0 t'
    return (showParen (i > 0) $
      (if occurs x t' then
        showParen True (shows x . showString " : " . s1)
      else s1) .
      showString " → ". s2)
  Nat -> return (showString "Nat")
  Universe -> return (showString "U")
  El t -> do
    s <- showTermM 0 t
    return (showString "El" . showParen True s)


instance Show Type where
  showsPrec i t = runFreshM (showTypeM i t)

instance Alpha Term
instance Alpha Type

instance Subst Term Term where
  isvar (Var x) = Just (SubstName x)
  isvar _ = Nothing

instance Subst Term Type

----- Substitution based normalization -----
substnf :: Term -> FreshM Term
substnf (Var x) = return $ Var x
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
substnf (The ty tm) = The <$> substnft ty <*> substnf tm

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

----- Normalization by Evaluation -----
type Env = [(Var, Val)]
data Closure r t = Closure Env (Bind r t) deriving Show
data Val
  = VVar Var
  | VApp Val Val | VLam (Closure Var Term)
  | VPair Val Val | VFst Val | VSnd Val
  | VZero | VSuc Int Val
  | VRec (Closure Var Type) (Closure () Term) (Closure (Var, Var) Term) Val
  | VQuote TyVal
  deriving Show

data TyVal
  = VSigma TyVal (Closure Var Type)
  | VPi TyVal (Closure Var Type)
  | VNat
  | VUniverse
  | VEl Val
  deriving Show

eval :: Fresh m => Env -> Term -> m Val
eval env = \case
  Var x -> return $ fromJust $ lookup x env
  Lam s -> return $ VLam (Closure env s)
  App t1 t2 -> do
    v1 <- eval env t1
    v2 <- eval env t2
    case v1 of
      VLam (Closure env' t) -> do
        (x, s) <- unbind t
        eval ((x,v2):env') s
      _ -> return $ VApp v1 v2
  Pair t1 t2 -> VPair <$> eval env t1 <*> eval env t2
  Fst t -> do
    v <- eval env t
    case v of
      VPair t1 _ -> return t1
      _ -> return $ VFst v
  Snd t -> do
    v <- eval env t
    case v of
      VPair _ t2 -> return t2
      _ -> return $ VSnd v
  Zero -> return VZero
  Suc t -> do
    v <- eval env t
    case v of
      VSuc k v' -> return (VSuc (k+1) v')
      _ -> return $ VSuc 1 v
  NatElim m z s t -> do
    v <- eval env t
    let vrec = VRec (Closure env m) (Closure env (bind () z)) (Closure env s)
    case v of
      VZero -> eval env z
      VSuc k VZero -> go k =<< eval env z
      VSuc k v' -> go k (vrec v')
      _ -> return $ vrec v
    where
      go 0 v = return v
      go k v = do
        v' <- go (k-1) v
        ((n,r), s') <- unbind s
        eval ((n, VSuc k VZero) : (r,v') : env) s'
  Quote ty -> VQuote <$> evalTy env ty
  The _ tm -> eval env tm

evalTy :: Fresh m => Env -> Type -> m TyVal
evalTy env = \case
  Sigma t1 t2 -> do
    v1 <- evalTy env t1
    return $ VSigma v1 (Closure env t2)
  Pi t1 t2 -> do
    v1 <- evalTy env t1
    return $ VPi v1 (Closure env t2)
  Nat -> return VNat
  Universe -> return VUniverse
  El t -> do
    v <- eval env t
    case v of
      VQuote ty -> return ty
      _ -> return $ VEl v

nTimes :: Int -> (a -> a) -> (a -> a)
nTimes 0 _ = id
nTimes n f = f . nTimes (n-1) f

($$) :: (Fresh m, Alpha p) => Closure p Term -> (p -> [(Var, Val)]) -> m (p, Val)
($$) (Closure env t) r = do
  (x, s) <- unbind t
  s' <- eval (r x ++ env) s
  return (x, s')

($$-) :: (Fresh m, Alpha p) => Closure p Type -> (p -> [(Var, Val)]) -> m (p, TyVal)
($$-) (Closure env t) r = do
  (x, s) <- unbind t
  s' <- evalTy (r x ++ env) s
  return (x, s')

quote :: Fresh m => Val -> m Term
quote (VVar x) = return $ Var x
quote (VApp v1 v2) = App <$> quote v1 <*> quote v2
quote (VLam c) = do
  (x, c') <- c $$ \x -> [(x, VVar x)]
  t <- quote c'
  return $ Lam (bind x t)
quote (VPair v1 v2) = Pair <$> quote v1 <*> quote v2
quote (VFst v) = Fst <$> quote v
quote (VSnd v) = Snd <$> quote v
quote VZero = return Zero
quote (VSuc k v) = nTimes k Suc <$> quote v
quote (VRec cm cz cs v) = do -- TODO should we not normalize the motive?
  (n, m) <- cm $$- \n -> [(n, VVar n)]
  tym <- quoteTy m
  (_, z) <- cz $$ \() -> []
  tz <- quote z
  (p, s) <- cs $$ \(k,r) -> [(k, VVar k), (r, VVar r)]
  ts <- quote s
  -- instead of (bind n tym), directly use cm
  NatElim (bind n tym) tz (bind p ts) <$> quote v
quote (VQuote ty) = Quote <$> quoteTy ty

quoteTy :: Fresh m => TyVal -> m Type
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
quoteTy (VEl t) = El <$> quote t

nf :: Env -> Term -> Term
nf env t = runFreshM $ quote =<< eval env t

nfSubst :: Term -> Term
nfSubst = runFreshM . substnf
