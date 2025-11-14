module Syntax (
  normterm,
  testterm,
  nbeterm
) where
import Unbound.Generics.LocallyNameless
import GHC.Generics (Generic)
import Data.Maybe (fromJust)

type Var = Name Term

data Term
  = Var Var
  | Lam (Bind Var Term) | App Term Term
  | Pair Term Term | Fst Term | Snd Term
  | Zero | Suc Term | NatElim Term (Bind (Var, Var) Term) Term
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
  Suc t -> do
    s <- showTermM 0 t
    return (showString "suc" . showParen True s)
  NatElim z s t -> do
    sz <- showTermM 0 z
    (x, s') <- unbind s
    ss <- showTermM 0 s'
    st <- showTermM 0 t
    return (showString "elim" . showParen True (
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

showTypeM :: Int -> Type -> FreshM ShowS
showTypeM i = \case
  Sigma t1 t2 -> do
    s1 <- showTypeM 0 t1
    (x, t') <- unbind t2
    s2 <- showTypeM 0 t'
    return (showParen (i > 0) $
      showParen True (shows x . showString " : " . s1) .
      showString " × ". s2)
  Pi t1 t2 -> do
    s1 <- showTypeM 0 t1
    (x, t') <- unbind t2
    s2 <- showTypeM 0 t'
    return (showParen (i > 0) $
      showParen True (shows x . showString " : " . s1) .
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
substnf (NatElim z s t) = do
  n <- substnf t
  go n
  where
    go :: Term -> FreshM Term
    go Zero = substnf z
    go (Suc n) = do
      res <- go n
      substnf $ instantiate s [n, res]
    go r = return $ NatElim z s r
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
data Closure r = Closure Env (Bind r Term)
data Val
  = VVar Var
  | VApp Val Val | VLam {- unpack -} (Closure Var)
  | VPair Val Val | VFst Val | VSnd Val
  | VNat Int | VSuc Int Val | VRec (Closure ()) (Closure (Var, Var)) Val

eval :: Env -> Term -> FreshM Val
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
  Zero -> return $ VNat 0
  Suc t -> do
    v <- eval env t
    case v of
      VNat k -> return (VNat (k+1))
      VSuc k v' -> return (VSuc (k+1) v')
      _ -> return $ VSuc 1 v
  NatElim z s t -> do
    v <- eval env t
    case v of
      VNat k -> do
        vz <- eval env z
        go k vz
      VSuc k v' -> go k (VRec (Closure env (bind () z)) (Closure env s) v')
      _ -> return $ VRec (Closure env (bind () z)) (Closure env s) v
    where
      go 0 v = return v
      go k v = do
        v' <- go (k-1) v
        ((n,r), s') <- unbind s
        eval ((n, VNat k) : (r,v') : env) s'
  Quote _ -> error ""
  The _ _ -> error ""

nTimes :: Int -> (a -> a) -> (a -> a)
nTimes 0 _ = id
nTimes n f = f . nTimes (n-1) f

quote :: Val -> FreshM Term
quote (VVar x) = return $ Var x
quote (VApp v1 v2) = App <$> quote v1 <*> quote v2
quote (VLam (Closure _ t)) = return (Lam t) -- ?
quote (VPair v1 v2) = Pair <$> quote v1 <*> quote v2
quote (VFst v) = Fst <$> quote v
quote (VSnd v) = Snd <$> quote v
quote (VNat n) = return $ nTimes n Suc Zero
quote (VSuc k v) = nTimes k Suc <$> quote v
quote (VRec (Closure _ z) (Closure _ s) v) = do
  (_, z') <- unbind z
  NatElim z' s <$> quote v

----- Examples -----

add :: Term
add = Lam $ bind x $ Lam $ bind y $
  NatElim (Var y) (bind (n , r) $ Suc (Var r)) (Var x)
  where
    x = s2n "x"
    y = s2n "y"
    n = s2n "n"
    r = s2n "r"

mul :: Term
mul = Lam $ bind x $ Lam $ bind y $
  NatElim Zero (bind (n , r) $ App (App add (Var r)) (Var y)) (Var x)
  where
    x = s2n "x"
    y = s2n "y"
    n = s2n "n"
    r = s2n "r"

four :: Term
four = App (App add (Suc (Suc Zero))) (Suc (Suc Zero))

testterm :: Term
testterm = App (App mul four) four

normterm :: Term
normterm = runFreshM $ substnf testterm

nbeterm :: Term
nbeterm = runFreshM $ quote =<< eval [] testterm
