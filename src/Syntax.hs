module Syntax (
  Var, MetaVar(..), Term(..), Type(..),
  nfSubst
) where
import Unbound.Generics.LocallyNameless
import GHC.Generics (Generic)
import Control.Lens (anyOf)

import Utils

type Var = Name Term
data MetaVar a = MetaVar
  {- suggested name -} !String
  {- metavar id -} !Int
  {- stuck substitution -} [a] deriving (Show, Generic)

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
    (\tms -> showString name . showList__ id tms) <$>
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
  = MTyVar (MetaVar Term)
  | Sigma Type (Bind Var Type)
  | Pi Type (Bind Var Type)
  | Nat
  | Universe
  | El Term
  deriving (Generic)

-- Todo remove dependency on lens
occurs :: Var -> Type -> Bool
occurs x = anyOf fv (== x)

showTypeM :: Int -> Type -> LFreshM ShowS
showTypeM i = \case
  MTyVar (MetaVar name _ subs) ->
    (\tms -> showString name . showList__ id tms) <$>
    mapM (showTermM 0) subs
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
substnft (MTyVar (MetaVar name mid subs))
  = MTyVar . MetaVar name mid <$> mapM substnf subs
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
