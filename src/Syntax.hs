module Syntax (
  Var, MetaVar(..), Const(..),
  Term(..), Type(..)
) where
import Unbound.Generics.LocallyNameless
import GHC.Generics (Generic)
import Control.Lens (anyOf)

import Cofibration
import Utils

type Var = Name Term
data MetaVar a = MetaVar
  {- suggested name -} !String
  {- metavar id -} !Int
  {- stuck substitution -} [a] deriving (Show, Generic)
data Const a = Const !String [a] deriving (Show, Generic)

data Term
  -- variables and metavariables
  = Var Var | MVar (MetaVar Term)
  -- constants -- todo add type constants
  | Con (Const Term) -- | Let !String (Bind [Var] Term) Term -- todo type decl
  -- function type
  | Lam (Bind Var Term) | App Term Term
  -- pair type
  | Pair Term Term | Fst Term | Snd Term
  -- natural numbers
  | Zero | Suc Term
  | NatElim
    {- motive -} (Bind Var Type)
    {- zero -} Term
    {- suc -} (Bind (Var, Var) Term)
    {- arg -} Term
  -- Pushforward type
  | Lock Cof Term | Unlock Term Cof
  -- Extension type
  | InCof Cof Term | OutCof Cof {- restrict -} Term {- actual -} Term
  -- universe type
  | Quote Type
  -- type ascription
  | The Type Term
  deriving (Generic) -- TODO get a readback to raw terms and test roundtrip

showTermM :: Int -> Term -> LFreshM ShowS
showTermM i = \case
  Var x -> return (showsPrec i x)
  MVar (MetaVar name _ subs) ->
    (\tms -> showString name . showList__ id tms) <$>
    mapM (showTermM 0) subs
  Con (Const name subs) ->
    (\tms -> showString name . showList__ id tms) <$>
    mapM (showTermM 0) subs
  -- Let name clause body -> _
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

  -- todo hide these constructors
  Lock p t -> do
    s <- showTermM 0 t
    return (showParen (i > 0) $
      showString "🔒" . shows p . showString ". " . s)
  Unlock t p -> do
    s <- showTermM 10 t
    return (showParen (i > 10) $ s . showString " @" . shows p)
  InCof p t -> do
    s <- showTermM 0 t
    return $ showParen (i > 0) (showString "In⟨" . shows p . showString "⟩ " . s)
  OutCof p _ t -> do -- todo show the restriction
    s <- showTermM 0 t
    return $ showParen (i > 0) (showString "Out⟨" . shows p . showString "⟩ " . s)

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
  | Pushforward Cof Type
  | Ext Type Cof Term
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

  Pushforward p ty -> do
    s <- showTypeM 0 ty
    return (showParen (i > 0) $
      showString "{" . shows p . showString "}" . s)
  Ext ty p tm -> do
    sty <- showTypeM 0 ty
    stm <- showTermM 0 tm
    return $ showString "{ " . sty .
      showString " | " . shows p .
      showString " ↪ " . stm . showString " }"

  Universe -> return (showString "U")
  El t -> showTermM i t


instance Show Type where
  showsPrec i t = runLFreshM (showTypeM i t)

instance Alpha a => Alpha (MetaVar a)
instance Alpha a => Alpha (Const a)
instance Alpha Term
instance Alpha Type

instance Subst Term Term where
  isvar (Var x) = Just (SubstName x)
  isvar _ = Nothing

instance Subst Term Type

instance Subst Term (MetaVar Term)
instance Subst Term (Const Term)
