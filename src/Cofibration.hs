{-# LANGUAGE DeriveTraversable #-}
module Cofibration (
  Atom,
  World, emptyWorld,
  Cof, implies, fromAtom, unfoldMeta,
  Cases, pattern EmptyCases, pattern SingleCase, select) where
import qualified Data.IntMap as IM
import GHC.Generics (Generic)
import Unbound.Generics.LocallyNameless

-- Decide the theory of meet-semilattices with generators
-- and relations of the form  p = expr  and  p ≤ expr.
-- The first we can just delete immediately

data Atom = Atom String !Int deriving Generic
instance Eq Atom where
  Atom _ p == Atom _ q = p == q
instance Ord Atom where
  compare (Atom _ p) (Atom _ q) = compare p q
instance Show Atom where
  show (Atom p _) = p

-- todo more efficient data structures
data World = World {
  atoms :: IM.IntMap String ,
  relations :: [(Atom, Cof)]
} deriving Show

emptyWorld :: World
emptyWorld = World IM.empty []

newtype Cof = Cof (Ignore (IM.IntMap String)) -- a list for conjunctions
  deriving (Generic, Show)
instance Alpha Cof
instance Subst a Cof

instance Semigroup Cof where
  Cof p <> Cof q = Cof $ ignore $ IM.union (unignore p) (unignore q)

instance Monoid Cof where
  mempty = Cof (ignore IM.empty)

fromAtom :: Atom -> Cof
fromAtom (Atom s i) = Cof (ignore $ IM.singleton i s)

unfoldMeta :: Cof
unfoldMeta = fromAtom $ Atom "?" (-1)

--         W     ;  Phi |- Psi true
implies :: World -> Cof -> Cof -> Bool
implies w p q = _

newtype Cases a = Cases [(Cof, a)]
  deriving (Functor, Foldable, Traversable, Semigroup, Monoid, Show)
  -- a case split on a disjunction of cofibrations

pattern EmptyCases :: Cases a
pattern EmptyCases = Cases []

pattern SingleCase :: Cof -> a -> Cases a
pattern SingleCase p a = Cases [(p, a)]

--        W     ;  Phi |- case {} == ?
select :: World -> Cof -> Cases a -> Maybe a
select = _

-- todo is it possible to simplify but not evaluate the branches?
