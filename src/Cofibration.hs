module Cofibration where
import GHC.Generics (Generic)
import Unbound.Generics.LocallyNameless

-- Decide the theory of meet-semilattices with generators
-- and relations of the form  p = expr  and  p ≤ expr.

data Atom = Atom String !Int deriving Generic
instance Alpha Atom
instance Eq Atom where
  Atom _ p == Atom _ q = p == q
instance Show Atom where
  show (Atom p _) = p

type Cof = [Atom] -- a list for conjunctions
type World = [Atom] -- all the declared atoms and relations between them

type Cases a = [(Cof, a)] -- a case split on a disjunction of cofibrations
