module Cofibration (
  Atom,
  World, emptyWorld, newAtom,
  Cof, implies, fromAtom,
  Cases, pattern EmptyCases, pattern SingleCase, select) where
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import Data.List (intercalate)
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

data World = World {
  atoms :: IM.IntMap String,
  relations :: IM.IntMap Cof,
  nextAtom :: !Int
} deriving Show

emptyWorld :: World
emptyWorld = World IM.empty IM.empty 0

newAtom :: String -> Cof -> World -> (Atom, World)
newAtom name p w =
  let
    i = nextAtom w
    a = Atom name i in
    (a, w {
      atoms = IM.insert i name (atoms w),
      relations = IM.insert i p (relations w),
      nextAtom = i + 1
    })

newtype Cof = Cof (Ignore (IM.IntMap String)) -- a list for conjunctions
  deriving (Generic)
instance Show Cof where
  show (Cof p) = "⟨" ++
    intercalate " ∧ " (map snd $ IM.toList (unignore p))
    ++ "⟩"

instance Alpha Cof
instance Subst a Cof

instance Eq Cof where
  Cof p == Cof q = -- coarse equality
    let
      u = IM.keysSet (unignore p)
      v = IM.keysSet (unignore q)
    in
      u == v

instance Semigroup Cof where
  Cof p <> Cof q = Cof $ ignore $ IM.union (unignore p) (unignore q)

instance Monoid Cof where
  mempty = Cof (ignore IM.empty)

fromAtom :: Atom -> Cof
fromAtom (Atom s i) = Cof (ignore $ IM.singleton i s)

--         W     ;  Phi |- Psi true
implies :: World -> Cof -> Cof -> Bool
implies w (Cof p) (Cof q) = let
  Cof impls = mconcat $
    map (\k -> IM.findWithDefault mempty k $ relations w) $
    IM.keys $ unignore p
  in IM.keysSet (unignore q) `IS.isSubsetOf`
    (IM.keysSet (unignore impls) `IS.union` IM.keysSet (unignore p))

newtype Cases a = Cases [(Cof, a)]
  deriving (Functor, Foldable, Traversable, Semigroup, Monoid, Show)
  -- a case split on a disjunction of cofibrations

pattern EmptyCases :: Cases a
pattern EmptyCases = Cases []

pattern SingleCase :: Cof -> a -> Cases a
pattern SingleCase p a = Cases [(p, a)]

--        W     ;  Phi |- case {} == ?
select :: World -> Cof -> Cases a -> Maybe a
select _ _ (Cases []) = Nothing
select w p (Cases ((q,a):cs)) =
  if implies w p q then
    Just a
  else
    select w p (Cases cs)

-- todo more efficient data structures
-- todo is it possible to simplify but not evaluate the branches?
