-- | This module provides a type of atoms. An atom is a globally
-- unique identifier that also has a concrete name, as well as
-- additional name suggestions (in case it must be renamed).

module Nominal.Atoms where

import Data.Unique

import Nominal.Unsafe
import Nominal.ConcreteNames

-- ----------------------------------------------------------------------
-- * Atoms

-- | An atom is a globally unique, opaque value with a concrete name
-- and some optional name suggestions.
data Atom = Atom Unique String NameSuggestion

instance Eq Atom where
  -- We only compare the unique identifier, because the name
  -- suggestions may be large or even infinite.
  Atom x n ns == Atom x' n' ns' = x == x'

instance Ord Atom where
  -- We only compare the unique identifier, because the name
  -- suggestions may be large or even infinite.
  compare (Atom x n ns) (Atom x' n' ns') = compare x x'

instance Show Atom where
  show = show_atom

-- ----------------------------------------------------------------------
-- ** Basic operations on atoms

-- | Return the name of an atom.
show_atom :: Atom -> String
show_atom (Atom x n ns) = n

-- | Return the suggested names of an atom.
atom_names :: Atom -> NameSuggestion
atom_names (Atom x n ns) = ns

-- | Make sure the atom has name suggestions, by adding the specified
-- ones if none are present.
add_default_names :: NameSuggestion -> Atom -> Atom
add_default_names ns (Atom x n []) = Atom x n ns
add_default_names ns (Atom x n ns') = Atom x n ns'

-- ----------------------------------------------------------------------
-- ** Creation of fresh atoms in a scope

-- | Create a fresh atom with the given name and name suggestions.
with_fresh_atom_named_namelist :: String -> NameSuggestion -> (Atom -> a) -> a
with_fresh_atom_named_namelist n ns body =
  with_unique (\x -> body (Atom x n ns))
  
-- | Create a fresh atom with the given name suggestion.
-- 
-- The call to 'global_new' is done lazily, so an actual concrete name
-- will only be computed on demand.
with_fresh_atom_namelist :: NameSuggestion -> (Atom -> a) -> a
with_fresh_atom_namelist ns body =
  with_fresh_atom_named_namelist (global_new ns) ns body

-- | Create a fresh atom with the given concrete name.
with_fresh_atom_named :: String -> (Atom -> a) -> a
with_fresh_atom_named n body =
  with_fresh_atom_named_namelist n [n] body

-- ----------------------------------------------------------------------
-- * Multiple atom types

-- | The type class 'AtomKind' requires a single method, which is
-- moreover optional: a list of suggested names for this kind of atom.
-- For example:
--
-- > data VarName
-- > instance AtomKind VarName where suggested_names a = ["x", "y", "z"]
--
-- > data TypeName
-- > instance AtomKind TypeName where suggested_names a = ["a", "b", "c"]
--
-- It is possible to have infinitely many kinds of atoms, for example:
--
-- > data Zero
-- > data Succ a
-- > instance AtomKind Zero
-- > instance AtomKind (Succ a)
--
-- Then Zero, Succ Zero, Succ (Succ Zero), etc., will all be atom kinds.
class AtomKind a where
  suggested_names :: a -> NameSuggestion
  suggested_names a = default_names

-- | The type of atoms of a given kind. For example:
--
-- > type Variable = AtomOfKind VarName
-- > type Type = AtomOfKind TypeName
newtype AtomOfKind a = AtomOfKind Atom
  deriving (Eq, Ord)

