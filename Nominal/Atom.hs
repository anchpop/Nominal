-- | This module provides a type of atoms. An atom is a globally
-- unique identifier that also has a concrete name, as well as
-- additional name suggestions (in case it must be renamed).

module Nominal.Atom where

import Data.Unique

import Nominal.Unsafe
import Nominal.ConcreteNames

-- ----------------------------------------------------------------------
-- * Atoms

-- | An atom is a globally unique, opaque value.
data Atom =
  -- | An atom consists of a unique identifier, a concrete name, and
  -- some optional name suggestions.
  Atom Unique String NameSuggestion
  

instance Eq Atom where
  -- We only compare the unique identifier, because the name
  -- suggestions may be large or even infinite.
  Atom x n ns == Atom x' n' ns' = x == x'

-- | User code should /not/ explicitly compare atoms for relative
-- ordering, because this is not referentially transparent (can be
-- unsound).  However, we define an 'Ord' instance for atoms anyway,
-- because it permits atoms to be used as keys in 'Set's and 'Map's.
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

-- Implementation note: the use of 'unsafePerformIO' in 'with_unique'
-- makes this function not referentially transparent. For example, we
-- have
--
-- > with_fresh id /= with_fresh id.
--
-- However, if the above-mentioned correctness criterion is satisfied,
-- then the programs will be referentially transparent (and all
-- definable functions will be equivariant).
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

