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
  Atom Unique String NameGen
  

instance Eq Atom where
  -- We only compare the unique identifier, because the name
  -- suggestions may be large or even infinite.
  Atom x n ng == Atom x' n' ng' = x == x'

-- | User code should /not/ explicitly compare atoms for relative
-- ordering, because this is not referentially transparent (can be
-- unsound).  However, we define an 'Ord' instance for atoms anyway,
-- because it permits atoms to be used as keys in 'Set's and 'Map's.
instance Ord Atom where
  -- We only compare the unique identifier, because the name
  -- suggestions may be large or even infinite.
  compare (Atom x n ng) (Atom x' n' ng') = compare x x'

instance Show Atom where
  show = atom_show

-- ----------------------------------------------------------------------
-- ** Basic operations on atoms

-- | Return the name of an atom.
atom_show :: Atom -> String
atom_show (Atom x n ng) = n

-- | Return the suggested names of an atom.
atom_names :: Atom -> NameGen
atom_names (Atom x n ng) = ng

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
with_fresh_atom_named_namegen :: String -> NameGen -> (Atom -> a) -> a
with_fresh_atom_named_namegen n ng body =
  with_unique (\x -> body (Atom x n ng))
  
-- | Create a fresh atom with the given name suggestion.
-- 
-- The call to 'global_new' is done lazily, so an actual concrete name
-- will only be computed on demand.
with_fresh_atom_namegen :: NameGen -> (Atom -> a) -> a
with_fresh_atom_namegen ng body =
  with_fresh_atom_named_namegen (global_new ng) ng body
