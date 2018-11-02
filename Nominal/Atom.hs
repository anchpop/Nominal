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
-- ** Creation of fresh atoms globally

-- | Globally create a fresh atom with the given name and name
-- suggestions.
fresh_atom_named :: String -> NameGen -> IO Atom
fresh_atom_named n ng = do
  x <- newUnique
  return (Atom x n ng)

-- | Globally create a fresh atom with the given name suggestions.
fresh_atom :: NameGen -> IO Atom
fresh_atom ng = do
  n <- global_new_io ng
  fresh_atom_named n ng

-- ----------------------------------------------------------------------
-- ** Creation of fresh atoms in a scope

-- | Create a fresh atom with the given name and name suggestions.  To
-- ensure soundness, the created atom must not escape the body of the
-- 'Nominal.Atomic.with_fresh' block. Otherwise, referential
-- transparency may be violated. For example,
--
-- > with_fresh id != with_fresh id.
--
-- See the documentation of 'Nominal.Atomic.with_fresh' for more
-- information on the correctness criterion.
with_fresh_atom_named :: String -> NameGen -> (Atom -> a) -> a
with_fresh_atom_named n ng body =
  with_unique (\x -> body (Atom x n ng))

-- | Create a fresh atom with the given name suggestion.
--
-- Here, the call to 'global_new' is performed lazily (outside of the
-- 'IO' monad), so an actual concrete name will only be computed on
-- demand.
with_fresh_atom :: NameGen -> (Atom -> a) -> a
with_fresh_atom ng body =
  with_fresh_atom_named (global_new ng) ng body

