{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

-- | This module provides the class 'Atomic', which generalizes the
-- type 'Atom'. The purpose of this is to allow users to define more
-- than one type of atoms.

module Nominal.Atomic where

import Prelude hiding ((.))
import GHC.Generics

import Nominal.ConcreteNames
import Nominal.Atom
import Nominal.Nominal
import Nominal.NominalSupport
import Nominal.Bindable

-- ----------------------------------------------------------------------
-- * The 'Atomic' class

-- | A type class for atom types.
--
-- The suggested way to define a type of atoms is to define a new
-- empty type /t/ that is an instance of 'AtomKind'.  Optionally, a
-- list of suggested names for the new atoms can be provided.  (These
-- will be used as the names of bound variables unless otherwise
-- specified). Then 'AtomOfKind' /t/ is a new type of atoms.
-- 
-- > data VarName
-- > instance AtomKind VarName where
-- >   suggested_names = ["x", "y", "z"]
-- > newtype Variable = AtomOfKind VarName
class (Nominal a, NominalSupport a, Eq a, Ord a, Show a, Bindable a) => Atomic a where
  to_atom :: a -> Atom
  from_atom :: Atom -> a

  -- | The default variable names for the atom type.
  names :: a -> NameGen

instance Atomic Atom where
  to_atom = id
  from_atom = id
  names a = default_namegen

-- ----------------------------------------------------------------------
-- ** Basic operations

-- | Return the name of an atom.
atomic_show :: (Atomic a) => a -> String
atomic_show a = atom_show (to_atom a)

-- ----------------------------------------------------------------------
-- ** Creation of fresh atoms in a scope

-- | Perform a computation in the presence of a fresh atom. For
-- soundness, the programmer must ensure that the atom created does
-- not escape the body of the 'with_fresh' block. Thus, the following
-- uses are permitted:
--   
-- > with_fresh (\a -> f a == g a)
-- > with_fresh (\a -> a . f a b c)
--
-- Here is an example of what is /not/ permitted:
--
-- > with_fresh (\a -> a)
--
-- Technically, the correctness condition is that in an application
--
-- > with_fresh (\a -> body),
--
-- we must have /a/ # /body/ (see [Pitts 2002] for more details on
-- what this means). Haskell does not enforce this restriction, but if
-- a program violates it, referential transparency may not hold, which
-- may, in the worst case, lead to unsound compiler optimizations and
-- undefined behavior.
with_fresh :: (Atomic a) => (a -> t) -> t
with_fresh body = with_fresh_namelist [] body

-- | A version of 'with_fresh' that permits a suggested name to be
-- given to the atom. The name is only a suggestion, and will be
-- changed, if necessary, to avoid clashes.
--
-- This function is subject to the same correctness condition as
-- 'with_fresh'.
with_fresh_named :: (Atomic a) => String -> (a -> t) -> t
with_fresh_named n body =
  with_fresh_atom_named_namegen n ng (\a -> body (from_atom a))
  where
    ng = names (un body)
    un :: (a -> t) -> a
    un = undefined

-- | A version of 'with_fresh' that permits a list of suggested names
-- to be specified. The first suitable name in the list will be used
-- if possible.
--
-- This function is subject to the same correctness condition as
-- 'with_fresh'.
with_fresh_namelist :: (Atomic a) => NameSuggestion -> (a -> t) -> t
with_fresh_namelist ns body =
  with_fresh_atom_namegen ng (\a -> body (from_atom a))
  where
    NameGen ns1 ex = names (un body)
    ns2 = if null ns then ns1 else ns
    ng = NameGen ns2 ex
    un :: (a -> t) -> a
    un = undefined

-- ----------------------------------------------------------------------
-- ** Convenience functions for abstraction

-- | A convenience function for constructing binders. We can write
--
-- > bind (\x -> t)
--
-- to denote the atom abstraction (x.t), where /x/ is a fresh atom.
bind :: (Atomic a, Nominal t) => (a -> t) -> Bind a t
bind f = with_fresh (\x -> x . f x)

-- | A version of 'bind' that also takes a suggested name for the bound atom.
bind_named :: (Atomic a, Nominal t) => String -> (a -> t) -> Bind a t
bind_named n f = with_fresh_named n (\x -> x . f x)

-- | A version of 'bind' that also take a list of suggested names for
-- the bound atom.
bind_namelist :: (Atomic a, Nominal t) => NameSuggestion -> (a -> t) -> Bind a t
bind_namelist ns f = with_fresh_namelist ns (\x -> x . f x)

-- ----------------------------------------------------------------------
-- ** Merging

-- | Convert an atomic binding to an atom binding.
to_bindatom :: (Atomic a, Nominal t) => Bind a t -> BindAtom t
to_bindatom body = open body $ \a t -> atom_abst (to_atom a) t

-- | Convert an atom binding to an atomic binding.
from_bindatom :: (Atomic a, Nominal t) => BindAtom t -> Bind a t
from_bindatom body = atom_open body $ \a t -> (from_atom a . t)

-- | Sometimes, it is necessary to open two abstractions, using the
-- /same/ fresh name for both of them. An example of this is the
-- typing rule for lambda abstraction in dependent type theory:
--
-- >           Gamma, x:t  |-  e : s
-- >      ------------------------------------
-- >        Gamma |-  Lam (x.e) : Pi t (x.s)
--
-- In the bottom-up reading of this rule, we are given the terms @Lam@
-- /body/ and @Pi@ /t/ /body'/, and we require a fresh name /x/ and
-- terms /e/, /s/ such that /body/ = (/x/./e/) and /body'/ =
-- (/x/./s/).  Crucially, the same atom /x/ should be used in both /e/
-- and /s/, because we subsequently need to check that /e/ has type
-- /s/ in some scope that is common to /e/ and /s/.
--
-- The 'merge' primitive permits us to deal with such situations.  Its
-- defining property is
--
-- > merge (x.e) (x.s) = (x.(e,s)).
--
-- We can therefore solve the above problem:
--
-- > open (merge body body') (\x (e,s) -> .....)
--
-- Moreover, the 'merge' primitive can be used to define other
-- merge-like functionality. For example, it is easy to define a
-- function
--
-- > merge_list :: (Atomic a, Nominal t) => [Bind a t] -> Bind a [t]
--
-- in terms of it.
--
-- Semantically, the 'merge' operation implements the isomorphism of
-- nominal sets [A]T x [A]S = [A](T x S).
--
-- If /x/ and /y/ are atoms with user-suggested concrete names and
--
-- > (z.(t',s')) = merge (x.t) (y.s),
--
-- then /z/ will be preferably given the concrete name of /x/, but the
-- concrete name of /y/ will be used if the name of /x/ would cause a
-- clash.
merge :: (Atomic a, Nominal t, Nominal s) => Bind a t -> Bind a s -> Bind a (t,s)
merge at as = from_bindatom (atom_merge (to_bindatom at) (to_bindatom as))

-- ----------------------------------------------------------------------
-- * Multiple atom types

-- | An atom kind is a type-level constant (typically an empty type)
-- that is an instance of the 'AtomKind' class. An atom kind is
-- optionally equipped with a list of suggested names for this kind of
-- atom.  For example:
--
-- > data VarName
-- > instance AtomKind VarName where
-- >   suggested_names _ = ["x", "y", "z"]
--
-- > data TypeName
-- > instance AtomKind TypeName where
-- >   suggested_names _ = ["a", "b", "c"]
--
-- It is possible to have infinitely many atom kinds, for example:
--
-- > data Zero
-- > data Succ a
-- > instance AtomKind Zero
-- > instance AtomKind (Succ a)
--
-- Then Zero, Succ Zero, Succ (Succ Zero), etc., will all be atom kinds.
class AtomKind a where
  -- | An optional list of default names for this kind of atom.
  suggested_names :: a -> NameSuggestion
  suggested_names a = default_names

  -- | An optional function for generating infinitely many distinct
  -- names from a finite list of suggestions. The default behavior is
  -- to append numerical subscripts. For example, the names @[x, y,
  -- z]@ are by default expanded to @[x, y, z, x₁, y₁, z₁, x₂, y₂,
  -- …]@, using Unicode for the subscripts.  To use a a different
  -- naming convention, redefine 'expand_names'.
  -- 
  -- It is not strictly necessary for all of the returned names to be
  -- distinct; it is sufficient that there are infinitely many
  -- distinct ones.
  --
  -- Example: the following generates new variable names by appending
  -- primes instead of subscripts:
  --
  -- > expand_names _ xs = ys
  -- >   where ys = xs ++ map (++ "'") ys
  expand_names :: a -> NameSuggestion -> [String]
  expand_names a = expand_default

-- | The type of atoms of a given kind. For example:
--
-- > type Variable = AtomOfKind VarName
-- > type Type = AtomOfKind TypeName
newtype AtomOfKind a = AtomOfKind Atom
  deriving (Eq, Ord, Generic, Bindable)

instance (AtomKind a) => Show (AtomOfKind a) where
  show = atomic_show

instance (AtomKind a) => Nominal (AtomOfKind a) where
  π • (AtomOfKind a) = AtomOfKind (π • a)

instance (AtomKind a) => NominalSupport (AtomOfKind a) where
  support (AtomOfKind a) = support a

instance (AtomKind a) => Atomic (AtomOfKind a) where
  to_atom (AtomOfKind a) = a
  from_atom a = AtomOfKind a
  names f = atomofkind_names f

-- | Return the list of default names associated with the /kind/ of
-- the given atom (not the name(s) of the atom itself).
atomofkind_names :: (AtomKind a) => AtomOfKind a -> NameGen
atomofkind_names f = NameGen ns ex
  where
    ns = suggested_names (un f)
    ex = expand_names (un f)
    un :: AtomOfKind a -> a
    un = undefined
