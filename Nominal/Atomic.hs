module Nominal.Atomic where

import Prelude hiding ((.))

import Nominal.ConcreteNames
import Nominal.Atoms
import Nominal.Nominal
import Nominal.NominalSupport
import Nominal.Bindable


-- ----------------------------------------------------------------------
-- * The 'Atomic' class

-- | A type class for atom types. There are two suggested ways users can
-- generate additional types of atoms.
--
-- 1. By defining some new empty type /X/ that is an instance of
-- 'AtomKind'.  Optionally, a list of suggested names for the new
-- atoms can be provided.  (These will be used as the names of bound
-- variables unless otherwise specified). Then 'AtomOfKind' /X/ is a
-- new type of atoms.
-- 
-- > data X
-- > instance AtomKind X where
-- >   suggested_names = ["x", "y", "z"]
-- > newtype MyName = AtomOfKind X
-- 
-- 2. By cloning an existing 'Atomic' type, deriving 'Atomic',
-- 'Nominal', 'NominalSupport', 'NominalShow', 'Eq', and 'Ord', and
-- defining a 'Show' instance:
--
-- > {-# LANGUAGE GeneralizedNewtypeDeriving #-}
-- >
-- > newtype Variable = Variable Atom
-- >   deriving (Atomic, Nominal, NominalSupport, NominalShow, Eq, Ord)
-- > 
-- > instance Show Variable where
-- >   showsPrec = nominal_showsPrec
class (Nominal a, NominalSupport a, Eq a, Ord a, Show a, Bindable a) => Atomic a where
  to_atom :: a -> Atom
  from_atom :: Atom -> a

  -- | The default variable names for the atom type.
  names :: a -> NameSuggestion

show_atomic :: (Atomic a) => a -> String
show_atomic a = show_atom (to_atom a)

to_bindatom :: (Atomic a, Nominal t) => Bind a t -> BindAtom t
to_bindatom body = open body $ \a t -> atom_abst (to_atom a) t

from_bindatom :: (Atomic a, Nominal t) => BindAtom t -> Bind a t
from_bindatom body = atom_open body $ \a t -> (from_atom a . t)

instance Atomic Atom where
  to_atom = id
  from_atom = id
  names a = default_names

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

-- | A convenience function for constructing binders. 
--
-- > bind (\x -> t)
--
-- is a convenient way to write the atom abstraction (x.t),
-- where /x/ is a fresh variable.
bind :: (Atomic a, Nominal t) => (a -> t) -> Bind a t
bind body = bind_namelist ns body
  where
    ns = names (un body)
    un :: (a -> t) -> a
    un = undefined

-- | A version of 'bind' that also takes a suggested name for the bound atom.
bind_named :: (Atomic a, Nominal t) => String -> (a -> t) -> Bind a t
bind_named n = bind_namelist [n]

-- | A version of 'bind' that also take a list of suggested names for the bound atom.
bind_namelist :: (Atomic a, Nominal t) => NameSuggestion -> (a -> t) -> Bind a t
bind_namelist ns f = with_fresh_namelist ns (\x -> x . f x)

-- ----------------------------------------------------------------------
-- * High-level functions

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
-- we must have /a/ # /body/ (see Pitts 2002 for more details on what
-- this means). Haskell does not enforce this restriction, but if a
-- program violates this, referential transparency may be violated,
-- which may, in the worst case, lead to unsound compiler
-- optimizations and undefined behavior.

-- Implementation note: the use of 'unsafePerformIO' makes this
-- function not referentially transparent. For example, we have
--
-- > with_fresh id /= with_fresh id.
--
-- However, if the above-mentioned correctness criterion is satisfied,
-- then the programs will be referentially transparent (and all
-- definable functions will be equivariant).
with_fresh :: (Atomic a) => (a -> t) -> t
with_fresh body = with_fresh_namelist ns body
  where
    ns = names (un body)
    un :: (a -> t) -> a
    un = undefined

-- | A version of 'with_fresh' that permits a suggested name to be
-- given to the atom. The name is only a suggestion, and will be
-- changed, if necessary, to avoid clashes.
with_fresh_named :: (Atomic a) => String -> (a -> t) -> t
with_fresh_named n body =
  with_fresh_atom_named n (\a -> body (from_atom a))

-- | A version of 'with_fresh' that permits a list of suggested names
-- to be specified. The first suitable name in the list will be used
-- if possible.
with_fresh_namelist :: (Atomic a) => NameSuggestion -> (a -> t) -> t
with_fresh_namelist ns body =
  with_fresh_atom_namelist ns (\a -> body (from_atom a))
