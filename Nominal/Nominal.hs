{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}

-- | This module provides the 'Nominal' type class. A type is
-- 'Nominal' if the group of finitely supported permutations of atoms
-- acts on it. We can abstract over an atom in such a type.
--
-- We also provide some generic programming so that instances of
-- 'Nominal' can be automatically derived in most cases.

module Nominal.Nominal where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import GHC.Generics

import Nominal.ConcreteNames
import Nominal.Atom
import Nominal.Permutation

-- ----------------------------------------------------------------------
-- * The Nominal class

-- | A type is 'Nominal' if the group of finitely supported
-- permutations of atoms acts on it. In most cases, instances of
-- 'Nominal' can be automatically derived. See
-- <#NOMINAL Nominal types> for more information on how to do so.
class Nominal t where
  -- | Apply a permutation of atoms to a term.
  (•) :: Permutation -> t -> t

  default (•) :: (Generic t, GNominal (Rep t)) => Permutation -> t -> t
  π • x = to (gbullet π (from x))

-- ----------------------------------------------------------------------
-- * Deferred permutation

-- | 'Defer' /t/ is the type /t/, but equipped with an explicit substitution.
-- This is used to cache substitutions so that they can be optimized
-- and applied all at once.
data Defer t = Defer Permutation t

-- | Apply a deferred permutation.
force :: (Nominal t) => Defer t -> t
force (Defer sigma t) = sigma • t

instance Nominal (Defer t) where
  -- This is where 'Defer' pays off. Rather than using 'force',
  -- we compile the permutations for later efficient use.
  π • (Defer sigma t) = Defer (perm_composeR π sigma) t
  
-- ----------------------------------------------------------------------
-- * Atom abstraction

-- | 'BindAtom' /t/ is the type of atom abstractions, denoted [a]t in
-- the nominal logic literature. Its elements are of the form (a.v)
-- modulo alpha-equivalence. For more details on what this means, see
-- Definition 4 of [Pitts 2002].

-- Implementation note: we currently use an HOAS encoding. It remains
-- to be seen whether this is efficient. An important invariant of the
-- HOAS encoding is that the underlying function must only be applied
-- to /fresh/ atoms.
-- 
-- It would also be possible to use a DeBruijn encoding or a nameful
-- encoding. It remains to be seen which encoding is the most
-- efficient in practice.
data BindAtom t = BindAtom NameSuggestion (Atom -> Defer t)

-- | Atom abstraction: 'atom_abst' /a/ /t/ represents the equivalence
-- class of pairs (/a/,/t/) modulo alpha-equivalence. We first define
-- this for 'Atom' and later generalize to other 'Atomic' types.
atom_abst :: Atom -> t -> BindAtom t
atom_abst a t = BindAtom (atom_names a) (\x -> Defer (perm_swap a x) t)

-- | Pattern matching for atom abstraction. In an ideal programming
-- idiom, we would be able to define a function on atom abstractions
-- like this:
--
-- > f (x.s) = body.
--
-- Haskell doesn't let us provide this syntax, but the 'open' function
-- provides the equivalent syntax
--
-- > f t = open t (\x s -> body).
--
-- To be referentially transparent and equivariant, the body is
-- subject to the same restriction as 'with_fresh', namely,
-- /x/ must be fresh for the body (in symbols /x/ # /body/).
atom_open :: (Nominal t) => BindAtom t -> (Atom -> t -> s) -> s
atom_open (BindAtom ns f) body =
  with_fresh_atom_namelist ns (\a -> body a (force (f a)))

instance (Nominal t, Eq t) => Eq (BindAtom t) where
  b1 == b2 = atom_open (atom_merge b1 b2) $ \a (t1,t2) -> t1 == t2

instance (Nominal t) => Nominal (BindAtom t) where
  π • (BindAtom n f) = BindAtom n (\x -> π • (f x))

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
atom_merge :: (Nominal t, Nominal s) => BindAtom t -> BindAtom s -> BindAtom (t,s)
atom_merge (BindAtom ns f) (BindAtom ns' g) = (BindAtom ns'' h) where
  ns'' = combine_names ns ns'
  h x = Defer perm_identity (force (f x), force (g x))

-- ----------------------------------------------------------------------
-- * Basic types

-- | A /basic/ or /non-nominal/ type is a type whose elements cannot
-- contain any atoms. Typical examples are base types, such as 'Integer'
-- or 'Bool', and other types constructed exclusively from them,
-- such as @['Integer']@ or @'Bool' -> 'Bool'@. On such types, the
-- nominal structure is trivial, i.e., @π • /x/ = /x/@ for all /x/.
--
-- For convenience, we define 'Basic' as a wrapper around such types,
-- which will automatically generate appropriate instances of
-- 'Nominal', 'NominalSupport', 'NominalShow', and 'Bindable'. You can
-- use it, for example, like this:
--
-- > type Term = Var Atom | Const (Basic Int) | App Term Term
--
-- Some common base types, including 'Bool', 'Char', 'Int',
-- 'Integer', 'Double', and 'Float', are already instances of the
-- relevant type classes, and do not need to be wrapped in 'Basic'.
newtype Basic t = Basic t
  deriving (Show, Eq, Ord)

-- ----------------------------------------------------------------------
-- * Nominal instances

-- $ Most of the time, instances of 'Nominal' should be derived using
-- @deriving (Generic, Nominal)@, as in this example:
--
-- > {-# LANGUAGE DeriveGeneric #-}
-- > {-# LANGUAGE DeriveAnyClass #-}
-- >
-- > data Term = Var Atom | App Term Term | Abs (Bind Atom Term)
-- >   deriving (Generic, Nominal)
--
-- In the case of non-nominal types (typically base types such as
-- 'Double'), a 'Nominal' instance can be defined using
-- 'basic_action':
--
-- > instance Nominal MyType where
-- >   (•) = basic_action

-- | A helper function for defining 'Nominal' instances
-- for /non-nominal types only/. It can be used like this:
--
-- > instance Nominal MyType where
-- >   (•) = basic_action
basic_action :: Permutation -> t -> t
basic_action π t = t

-- Base cases

instance Nominal Atom where
  (•) = perm_apply_atom

instance Nominal Bool where
  (•) = basic_action

instance Nominal Integer where
  (•) = basic_action

instance Nominal Int where
  (•) = basic_action

instance Nominal Char where
  (•) = basic_action

instance Nominal Double where
  (•) = basic_action

instance Nominal Float where
  (•) = basic_action

instance Nominal (Basic t) where
  (•) = basic_action

-- Generic instances

instance (Nominal t) => Nominal [t]
instance Nominal ()
instance (Nominal t, Nominal s) => Nominal (t,s)
instance (Nominal t, Nominal s, Nominal r) => Nominal (t,s,r)
instance (Nominal t, Nominal s, Nominal r, Nominal q) => Nominal (t,s,r,q)
instance (Nominal t, Nominal s, Nominal r, Nominal q, Nominal p) => Nominal (t,s,r,q,p)
instance (Nominal t, Nominal s, Nominal r, Nominal q, Nominal p, Nominal o) => Nominal (t,s,r,q,p,o)
instance (Nominal t, Nominal s, Nominal r, Nominal q, Nominal p, Nominal o, Nominal n) => Nominal (t,s,r,q,p,o,n)

-- Special instances

instance (Nominal t, Nominal s) => Nominal (t -> s) where
  π • f = \x -> π • (f (π' • x))
    where
      π' = perm_invert π

instance (Ord k, Nominal k, Nominal v) => Nominal (Map k v) where
  π • map = Map.fromList [ (π • k, π • v) | (k, v) <- Map.toList map ]

instance (Ord k, Nominal k) => Nominal (Set k) where
  π • set = Set.fromList [ π • k | k <- Set.toList set ]

-- ----------------------------------------------------------------------
-- * Generic programming for Nominal

-- | A version of the 'Nominal' class suitable for generic programming.
class GNominal f where
  gbullet :: Permutation -> f a -> f a

instance GNominal V1 where
  gbullet π x = undefined -- Does not occur, because V1 is an empty type.

instance GNominal U1 where
  gbullet π U1 = U1

instance (GNominal a, GNominal b) => GNominal (a :*: b) where
  gbullet π (a :*: b) = gbullet π a :*: gbullet π b

instance (GNominal a, GNominal b) => GNominal (a :+: b) where
  gbullet π (L1 x) = L1 (gbullet π x)
  gbullet π (R1 x) = R1 (gbullet π x)

instance (GNominal a) => GNominal (M1 i c a) where
  gbullet π (M1 x) = M1 (gbullet π x)

instance (Nominal a) => GNominal (K1 i a) where
  gbullet π (K1 x) = K1 (π • x)

