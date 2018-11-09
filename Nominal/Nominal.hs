{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}

-- | This module provides the 'Nominal' type class. A type is
-- 'Nominal' if the group of finitely supported permutations of atoms
-- acts on it. We can abstract over an atom in such a type.
--
-- We also provide some generic programming so that instances of
-- 'Nominal' can be automatically derived in most cases.
--
-- This module exposes implementation details of the Nominal library,
-- and should not normally be imported. Users of the library should
-- only import the top-level module "Nominal".

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

-- | A type is nominal if the group of finitely supported permutations
-- of atoms acts on it.
--
-- In most cases, instances of 'Nominal' can be automatically
-- derived. See <#DERIVING "Deriving generic instances"> for
-- information on how to do so, and
-- <#CUSTOM "Defining custom instances"> for how to write custom
-- instances.
class Nominal t where
  -- | Apply a permutation of atoms to a term.
  (•) :: NominalPermutation -> t -> t

  default (•) :: (Generic t, GNominal (Rep t)) => NominalPermutation -> t -> t
  π • x = to (gbullet π (from x))

-- ----------------------------------------------------------------------
-- * Deferred permutation

-- | 'Defer' /t/ is the type /t/, but equipped with an explicit substitution.
-- This is used to cache substitutions so that they can be optimized
-- and applied all at once.
data Defer t = Defer NominalPermutation t

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
-- modulo alpha-equivalence. For full technical details on what this
-- means, see Definition 4 of [Pitts 2002].
--
-- Implementation note: we currently use an HOAS encoding, as this
-- turns out to be far more efficient (both in time and memory usage)
-- than the alternatives. An important invariant of the HOAS encoding
-- is that the underlying function must only be applied to /fresh/
-- atoms.
data BindAtom t = BindAtom NameGen (Atom -> Defer t)

-- | Atom abstraction: 'atom_abst' /a/ /t/ represents the equivalence
-- class of pairs (/a/,/t/) modulo alpha-equivalence. We first define
-- this for 'Atom' and later generalize to other 'Atomic' types.
atom_abst :: Atom -> t -> BindAtom t
atom_abst a t = BindAtom (atom_names a) (\x -> Defer (perm_swap a x) t)

-- | Destructor for atom abstractions. If /m/ = /y/./s/, the term
-- 
-- > open m (\x t -> body)
--
-- binds /x/ to a fresh name and /t/ to a term such that /x/./t/ = /y/./s/.
-- 
-- The correct use of this function is subject to Pitts's freshness
-- condition.
atom_open :: (Nominal t) => BindAtom t -> (Atom -> t -> s) -> s
atom_open (BindAtom ng f) k =
  with_fresh_atom ng (\a -> k a (force (f a)))

instance (Nominal t, Eq t) => Eq (BindAtom t) where
  b1 == b2 = atom_open (atom_merge b1 b2) $ \a (t1,t2) -> t1 == t2

instance (Nominal t) => Nominal (BindAtom t) where
  π • (BindAtom n f) = BindAtom n (\x -> π • (f x))

-- | Merge two abstractions. The defining property is
--
-- > merge (x.t) (x.s) = (x.(t,s))
atom_merge :: (Nominal t, Nominal s) => BindAtom t -> BindAtom s -> BindAtom (t,s)
atom_merge (BindAtom ng f) (BindAtom ng' g) = (BindAtom ng'' h) where
  ng'' = combine_names ng ng'
  h x = Defer perm_identity (force (f x), force (g x))

-- ----------------------------------------------------------------------
-- * Basic types

-- | A /basic/ or /non-nominal/ type is a type whose elements cannot
-- contain any atoms. Typical examples are base types, such as 'Integer'
-- or 'Bool', and other types constructed exclusively from them,
-- such as @['Integer']@ or @'Bool' -> 'Bool'@. On such types, the
-- nominal structure is trivial, i.e., @π • /x/ = /x/@ for all /x/.
--
-- For convenience, we define 'Basic' as a wrapper around such types,
-- which will automatically generate appropriate instances of
-- 'Nominal', 'NominalSupport', 'NominalShow', and 'Bindable'. You can
-- use it, for example, like this:
--
-- > type Term = Var Atom | Const (Basic Int) | App Term Term
--
-- Some common base types, including 'Bool', 'Char', 'Int', 'Integer',
-- 'Double', 'Float', and 'Ordering' are already instances of the
-- relevant type classes, and do not need to be wrapped in 'Basic'.
--
-- The use of 'Basic' can sometimes have a performance advantage. For
-- example, @'Basic' 'String'@ is a more efficient 'Nominal' instance
-- than 'String'. Although they are semantically equivalent, the use
-- of 'Basic' prevents having to traverse the string to check each
-- character for atoms that are clearly not there.
newtype Basic t = Basic t
  deriving (Show, Eq, Ord)

-- ----------------------------------------------------------------------
-- * Nominal instances

-- $ Most of the time, instances of 'Nominal' should be derived using
-- @deriving (Generic, Nominal)@, as in this example:
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
-- for non-nominal types.
basic_action :: NominalPermutation -> t -> t
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

instance Nominal Ordering where
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
instance (Nominal a) => Nominal (Maybe a)
instance (Nominal a, Nominal b) => Nominal (Either a b)


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
  gbullet :: NominalPermutation -> f a -> f a

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

