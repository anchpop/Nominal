{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}

-- | This module provides the 'NominalSupport' type class. It consists
-- of those types for which the support can be calculated. With the
-- exception of function types, most 'Nominal' types are also
-- in 'NominalSupport'.
--
-- We also provide some generic programming so that instances of
-- 'NominalSupport' can be automatically derived in most cases.
--
-- This module exposes implementation details of the Nominal library,
-- and should not normally be imported. Users of the library should
-- only import the top-level module "Nominal".

module Nominal.NominalSupport where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import GHC.Generics

import Nominal.ConcreteNames
import Nominal.Atom
import Nominal.Nominal

-- ----------------------------------------------------------------------
-- * Literal strings

-- | A wrapper around strings. This is used to denote any literal
-- strings whose values should not clash with the names of bound
-- variables. For example, if a term contains a constant symbol /c/,
-- the name /c/ should not also be used as the name of a bound
-- variable. This can be achieved by marking the string with
-- 'Literal', like this
-- 
-- > data Term = Var Atom | Const (Literal String) | ...
--
-- Another way to use 'Literal' is in the definition of custom
-- 'NominalSupport' instances. See
-- <#CUSTOM "Defining custom instances"> for an example.

newtype Literal = Literal String
                deriving (Show)

instance Nominal Literal where
  (•) = basic_action

-- ----------------------------------------------------------------------
-- * Support

-- | Something to be avoided can be an atom or a string.
data Avoidee = A Atom | S String
             deriving (Eq, Ord, Show)

-- | This type provides an internal representation for the support of
-- a nominal term, i.e., the set of atoms (and constants) occurring in
-- it. This is an abstract type with no exposed structure. The only way
-- to construct a value of type 'Support' is to use the function
-- 'support'.
newtype Support = Support (Set Avoidee)

-- | The empty support.
support_empty :: Support
support_empty = Support Set.empty

-- | The union of a list of supports.
support_unions :: [Support] -> Support
support_unions xs = Support (Set.unions [ x | Support x <- xs ])

-- | The union of two supports.
support_union :: Support -> Support -> Support
support_union (Support x) (Support y) = Support (Set.union x y)

-- | Add an atom to the support.
support_insert :: Atom -> Support -> Support
support_insert a (Support x) = Support (Set.insert (A a) x)

-- | A singleton support.
support_atom :: Atom -> Support
support_atom a = Support (Set.singleton (A a))

-- | Delete an atom from the support.
support_delete :: Atom -> Support -> Support
support_delete a (Support s) = Support (Set.delete (A a) s)

-- | Delete a list of atoms from the support.
support_deletes :: [Atom] -> Support -> Support
support_deletes [] s = s
support_deletes (a:as) s = support_deletes as (support_delete a s)

-- | Add a literal string to the support.
support_string :: String -> Support
support_string s = Support (Set.singleton (S s))

-- | Convert the support to a list of strings.
strings_of_support :: Support -> Set String
strings_of_support (Support s) = Set.map name s where
  name (A a) = show a
  name (S s) = s
                 
-- ----------------------------------------------------------------------
-- * The NominalSupport class

-- | 'NominalSupport' is a subclass of 'Nominal' consisting of those
-- types for which the support can be calculated. With the notable
-- exception of function types, most 'Nominal' types are also
-- instances of 'NominalSupport'.
--
-- In most cases, instances of 'NominalSupport' can be automatically
-- derived. See <#DERIVING "Deriving generic instances"> for
-- information on how to do so, and
-- <#CUSTOM "Defining custom instances"> for how to write custom
-- instances.
class (Nominal t) => NominalSupport t where
  -- | Compute a set of atoms and strings that should not be used as
  -- the names of bound variables.
  support :: t -> Support

  default support :: (Generic t, GNominalSupport (Rep t)) => t -> Support
  support x = gsupport (from x)

-- ----------------------------------------------------------------------
-- * Open for printing

-- | A variant of 'open' which moreover chooses a name for the bound
-- atom that does not clash with any free name in its scope. This
-- function is mostly useful for building custom pretty-printers for
-- nominal terms. Except in pretty-printers, it is equivalent to
-- 'open'.
--
-- Usage:
--
-- > open_for_printing sup t (\x s sup' -> body)
--
-- Here, /sup/ = 'support' /t/. For printing to be efficient (roughly
-- O(/n/)), the support must be pre-computed in a bottom-up fashion,
-- and then passed into each subterm in a top-down fashion (rather
-- than re-computing it at each level, which would be O(/n/²)).  For
-- this reason, 'open_for_printing' takes the support of /t/ as an
-- additional argument, and provides /sup'/, the support of /s/, as an
-- additional parameter to the body.
--
-- The correct use of this function is subject to
-- <#CONDITION Pitts's freshness condition>.
atom_open_for_printing :: (Nominal t) => Support -> BindAtom t -> (Atom -> t -> Support -> s) -> s
atom_open_for_printing sup t@(BindAtom ng f) k =
  with_fresh_atom_named n ng (\a -> k a (force (f a)) (sup' a))
  where
    n = rename_fresh (strings_of_support sup) ng
    sup' a = support_insert a sup

-- ----------------------------------------------------------------------
-- * NominalSupport instances

-- $ Most of the time, instances of 'NominalSupport' should be derived using
-- @deriving (Generic, NominalSupport)@, as in this example:
--
-- > {-# LANGUAGE DeriveGeneric #-}
-- > {-# LANGUAGE DeriveAnyClass #-}
-- >
-- > data Term = Var Atom | App Term Term | Abs (Bind Atom Term)
-- >   deriving (Generic, NominalSupport)
--
-- In the case of non-nominal types (typically base types such as
-- 'Double'), a 'NominalSupport' instance can be defined using
-- 'basic_support':
--
-- > instance NominalSupport MyType where
-- >   support = basic_support

-- | A helper function for defining 'NominalSupport' instances
-- for non-nominal types.
basic_support :: t -> Support
basic_support t = support ()

-- Base cases

instance NominalSupport Atom where
  support = support_atom

instance NominalSupport Bool where
  support = basic_support

instance NominalSupport Integer where
  support = basic_support

instance NominalSupport Int where
  support = basic_support

instance NominalSupport Char where
  support = basic_support

instance NominalSupport Double where
  support = basic_support

instance NominalSupport Float where
  support = basic_support

instance NominalSupport Ordering where
  support = basic_support

instance NominalSupport (Basic t) where
  support = basic_support

instance NominalSupport Literal where
  support (Literal s) = support_string s

-- Generic instances

instance (NominalSupport t) => NominalSupport [t]
instance NominalSupport ()
instance (NominalSupport t, NominalSupport s) => NominalSupport (t,s)
instance (NominalSupport t, NominalSupport s, NominalSupport r) => NominalSupport (t,s,r)
instance (NominalSupport t, NominalSupport s, NominalSupport r, NominalSupport q) => NominalSupport (t,s,r,q)
instance (NominalSupport t, NominalSupport s, NominalSupport r, NominalSupport q, NominalSupport p) => NominalSupport (t,s,r,q,p)
instance (NominalSupport t, NominalSupport s, NominalSupport r, NominalSupport q, NominalSupport p, NominalSupport o) => NominalSupport (t,s,r,q,p,o)
instance (NominalSupport t, NominalSupport s, NominalSupport r, NominalSupport q, NominalSupport p, NominalSupport o, NominalSupport n) => NominalSupport (t,s,r,q,p,o,n)
instance (NominalSupport a) => NominalSupport (Maybe a)
instance (NominalSupport a, NominalSupport b) => NominalSupport (Either a b)


-- Special instances

instance (NominalSupport t) => NominalSupport (BindAtom t) where
  support (BindAtom ng f) =
    with_fresh_atom ng (\a -> support_delete a (support (f a)))

instance (NominalSupport t) => NominalSupport (Defer t) where
  support t = support (force t)

instance (Ord k, NominalSupport k, NominalSupport v) => NominalSupport (Map k v) where
  support map = support (Map.toList map)

instance (Ord k, NominalSupport k) => NominalSupport (Set k) where
  support set = support (Set.toList set)

-- ----------------------------------------------------------------------
-- * Generic programming for NominalSupport

-- | A version of the 'NominalSupport' class suitable for generic programming.
class GNominalSupport f where
  gsupport :: f a -> Support

instance GNominalSupport V1 where
  gsupport x = undefined -- Does not occur, because V1 is an empty type.

instance GNominalSupport U1 where
  gsupport U1 = support_empty

instance (GNominalSupport a, GNominalSupport b) => GNominalSupport (a :*: b) where
  gsupport (a :*: b) = support_union (gsupport a) (gsupport b)

instance (GNominalSupport a, GNominalSupport b) => GNominalSupport (a :+: b) where
  gsupport (L1 x) = gsupport x
  gsupport (R1 x) = gsupport x

instance (GNominalSupport a) => GNominalSupport (M1 i c a) where
  gsupport (M1 x) = gsupport x

instance (NominalSupport a) => GNominalSupport (K1 i a) where
  gsupport (K1 x) = support x
