{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}

-- | This module provides the 'NominalSupport' type class. It consists
-- of those typesfor which the support can be calculated. With the
-- exception of function types, most 'Nominal' types are also
-- 'NominalSupport'.
--
-- We also provide some generic programming so that instances of
-- 'NominalSupport' can be automatically derived in most cases.

module Nominal.NominalSupport where

import Data.Set (Set)
import qualified Data.Set as Set
import GHC.Generics

import Nominal.Atoms
import Nominal.Nominal

-- ----------------------------------------------------------------------
-- * Literal strings

newtype Literal = Literal String
                deriving (Show)

instance Nominal Literal where
  π • t = t

-- ----------------------------------------------------------------------
-- * Support

-- | Something to be avoided can be an atom or a string.
data Avoidee = A Atom | S String
             deriving (Eq, Ord, Show)

-- | This type provides an internal representation for the support of
-- a nominal term, i.e., the set of atoms occurring in it. This is an
-- opaque type with no exposed structure. The only way to construct a
-- value of type 'Support' is to use the function 'support'.
newtype Support = Support (Set Avoidee)

support_empty :: Support
support_empty = Support Set.empty

support_unions :: [Support] -> Support
support_unions xs = Support (Set.unions [ x | Support x <- xs ])

support_union :: Support -> Support -> Support
support_union (Support x) (Support y) = Support (Set.union x y)

support_insert :: Atom -> Support -> Support
support_insert a (Support x) = Support (Set.insert (A a) x)

support_atom :: Atom -> Support
support_atom a = Support (Set.singleton (A a))

support_delete :: Atom -> Support -> Support
support_delete a (Support s) = Support (Set.delete (A a) s)

support_string :: String -> Support
support_string s = Support (Set.singleton (S s))

strings_of_support :: Support -> Set String
strings_of_support (Support s) = Set.map name s where
  name (A a) = show a
  name (S s) = s
                 
-- ----------------------------------------------------------------------
-- * The NominalSupport class

-- | 'NominalSupport' is a subclass of 'Nominal' consisting of those
-- types for which the support can be calculated. With the exception
-- of function types, most 'Nominal' types are also 'NominalSupport'.
--
-- Instances of 'NominalSupport' are usually defined by
-- straightforward recursive clauses. The recursive clauses must apply
-- 'support' to a tuple or list (or combination thereof) of immediate
-- subterms.
--
-- > instance NominalShow Term where
-- >   support (Var x) = support x
-- >   support (App t s) = support (t, s)
-- >   support (Abs t) = support t
-- >   support (MultiApp t args) = support (t, [args])
-- >   support Unit = support ()
--
-- If your nominal type uses additional constants, identifiers, or
-- reserved keywords that are not implemented as 'Atom's, but whose
-- names you wouldn't like to clash with the names of bound
-- variables, declare them with 'Literal' applied to a string:
--
-- >   support (Const str) = support (Literal str)
class (Nominal t) => NominalSupport t where
  -- | Compute a set of atoms and strings that should not be used as
  -- the names of bound variables.
  support :: t -> Support

  default support :: (Generic t, GNominalSupport (Rep t)) => t -> Support
  support x = gsupport (from x)

-- ----------------------------------------------------------------------
-- * Generic NominalSupport instances

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



