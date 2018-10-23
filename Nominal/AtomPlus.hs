{-# LANGUAGE TypeFamilies #-}

-- | This module provides 'AtomPlus', a type of atoms that are
-- equipped with additional information.

module Nominal.AtomPlus where

import Prelude hiding ((.))

import Nominal.ConcreteNames
import Nominal.Nominal
import Nominal.NominalSupport
import Nominal.NominalShow
import Nominal.Bindable
import Nominal.Atomic

-- ----------------------------------------------------------------------
-- * AtomPlus

-- | A type of atoms that are equipped with additional information.
-- The information should not itself be nominal. Examples are: bound
-- variables that are equipped with information about the binding
-- site; type variables that are equipped with flags or boolean
-- constraints.
--
-- Here, /a/ is an 'Atomic' instance, and /t/ is the type of the
-- additional information stored in the atom.
data AtomPlus a t = AtomPlus a t
  deriving (Show)

-- ----------------------------------------------------------------------
-- Instances

instance (Eq a) => Eq (AtomPlus a t) where
  -- We only compare the unique identifier, for efficiency.
  AtomPlus x t == AtomPlus x' t' = x == x'

instance (Ord a) => Ord (AtomPlus a t) where
  -- We only compare the unique identifier, for efficiency.
  compare (AtomPlus x t) (AtomPlus x' t') = compare x x'

instance (Nominal a) => Nominal (AtomPlus a t) where
  π • AtomPlus a t = AtomPlus (π • a) t

instance (NominalSupport a) => NominalSupport (AtomPlus a t) where
  support (AtomPlus x t) = support x

instance (NominalSupport a, Show a, Show t) => NominalShow (AtomPlus a t) where
  nominal_showsPrecSup = simple_showsPrecSup

instance (Bindable a) => Bindable (AtomPlus a t) where
  binding (AtomPlus a t) = (xs, g)
    where
      (xs, f) = binding a
      g xs = AtomPlus (f xs) t
  
-- ----------------------------------------------------------------------
-- ** Creation of fresh atoms in a scope

-- | Like 'with_fresh', but store an additional /t/ in the atom.
with_fresh_plus :: (Atomic a) => t -> (AtomPlus a t -> s) -> s
with_fresh_plus t k =
  with_fresh $ \a -> k (AtomPlus a t)
 
-- | Like 'with_fresh_named', but store an additional /t/ in the atom.
with_fresh_named_plus :: (Atomic a) => t -> String -> (AtomPlus a t -> s) -> s
with_fresh_named_plus t n k =
  with_fresh_named n $ \a -> k (AtomPlus a t)

-- | Like 'with_fresh_namelist', but store an additional /t/ in the atom.
with_fresh_namelist_plus :: (Atomic a) => t -> NameSuggestion -> (AtomPlus a t -> s) -> s
with_fresh_namelist_plus t n k =
  with_fresh_namelist n $ \a -> k (AtomPlus a t)
