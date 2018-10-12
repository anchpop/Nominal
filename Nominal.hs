{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}

-- | A package for working with binders.

module Nominal (
  Atom,
  Atomic,
  with_fresh,
  with_fresh_named,
  with_fresh_namelist,
  bind,
  bind_named,
  bind_namelist,
  Nominal(..),
  Permutation,
  NominalSupport(..),
  NominalShow(..),
  Support,
  Literal(..),
  AtomKind(..),
  AtomOfKind,
  (∘),
  nominal_showsPrec,
  NameSuggestion,
  Bindable(..),
  merge,
  (.),
  AtomPlus(..),
  with_fresh_plus,
  with_fresh_named_plus,
  with_fresh_namelist_plus,
  module GHC.Generics
)
where

import Prelude hiding ((.))
import Data.Map (Map)
import qualified Data.Map as Map
import Data.List
import GHC.Generics

import Nominal.ConcreteNames
import Nominal.Atom
import Nominal.Permutation
import Nominal.Nominal
import Nominal.NominalSupport
import Nominal.Bindable
import Nominal.Atomic
import Nominal.NominalShow

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

instance (Nominal a) => Nominal (AtomPlus a t) where
  π • AtomPlus a t = AtomPlus (π • a) t

instance (Eq a) => Eq (AtomPlus a t) where
  -- We only compare the unique identifier, for efficiency.
  AtomPlus x t == AtomPlus x' t' = x == x'

instance (Ord a) => Ord (AtomPlus a t) where
  -- We only compare the unique identifier, for efficiency.
  compare (AtomPlus x t) (AtomPlus x' t') = compare x x'

instance (NominalSupport a) => NominalSupport (AtomPlus a t) where
  support (AtomPlus x t) = support x

instance (NominalSupport a, Show a, Show t) => NominalShow (AtomPlus a t) where
  nominal_showsPrecSup = simple_showsPrecSup

instance (Bindable a) => Bindable (AtomPlus a t) where
  data Bind (AtomPlus a t) s = BindAP t (Bind a s)
  bindable_action π (BindAP t body) = BindAP t (π • body)
  bindable_support (BindAP t body) = support body
  bindable_eq (BindAP t1 b1) (BindAP t2 b2) = open b1 $ \a _ -> AtomPlus a t1 == AtomPlus a t2 && b1 == b2
  abst (AtomPlus a t) body = BindAP t (abst a body)
  open (BindAP t body) k = open body $ \a s -> k (AtomPlus a t) s
  open_for_printing sup (BindAP t body) k = open_for_printing sup body $ \a s -> k (AtomPlus a t) s

with_fresh_plus :: (Atomic a) => t -> (AtomPlus a t -> s) -> s
with_fresh_plus t k =
  with_fresh $ \a -> k (AtomPlus a t)
 

with_fresh_named_plus :: (Atomic a) => t -> String -> (AtomPlus a t -> s) -> s
with_fresh_named_plus t n k =
  with_fresh_named n $ \a -> k (AtomPlus a t)

with_fresh_namelist_plus :: (Atomic a) => t -> NameSuggestion -> (AtomPlus a t -> s) -> s
with_fresh_namelist_plus t n k =
  with_fresh_namelist n $ \a -> k (AtomPlus a t)

-- ----------------------------------------------------------------------
-- * Generic programming

-- $ This allows the user to automatically derive 'Nominal',
-- 'NominalSupport', and 'NominalShow' instances. All the user has to
-- do is add the language options DeriveGeneric and DeriveAnyClass, and
-- add
--
-- > deriving (Generic, Nominal, NominalSupport, NominalShow)
--
-- to any nominal datatype.

