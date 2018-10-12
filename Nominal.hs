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
import GHC.Generics

import Nominal.ConcreteNames
import Nominal.Atom
import Nominal.Permutation
import Nominal.Nominal
import Nominal.NominalSupport
import Nominal.Bindable
import Nominal.Atomic
import Nominal.NominalShow
import Nominal.AtomPlus

