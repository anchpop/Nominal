-- | An efficient and easy-to-use library for defining datatypes with
-- binders, and automatically handling bound variables and
-- alpha-equivalence. It is based on Gabbay and Pitts's theory of
-- nominal sets.

module Nominal (
  -- * Overview
  -- $OVERVIEW

  -- * Atoms
  -- $ATOMS
  Atom,
  AtomKind(..),
  AtomOfKind,
  Atomic,
  NameSuggestion,
  
  -- ** Creation of fresh atoms in a scope
  -- $FRESHNESS
  with_fresh,
  with_fresh_named,
  with_fresh_namelist,

  -- $NOMINAL_ANCHOR
  
  -- * Nominal types
  -- $NOMINAL
  Nominal(..),
  Permutation,
  
  -- * Binders
  Bindable(..),
  Bind,
  bind,
  bind_named,
  bind_namelist,
  merge,
  (.),

  -- * Printing of nominal values
  NominalSupport(..),
  NominalShow(..),
  Support,
  Literal(..),
  (∘),
  nominal_showsPrec,

  -- * AtomPlus
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

-- $OVERVIEW
-- 
-- We start with a minimal example. The following code defines a
-- datatype of untyped lambda terms, as well as a substitution
-- function. The important point is that the definition of lambda
-- terms is /automatically/ up to alpha-equivalence (i.e., up to
-- renaming of bound variables), and substitution is /automatically/
-- capture-avoiding. These details are handled by the "Nominal"
-- package and do not require any special programming by the user.
--
-- > {-# LANGUAGE DeriveGeneric #-}
-- > {-# LANGUAGE DeriveAnyClass #-}
-- >
-- > import Nominal
-- > import Prelude hiding ((.))
-- >
-- > -- Untyped lambda terms, up to alpha-equivalence.
-- > data Term = Var Atom | App Term Term | Abs (Bind Atom Term)
-- >   deriving (Generic, Nominal)
-- >
-- > -- Capture-avoiding substitution.
-- > subst :: Term -> Atom -> Term -> Term
-- > subst m x (Var y)
-- >   | x == y = m
-- >   | otherwise = Var y
-- > subst m x (App t s) = App (subst m x t) (subst m x s)
-- > subst m x (Abs body) = open body (\y s -> Abs (y . subst m x s))
--
-- Let us examine this code in more detail:
-- 
-- * The first four lines are boilerplate. Any code that uses the
-- "Nominal" package should enable the language options
-- @DeriveGeneric@ and @DeriveAnyClass@, and should import "Nominal".
-- We also hide the @(.)@ operator from the "Prelude", because the
-- "Nominal" package re-purposes the period as a binding operator.
--
-- * The next line defines the datatype @Term@ of untyped lambda
-- terms.  Here, 'Atom' is a predefined type of atomic /names/, which
-- we use as the names of variables. A term is either a variable, an
-- application, or an abstraction. The type 'Bind' 'Atom' @Term@ is
-- defined by the "Nominal" package and represents pairs (/a/,/t/) of
-- an atom and a term, modulo alpha-equivalence. We write /a/'.'/t/ to
-- denote such an alpha-equivalence class of pairs.
--
-- * The next line declares that @Term@ is a /nominal/ type, by
-- deriving an instance of the type class 'Nominal' (and also
-- 'Generic', which enables the magic that allows 'Nominal' instances
-- to be derived automatically).  In a nutshell, a nominal datatype is
-- a type that is aware of the existence of atoms. The 'Bind'
-- operation can only be applied to nominal datatypes, because
-- otherwise alpha-equivalence would not make sense.
--
-- * The substitution function inputs a term /m/, a variable /x/, and
-- a term /t/, and outputs a modified version of the term /t/ in which
-- all occurrences of the variable /x/ have been replaced by /m/.  The
-- clauses for variables and application are straightforward. Note
-- that atoms can be compared for equality. In the clause for
-- abstraction, the /body/ of the abstraction, which is of type 'Bind'
-- 'Atom' @Term@, is /opened/: this means that a /fresh/ name /y/ and
-- a term /s/ are generated such that /body/ = /y/'.'/s/. Since the
-- name /y/ is guaranteed to be fresh, the substitution can be
-- recursively applied to /s/ without the possibility that /y/ may be
-- captured in /m/ or /x/.

-- $ATOMS
--
-- We assume that we are given one or more countable sets of /atoms/,
-- which can be used as the names of bound variables. As shown in the
-- above example, the type 'Atom' can be used for this purpose.
--
-- In addition, it is often useful to have more than one type of atoms
-- (for example, term variables and type variables), and/or to
-- customize the default variable names used by each type of atoms
-- (for example, to use /x/, /y/, /z/ for term variables and α, β, γ
-- for type variables).
--
-- The standard way to define an additional type of atoms is to define
-- a new empty type /t/ that is an instance of 'AtomKind'. Optionally,
-- a list of suggested names for the new atoms can be provided. Then
-- 'AtomOfKind' /t/ is a new type of atoms. For example:
--
-- > data VarName
-- > instance AtomKind VarName where
-- >   suggested_names _ = ["x", "y", "z"]
-- > newtype Variable = AtomOfKind VarName
-- 
-- All atom types are members of the type class 'Atomic'.

-- $FRESHNESS
--
-- Sometimes we need to generate a fresh atom of a given atom type.
-- In the "Nominal" package, a fresh atom should never be generated
-- globally. The philosophy is that a fresh atom is always generated
-- for a particular /purpose/, and the use of the atom is local to
-- that purpose.  Therefore, a fresh atom should always be generated
-- within a local /scope/. So instead of
--
-- > let a = fresh in something,
--
-- we write
--
-- > with_fresh (\a -> something).
--
-- To ensure soundness, the programmer must ensure that the fresh atom
-- does not escape the body of the 'with_fresh' block. See the
-- documentation of 'with_fresh' for examples of what is and is not
-- permitted, and a more precise statement of the correctness
-- condition.

-- $NOMINAL_ANCHOR #NOMINAL#

-- $NOMINAL
--
-- Informally, a type of /nominal/ if if is aware of the existence of
-- atoms, and knows what to do in case an atom needs to be renamed.
-- More formally, a type is nominal if it is acted upon by the group
-- of finitely supported permutations of atoms. Ideally, all types
-- are nominal.
--
-- When using the "Nominal" package, all types whose elements can
-- occur in the scope of a binder must be instances of the 'Nominal'
-- type class.  Fortunately, in most cases, instances of 'Nominal' can
-- be derived automatically. To do so, simply add @deriving (Generic,
-- Nominal)@ to any datatype definition. This also requires the
-- language options DeriveGeneric and DeriveAnyClass to be
-- enabled. For example:
--
-- > {-# LANGUAGE DeriveGeneric #-}
-- > {-# LANGUAGE DeriveAnyClass #-}
-- > 
-- > data MyTree a = Leaf | Branch a (MyTree a) (MyTree a)
-- >   deriving (Generic, Nominal)
--
-- There are some cases where automatically deriving 'Nominal'
-- instances will not work. These are: (a) base types such as
-- 'Double', (b) types that are not 'Generic', such as GADTs, and (c)
-- types that require a custom 'Nominal' instance for some reason
-- (advanced users only!). In these cases, we can define a 'Nominal'
-- instance by specifying how permutations of atoms act on the
-- elements of the type.
-- 
-- [Base types.] Since base types (such as 'Double') cannot
-- contain atoms, the action is trivial.
-- 
-- > instance Nominal Double where
-- >   π • x = x
--
-- [Data types.] For most data types, the action of a permutation
-- is simply passed down the terms recursively. For example, here is
-- how the 'Nominal' instance for the type @MyTree@ would be
-- defined:
--
-- > instance (Nominal a) => Nominal MyTree a where
-- >   π • Leaf = Leaf
-- >   π • (Branch x left right) = Branch (π • x) (π • left) (π • right)
