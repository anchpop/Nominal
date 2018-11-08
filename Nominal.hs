-- | An efficient and easy-to-use library for defining datatypes with
-- binders, and automatically handling bound variables and
-- alpha-equivalence. It is based on Gabbay and Pitts's theory of
-- nominal sets.
--
-- Most users should only import the top-level module "Nominal", which
-- exports all the relevant functionality in a clean and abstract way.
-- Its submodules, such as "Nominal.Unsafe", are implementation
-- specific and subject to change, and should not normally be imported
-- by user code.

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

  -- ** Creation of fresh atoms globally
  -- $GLOBAL_FRESHNESS
  fresh,
  fresh_named,
  fresh_namelist,

  -- $NOMINAL_ANCHOR
  
  -- * Nominal types
  -- $NOMINAL
  Nominal(..),
  Permutation,
  Basic(..),
  
  -- * Binders
  Bind,
  (.),
  abst,
  open,
  merge,

  -- ** Convenience functions
  bind,
  bind_named,
  bind_namelist,

  -- ** The Bindable class
  -- $BINDABLE
  Bindable(..),
  Pattern,

  -- ** Non-binding patterns
  NoBind(..),
  nobinding,
  
  -- * Printing of nominal values
  -- $PRINTING
  open_for_printing,
  NominalSupport(..),
  Support,
  Literal(..),

  -- $NOMINALSHOW_ANCHOR

  -- * The NominalShow class
  -- $NOMINALSHOW
  NominalShow(..),
  nominal_show,
  nominal_showsPrec,

  -- $DERIVING_ANCHOR

  -- * Deriving generic instances
  -- $DERIVING

  -- $CUSTOM_ANCHOR

  -- * Defining custom instances
  -- $CUSTOM

  -- ** Basic types
  -- $CUSTOM_BASIC

  basic_action,
  basic_support,
  basic_showsPrecSup,
  basic_binding,
  
  -- ** Recursive types
  -- $CUSTOM_RECURSIVE
  
  -- * Miscellaneous
  (∘),
  module Nominal.Generics
)
where

import Prelude hiding ((.))

import Nominal.ConcreteNames
import Nominal.Atom
import Nominal.Permutation
import Nominal.Nominal
import Nominal.NominalSupport
import Nominal.Bindable
import Nominal.Atomic
import Nominal.NominalShow
import Nominal.Generics

-- ----------------------------------------------------------------------

-- $OVERVIEW
-- 
-- We start with a minimal example. The following code defines a
-- datatype of untyped lambda terms, as well as a substitution
-- function. The important point is that the definition of lambda
-- terms is /automatically/ up to alpha-equivalence (i.e., up to
-- renaming of bound variables), and substitution is /automatically/
-- capture-avoiding. These details are handled by the "Nominal"
-- library and do not require any special programming by the user.
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
-- "Nominal" library should enable the language options
-- @DeriveGeneric@ and @DeriveAnyClass@, and should import "Nominal".
-- We also hide the @(.)@ operator from the "Prelude", because the
-- "Nominal" library re-purposes the period as a binding operator.
--
-- * The next line defines the datatype @Term@ of untyped lambda
-- terms.  Here, 'Atom' is a predefined type of atomic /names/, which
-- we use as the names of variables. A term is either a variable, an
-- application, or an abstraction. The type @('Bind' 'Atom' Term)@ is
-- defined by the "Nominal" library and represents pairs (/a/,/t/) of
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
-- a term /t/, and outputs the term obtained from /t/ by replacing all
-- occurrences of the variable /x/ by /m/.  The clauses for variables
-- and application are straightforward. Note that atoms can be
-- compared for equality. In the clause for abstraction, the /body/ of
-- the abstraction, which is of type @('Bind' 'Atom' Term)@, is
-- /opened/: this means that a /fresh/ name /y/ and a term /s/ are
-- generated such that /body/ = /y/'.'/s/. Since the name /y/ is
-- guaranteed to be fresh, the substitution can be recursively applied
-- to /s/ without the possibility that /y/ may be captured in /m/ or
-- /x/.

-- ----------------------------------------------------------------------

-- $ATOMS
--
-- /Atoms/ are things that can be bound. The important properties of
-- atoms are: there are infinitely many of them (so we can always find
-- a fresh one), and atoms can be compared for equality. Atoms do not
-- have any other special properties, and in particular, they are
-- interchangeable (any atom is as good as any other atom).
--
-- As shown in the introductory example above, the type 'Atom' can be
-- used for this purpose. In addition, it is often useful to have more
-- than one kind of atoms (for example, term variables and type
-- variables), and/or to customize the default names that are used
-- when atoms of each kind are displayed (for example, to use /x/,
-- /y/, /z/ for term variables and α, β, γ for type variables).
--
-- The standard way to define an additional type of atoms is to define
-- a new empty type /t/ that is an instance of 'AtomKind'. Optionally,
-- a list of suggested names for the atoms can be provided. Then
-- 'AtomOfKind' /t/ is a new type of atoms. For example:
--
-- > data VarName
-- > instance AtomKind VarName where
-- >   suggested_names _ = ["x", "y", "z"]
-- > 
-- > newtype Variable = AtomOfKind VarName
-- 
-- All atom types are members of the type class 'Atomic'.

-- ----------------------------------------------------------------------

-- $FRESHNESS
--
-- Sometimes we need to generate a fresh atom.  In the "Nominal"
-- library, the philosophy is that a fresh atom is usually generated
-- for a particular /purpose/, and the use of the atom is local to
-- that purpose. Therefore, a fresh atom should always be generated
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

-- ----------------------------------------------------------------------

-- $GLOBAL_FRESHNESS
--
-- Occasionally, it can be useful to generate a globally fresh atom.
-- This is done within the 'IO' monad, and therefore, the function
-- 'fresh' (and its friends) have no corresponding correctness
-- condition as for 'with_fresh'.
-- 
-- These functions are primarily intended for testing. They
-- give the user a convenient way to generate fresh names in the
-- read-eval-print loop, for example:
--
-- >>> a <- fresh :: IO Atom
-- >>> b <- fresh :: IO Atom
-- >>> a.b.(a,b)
-- x . y . (x,y)
--
-- These functions should rarely be used in programs. Normally you
-- should use 'with_fresh' instead of 'fresh', to generate a fresh
-- atom in a specific scope for a specific purpose. If you find
-- yourself generating a lot of global names and not binding them,
-- consider whether the "Nominal" library is the wrong tool for your
-- purpose. Perhaps you should use "Data.Unique" instead?

-- ----------------------------------------------------------------------

-- $NOMINAL_ANCHOR #NOMINAL#

-- $NOMINAL
--
-- Informally, a type of /nominal/ if if is aware of the existence of
-- atoms, and knows what to do in case an atom needs to be renamed.
-- More formally, a type is nominal if it is acted upon by the group
-- of finitely supported permutations of atoms. Ideally, all types
-- are nominal.
--
-- When using the "Nominal" library, all types whose elements can
-- occur in the scope of a binder must be instances of the 'Nominal'
-- type class.  Fortunately, in most cases, new instances of 'Nominal'
-- can be derived automatically.

-- ----------------------------------------------------------------------

-- $BINDABLE
--
-- The 'Bindable' class contains things that can be abstracted by
-- binders (sometimes called /patterns/). In addition to atoms, this
-- also includes pairs of atoms, lists of atoms, and so on.
-- In most cases, new instances of 'Bindable' can be derived
-- automatically.

-- ----------------------------------------------------------------------

-- $PRINTING
--
-- The printing of nominal values requires concrete names for the
-- bound variables to be chosen in such a way that they do not clash
-- with the names of any free variables, constants, or other bound
-- variables. This requires the ability to compute the set of free
-- atoms (and constants) of a term. We call this set the /support/ of
-- a term.
--
-- Our mechanism for pretty-printing nominal values consists of two
-- things: the type class 'NominalSupport', which represents terms
-- whose support can be calculated, and the function
-- 'open_for_printing', which handles choosing concrete names for
-- bound variables.
--
-- In addition to this general-purpose mechanism, there is also the
-- 'NominalShow' type class, which is analogous to 'Show' and provides
-- a default representation of nominal terms.

-- ----------------------------------------------------------------------

-- $NOMINALSHOW_ANCHOR #NOMINALSHOW#

-- $NOMINALSHOW
--
-- The 'NominalShow' class is analogous to Haskell's standard 'Show'
-- class, and provides a default method for converting elements of
-- nominal datatypes to strings. The function 'nominal_show' is
-- analogous to 'show'.  In most cases, new instances of 'NominalShow'
-- can be derived automatically.

-- ----------------------------------------------------------------------

-- $DERIVING_ANCHOR #DERIVING#

-- $DERIVING
--
-- In many cases, instances of 'Nominal', 'NominalSupport',
-- 'NominalShow', and/or 'Bindable' can be derived automatically, using
-- the generic \"@deriving@\" mechanism.  To do so, enable the
-- language options @DeriveGeneric@ and @DeriveAnyClass@, and derive a
-- 'Generic' instance in addition to whatever other instances you want
-- to derive.
--
-- ==== Example 1: Trees
--
-- > {-# LANGUAGE DeriveGeneric #-}
-- > {-# LANGUAGE DeriveAnyClass #-}
-- > 
-- > data MyTree a = Leaf | Branch a (MyTree a) (MyTree a)
-- >   deriving (Generic, Nominal, NominalSupport, NominalShow, Show, Bindable)
--
-- ==== Example 2: Untyped lambda calculus
--
-- Note that in the case of lambda terms, it does not make sense to
-- derive a 'Bindable' instance, as lambda terms cannot be used as
-- binders.
-- 
-- > {-# LANGUAGE DeriveGeneric #-}
-- > {-# LANGUAGE DeriveAnyClass #-}
-- > 
-- > data Term = Var Atom | App Term Term | Abs (Bind Atom Term)
-- >   deriving (Generic, Nominal, NominalSupport, NominalShow, Show)

-- ----------------------------------------------------------------------

-- $CUSTOM_ANCHOR #CUSTOM#

-- $CUSTOM
-- 
-- There are some cases where instances of 'Nominal' and the other
-- type classes cannot be automatically derived. These include: (a)
-- base types such as 'Double', (b) types that are not generic, such
-- as certain GADTs, and (c) types that require a custom 'Nominal'
-- instance for some other reason (advanced users only!). In such
-- cases, instances must be defined explicitly. The follow examples
-- explain how this is done.

-- ----------------------------------------------------------------------

-- $CUSTOM_BASIC
--
-- A type is /basic/ or /non-nominal/ if its elements cannot contain
-- atoms. Typical examples are base types such as 'Integer' and
-- 'Bool', and other types constructed exclusively from them, such as
-- @['Integer']@ or @'Bool' -> 'Bool'@.
--
-- For basic types, it is very easy to define instances of 'Nominal',
-- 'NominalSupport', 'NominalShow', and 'Bindable': for each class
-- method, we provide a corresponding helper function whose name
-- starts with @basic_@ that does the correct thing. These functions
-- can only be used to define instances for /non-nominal/ types.
--
-- ==== Example
--
-- We show how the nominal type class instances for the base type
-- 'Double' were defined.
--
-- > instance Nominal Double where
-- >   (•) = basic_action
-- >
-- > instance NominalSupport Double where
-- >   support = basic_support
-- >
-- > instance NominalShow Double where
-- >   showsPrecSup = basic_showsPrecSup
-- >
-- > instance Bindable Double where
-- >   binding = basic_binding
--
-- An alternative to defining new basic type class instances is to
-- wrap the corresponding types in the constructor 'Basic'.  The type
-- @'Basic' MyType@ is isomorphic to @MyType@, and is automatically an
-- instance of the relevant type classes.

-- ----------------------------------------------------------------------

-- $CUSTOM_RECURSIVE
--
-- For recursive types, instances for nominal type classes can be
-- defined by passing the relevant operations recursively down the
-- term structure.  We will use the type @MyTree@ as a running
-- example.
-- 
-- > data MyTree a = Leaf | Branch a (MyTree a) (MyTree a)
--
-- ==== Nominal
-- 
-- To define an instance of 'Nominal', we must specify how
-- permutations of atoms act on the elements of the type. For example:
--
-- > instance (Nominal a) => Nominal (MyTree a) where
-- >   π • Leaf = Leaf
-- >   π • (Branch a l r) = Branch (π • a) (π • l) (π • r)
--
-- ==== NominalSupport
-- 
-- To define an instance of 'NominalSupport', we must compute the
-- support of each term. This can be done by applying 'support' to a
-- tuple or list (or combination thereof) of immediate subterms. For
-- example:
--
-- > instance (NominalSupport a) => NominalSupport (MyTree a) where
-- >   support Leaf = support ()
-- >   support (Branch a l r) = support (a, l, r)
--
-- Here is another example showing additional possibilities:
-- 
-- > instance NominalSupport Term where
-- >   support (Var x) = support x
-- >   support (App t s) = support (t, s)
-- >   support (Abs t) = support t
-- >   support (MultiApp t args) = support (t, [args])
-- >   support Unit = support ()
--
-- If your nominal type uses additional constants, identifiers, or
-- reserved keywords that are not implemented as 'Atom's, but whose
-- names you don't want to clash with the names of bound variables,
-- declare them with 'Literal' applied to a string:
--
-- >   support (Const str) = support (Literal str)
--
-- ==== NominalShow
--
-- Custom 'NominalShow' instances require a definition of the
-- 'showsPrecSup' function. This is very similar to the 'showsPrec'
-- function of the 'Show' class, except that the function takes the
-- term's support as an additional argument. Here is how it is done
-- for the @MyTree@ datatype:
-- 
-- > instance (NominalShow a) => NominalShow (MyTree a) where
-- >   showsPrecSup sup d Leaf = showString "Leaf"
-- >   showsPrecSup sup d (Branch a l r) =
-- >     showParen (d > 10) $
-- >       showString "Branch "
-- >       ∘ showsPrecSup sup 11 a
-- >       ∘ showString " "
-- >       ∘ showsPrecSup sup 11 l
-- >       ∘ showString " "
-- >       ∘ showsPrecSup sup 11 r
--
-- ==== Bindable
--
-- The 'Bindable' class requires a function 'binding', which maps a
-- term to the corresponding pattern. The recursive cases use the
-- 'Applicative' structure of the 'Pattern' type. 
-- 
-- Here is how we could define a 'Bindable' instance for the
-- @MyTree@ type. We use the \"applicative do\" notation for
-- convenience, although this is not essential.
--
-- > {-# LANGUAGE ApplicativeDo #-}
-- > 
-- > instance (Bindable a) => Bindable (MyTree a) where
-- >   binding Leaf = do
-- >     pure Leaf
-- >   binding (Branch a l r) = do
-- >     a' <- binding a
-- >     l' <- binding l
-- >     r' <- binding r
-- >     pure (Branch a' l' r')
--
-- To embed non-binding sites within a pattern, replace 'binding' by
-- 'nobinding' in the recursive call. For further discussion of
-- non-binding patterns, see also 'NoBind'. Here is an example:
--
-- > {-# LANGUAGE ApplicativeDo #-}
-- > 
-- > data HalfBinder a b = HalfBinder a b
-- >
-- > instance (Bindable a) => Bindable (HalfBinder a b) where
-- >   binding (HalfBinder a b) = do
-- >     a' <- binding a
-- >     b' <- nobinding b
-- >     pure (HalfBinder a' b')
--
-- The effect of this is that the /a/ is bound and /b/ is not bound in
-- the term @(HalfBinder /a/ /b/)./t/@,
-- 
