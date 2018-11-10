{-# LANGUAGE PatternSynonyms #-}

-- | An efficient and easy-to-use library for defining datatypes with
-- binders, and automatically handling bound variables and
-- alpha-equivalence. It is based on <#GP1999 Gabbay and Pitts>'s
-- theory of nominal sets.
--
-- Users should only import the top-level module "Nominal", which
-- exports all the relevant functionality in a clean and abstract way.
-- Its submodules, such as "Nominal.Unsafe", are implementation
-- specific and subject to change, and should not normally be imported
-- by user code.

module Nominal (
  -- * Overview
  -- $OVERVIEW

  -- * Atoms
  -- ** Atom types
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
  NominalPermutation,
  Basic(..),
  
  -- * Binders
  Bind,
  -- ** Basic operations
  (.),
  pattern (:.),
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
  NominalBinder,

  -- ** Non-binding patterns
  NoBind(..),
  nobinding,

  -- $CONDITION_ANCHOR
  
  -- * Pitt's freshness condition
  -- $CONDITION
  
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
  module Nominal.Generic
  -- $GENERICS
  
  -- $RELATED_ANCHOR
  
  -- * Related Work
  -- $RELATED

  -- $REFERENCES_ANCHOR
  
  -- * Acknowledgements
  -- $ACKNOWLEDGEMENTS

  -- * References
  -- $REFERENCES
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
import Nominal.Generic

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
-- > subst m z (Var x)
-- >   | x == z    = m
-- >   | otherwise = Var x
-- > subst m z (App t s) = App (subst m z t) (subst m z s)
-- > subst m z (Abs (x :. t)) = Abs (x . subst m z t)
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
-- to be derived automatically).  In a nutshell, a nominal type is
-- a type that is aware of the existence of atoms. The 'Bind'
-- operation can only be applied to nominal types, because
-- otherwise alpha-equivalence would not make sense.
--
-- * The substitution function inputs a term /m/, a variable /z/, and
-- a term /t/, and outputs the term /t/[/m/\//z/] that is obtained
-- from /t/ by replacing all occurrences of the variable /z/ by /m/.
-- The clauses for variables and application are straightforward. Note
-- that atoms can be compared for equality. In the clause for
-- abstraction, @(x :. t)@ is an /abstraction pattern/. It matches any
-- abstraction of the form /y/'.'/s/, which is of type @('Bind' 'Atom'
-- Term)@. Moreover, each time the abstraction pattern is used, a
-- /fresh/ name /x/ and a term /t/ are generated such that /x/'.'/t/ =
-- /y/'.'/s/. Since the name /x/ resulting from the pattern matching
-- is always guaranteed to be fresh, the substitution can be
-- recursively applied to /t/ without the possibility that /x/ may be
-- captured in /m/ or that /x/ = /z/. In other words, abstraction
-- patterns implement what is informally known as
-- /Barendregt's variable convention/, i.e., the names of bound
-- variables are always assumed to be fresh.
--
-- See the folder
-- <http://hackage.haskell.org/package/nominal/src/examples/ \"examples\">
-- for additional examples.

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
-- does not escape the body of the 'with_fresh' block. See 
-- <#CONDITION "Pitts's freshness condition"> for examples
-- of what is and is not permitted, and a more precise statement of
-- the correctness condition.

-- ----------------------------------------------------------------------

-- $GLOBAL_FRESHNESS
--
-- Occasionally, it can be useful to generate a globally fresh atom.
-- This is done within the 'IO' monad, and therefore, the function
-- 'fresh' (and its friends) are /not/ subject to
-- <#CONDITION Pitts's freshness condition>.
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
-- The 'Bindable' class contains things that can be abstracted. More
-- precisely, /x/ is /bindable/, or a /binder/, if abstractions of the
-- form /x/./t/ can be formed.  Sometimes binders are also called
-- /patterns/, but we avoid this terminology here, to avoid confusion
-- with pattern matching, which is a separate operation from binding.
--
-- In addition to atoms, binders include pairs of atoms, lists of
-- atoms, and so on.  In most cases, new instances of 'Bindable' can
-- be derived automatically.
-- 
-- For example, @(/x/,/y/)./t/@ binds a pair of atoms in /t/. It is
-- roughly equivalent to @/x/./y/./t/@, except that it is of type
-- 'Bind' ('Atom', 'Atom') /t/ instead of
-- 'Bind' 'Atom' ('Bind' 'Atom' /t/).
--
-- When a binder contains repeated atoms, they are regarded as
-- distinct, and are bound one at a time, in some fixed but
-- unspecified order. For example, @(/x/,/x/).(/x/,/x/)@ is equivalent
-- to either @(/x/,/y/).(/x/,/x/)@ or @(/x/,/y/).(/y/,/y/)@. Which of
-- the two alternatives is chosen is implementation specific and user
-- code should not rely on the order of abstractions in such cases.


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
--
-- == Deriving instances for existing types
--
-- Sometimes it may be necessary to derive an instance of 'Nominal' or
-- one of the other type classes for an already existing datatype.
-- This can be done by specifying an instance declaration without any
-- body. For example, here is how the instances would be specified for
-- the 'Maybe' type:
--
-- > instance (Nominal a) => Nominal (Maybe a)
-- > instance (NominalSupport a) => NominalSupport (Maybe a)
-- > instance (NominalShow a) => NominalShow (Maybe a)
-- > instance (Bindable a) => Bindable (Maybe a)

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
-- @'Basic' MyType@ is isomorphic to @MyType@, and is automatically an
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
-- term to the corresponding binder. The recursive cases use the
-- 'Applicative' structure of the 'NominalBinder' type. 
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
-- To embed non-binding sites within a binder, replace 'binding' by
-- 'nobinding' in the recursive call. For further discussion of
-- non-binding binders, see also 'NoBind'. Here is an example:
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

-- ----------------------------------------------------------------------

-- $CONDITION_ANCHOR #CONDITION#

-- $CONDITION
--
-- To ensure soundness (referential transparency and equivariance),
-- all functions that generate a fresh name in a local scope must
-- satisfy a certain condition known as Pitts's /freshness/
-- /condition/ /for/ /binders/ (see Chapter 4.5 of 
-- <#PITTS2013 [Pitts 2013]>).
--
-- Informally, this condition means that the fresh atom must not
-- escape the body of the block in which it was created. Thus, for
-- example, the following are permitted:
--   
-- > with_fresh (\a -> f a == g a)
-- > with_fresh (\a -> a . f a b c)
--
-- Here is an example of what is /not/ permitted:
--
-- > with_fresh (\a -> a)
--
-- In more technical terms, the correctness condition is that in an
-- application
--
-- > with_fresh (\a -> body),
--
-- we must have /a/ \# /body/.  See <#PITTS2003 [Pitts 2003]> or
-- <#PITTS2013 [Pitts 2013]> for more information on what this
-- means.
--
-- The following exported functions are subject to the freshness condition:
-- 'with_fresh', 
-- 'with_fresh_named', 
-- 'with_fresh_namelist',
-- 'open',
-- 'open_for_printing',
-- as well as the use of abstraction patterns @(@':.'@)@.
--
-- Haskell does not enforce this restriction. But if a program
-- violates it, referential transparency may not hold, which could in
-- theory lead to unsound compiler optimizations and undefined
-- behavior. Here is an example of an incorrect use of 'with_fresh'
-- that violates referential transparency:
-- 
-- >>> (with_fresh id :: Atom) == (with_fresh id :: Atom)
-- False

----------------------------------------------------------------------

-- $GENERICS
--
-- We re-export the "Generic" type class for convenience, so that
-- users do not have to import "GHC.Generics".

----------------------------------------------------------------------

-- $RELATED_ANCHOR #RELATED#

-- $RELATED
--
-- <#CHENEY2005 [Cheney 2005]> and
-- <#WYS2011 [Weirich, Yorgey, and Sheard 2011]> describe
-- Haskell implementations of binders using generic programming. While
-- there are many similarities, these implementations differ from the
-- "Nominal" library in several respects.
-- 
-- 1. /Higher-order nominal types./ Weirich et al.'s \"Unbound\"
-- library is based on the locally nameless approach, and therefore
-- function types cannot appear under binders. Although Cheney's
-- library is based on the nominal approach, it requires the
-- relation /a/ \# /t/ to be decidable for all nominal types, and
-- therefore function types cannot be nominal. In the "Nominal"
-- library, function types are nominal and can occur under binders.
--
-- 2. /Freshness monad vs. scoped freshness./ Both the libraries of
-- Cheney and Weirich et al. use a freshness monad; all operations
-- that create fresh names (such as 'open') take place in this monad.
-- While this is semantically sound, it has some disadvantages: (a)
-- Every computation with binders must be threaded through the monad.
-- When this is done deeply within a nested expression, this gives
-- rise to an unnatural programming style. (b) Computations must be
-- threaded through the monad even though the user is aware, in the
-- relevant use cases, that the defined functions are in fact pure
-- (i.e., the freshness state is inessential). (c) The use of a
-- freshness monad precludes the use of abstraction patterns. The
-- "Nominal" library uses /scoped freshness/ instead of a freshness
-- monad. This lends itself to a more natural programming style. The
-- price to pay for this is that the user must ensure that fresh names
-- are only used in the local scope in which they were
-- generated. Formally, the user must adhere to a correctness
-- criterion
-- (<#CONDITION Pitts's freshness condition>) that cannot be checked
-- by the compiler.
--
-- 3. /Simplicity./ Weirich et al.'s \"Unbound\" library has many
-- advanced features, such as set-binders, recursive patterns, nested
-- bindings, and an exposed interface for certain low-level atom
-- manipulations.  The "Nominal" library currently lacks these
-- features. Instead, it focuses on ease of use and an efficient
-- implementation of a core set of functionalities. The hope is that
-- these are sufficiently general and robust to permit more advanced
-- features to be implemented in user space on top of the library. It
-- remains to be seen whether this is the case.
--
-- <#SPG2003 [Shinwell, Pitts, and Gabbay 2003]> describe FreshML, an
-- extension of ML with binders. This was later implemented by
-- <#SP2005 [Shinwell and Pitts 2005]> as an extension of Objective
-- Caml. The functionality and philosophy of the "Nominal" library is
-- essentially similar to that of FreshML. Since ML is a
-- side-effecting language, the issue of a freshness monad does not
-- arise, but users must still adhere to
-- <#CONDITION Pitts's freshness condition> to guarantee that programs
-- define equivariant functions. However, since ML lacks Haskell's
-- support for generic programming and custom patterns, the FreshML
-- implementation requires patching the compiler. It is therefore
-- harder to deploy than a library.

----------------------------------------------------------------------

-- $ACKNOWLEDGEMENTS
--
-- Thanks to Frank Fu for stress-testing the library and insisting on
-- efficiency. Thanks to Andrew Pitts for helpful suggestions, and
-- especially for nudging me to implement abstraction patterns.

----------------------------------------------------------------------

-- $REFERENCES_ANCHOR #REFERENCES#

-- $REFERENCES
--
-- #CHENEY2005#
--
-- * J. Cheney. "Scrap your nameplate (functional pearl)". Proceedings
-- of the 10th ACM SIGPLAN International Conference on Functional
-- Programming (ICFP 2005), pages 180–191, 2005.
-- 
-- #GB1999#
-- 
-- * M. J. Gabbay and A. M. Pitts. "A new approach to abstract syntax
-- involving binders".  Proceedings of the 14th Annual IEEE Symposium
-- on Logic in Computer Science (LICS 1999), pages 214–224, 1999.
-- 
-- #PITTS2003#
--
-- * M. Pitts. "Nominal logic, a first order theory of names and
-- binding". Information and Computation 186:165–193, 2003.
--
-- #PITTS2013#
--
-- * M. Pitts. "Nominal sets: names and symmetry in computer
-- science". Cambridge University Press, 2013.
--
-- #SPG2003#
--
-- * M. R. Shinwell, A. M. Pitts, and M. J. Gabbay. "FreshML:
-- programming with binders made simple". Proceedings of the 8th ACM
-- SIGPLAN International Conference on Functional Programming (ICFP
-- 2003), pages 263–274, 2003.
--
-- #SP2005#
--
-- * M. R. Shinwell and A. M. Pitts. "Fresh Objective Caml user
-- manual". Technical Report 621, University of Cambridge Computer
-- Laboratory, February 2005. Implementation at
-- <https://www.cl.cam.ac.uk/~amp12/fresh-ocaml/>.
--
-- #WYS2011#
--
-- * S. Weirich, B. A. Yorgey, and T. Sheard. "Binders unbound".
-- Proceedings of the 16th ACM SIGPLAN International Conference on
-- Functional Programming (ICFP 2011), pages 333–345, 2011.
-- Implementation at <http://hackage.haskell.org/package/unbound>.

