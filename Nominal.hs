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
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Data.List
import GHC.Generics

import Nominal.ConcreteNames
import Nominal.Unsafe
import Nominal.Atoms
import Nominal.Permutations
import Nominal.Nominal
import Nominal.NominalSupport

-- ----------------------------------------------------------------------

instance (Nominal t) => Nominal (BindAtom t) where
  π • (BindAtom n f) = BindAtom n (\x -> π • (f x))

instance (NominalSupport t) => NominalSupport (BindAtom t) where
  support (BindAtom n f) =
    with_fresh (\a -> support_delete a (support (f a)))

instance (Nominal t, Eq t) => Eq (BindAtom t) where
  b1 == b2 = atom_open (atom_merge b1 b2) $ \a (t1,t2) -> t1 == t2

-- | A variant of 'open' which moreover attempts to choose a name for
-- the bound atom that does not clash with any free name in its
-- scope. This requires a 'NominalShow' instance. It is mostly
-- useful for building custom pretty-printers for nominal
-- terms. Except in pretty-printers, it is equivalent to 'open'.
--
-- Usage:
--
-- > open_for_printing sup t (\x s sup' -> body)
--
-- Here, /sup/ = 'support' /t/. For printing to be efficient (roughly
-- O(/n/)), the support must be pre-computed in a bottom-up fashion,
-- and then passed into each subterm in a top-down fashion (rather
-- than re-computing it at each level, which would be O(/n/^2)).  For
-- this reason, 'open_for_printing' takes the support of /t/ as an
-- additional argument, and provides /sup'/, the support of /s/, as an
-- additional parameter to the body.
atom_open_for_printing :: (Nominal t) => NameSuggestion -> Support -> BindAtom t -> (Atom -> t -> Support -> s) -> s
atom_open_for_printing ns2 sup t@(BindAtom ns f) body =
  with_fresh_named n1 (\a -> body a (force (f a)) (sup' a))
  where
    ns1 = if null ns then ns2 else ns
    n1 = rename_fresh (strings_of_support sup) ns1
    sup' a = support_insert a sup

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
-- * The Bindable class

class (Eq a, Nominal a) => Bindable a where
  -- | 'Bind' /a/ /t/ is the type of atom abstractions, denoted [a]t
  -- in the nominal logic literature. Its elements are of the form
  -- (a.v) modulo alpha-equivalence. For more details on what this
  -- means, see Definition 4 of [Pitts 2002].
  data Bind a t

  -- | This is the '(•)' function of 'Nominal'. We need to define it
  -- here on a per-instance basis to get the 'Nominal' instance of
  -- 'Bind' /a/ /t/.
  bindable_action :: (Nominal t) => Permutation -> Bind a t -> Bind a t

  -- | This is the 'support' function of 'NominalSupport'. We need to
  -- define it here on a per-instance basis to get the
  -- 'NominalSupport' instance of 'Bind' /a/ /t/.
  bindable_support :: (NominalSupport t) => Bind a t -> Support

  -- | This is the equality test. We need to define it here on a
  -- per-instance basis to get the 'Eq' instance of 'Bind' /a/ /t/.
  bindable_eq :: (Nominal t, Eq t) => Bind a t -> Bind a t -> Bool
  
  -- | Atom abstraction: (/a/./t/) represents the equivalence class of
  -- pairs (/a/,/t/) modulo alpha-equivalence. Here, (/a/,/t/) ~
  -- (/b/,/s/) iff for fresh /c/, (/a/ /c/) • /t/ = (/b/ /c/) • /s/.
  --
  -- We use the infix operator '.', which is normally bound to
  -- function composition in the standard library. Thus, nominal
  -- programs should import the standard library like this:
  --
  -- > import Prelude hiding ((.))
  abst :: (Nominal t) => a -> t -> Bind a t
  
  -- | Pattern matching for atom abstraction. In an ideal programming
  -- idiom, we would be able to define a function on atom abstractions
  -- like this:
  --
  -- > f (x.s) = body.
  --
  -- Haskell doesn't let us provide this syntax, but the 'open'
  -- function provides the equivalent syntax
  --
  -- > f t = open t (\x s -> body).
  --
  -- To be referentially transparent and equivariant, the body is
  -- subject to the same restriction as 'with_fresh', namely, /x/ must
  -- be fresh for the body (in symbols /x/ # /body/).
  open :: (Nominal t) => Bind a t -> (a -> t -> s) -> s

  -- | A variant of 'open' which moreover attempts to choose a name
  -- for the bound atom that does not clash with any free name in its
  -- scope. This requires a 'NominalShow' instance. It is mostly
  -- useful for building custom pretty-printers for nominal
  -- terms. Except in pretty-printers, it is equivalent to 'open'.
  --
  -- Usage:
  --
  -- > open_for_printing sup t (\x s sup' -> body)
  --
  -- Here, /sup/ = 'support' /t/. For printing to be efficient
  -- (roughly O(/n/)), the support must be pre-computed in a bottom-up
  -- fashion, and then passed into each subterm in a top-down fashion
  -- (rather than re-computing it at each level, which would be
  -- O(/n/^2)).  For this reason, 'open_for_printing' takes the
  -- support of /t/ as an additional argument, and provides /sup'/,
  -- the support of /s/, as an additional parameter to the body.
  open_for_printing :: (Nominal t) => Support -> Bind a t -> (a -> t -> Support -> s) -> s

instance (Bindable a, Nominal t) => Nominal (Bind a t) where
  π • body = bindable_action π body

-- | Atom abstraction: (/a/./t/) represents the equivalence class of
-- pairs (/a/,/t/) modulo alpha-equivalence. Here, (/a/,/t/) ~
-- (/b/,/s/) iff for fresh /c/, (/a/ /c/) • /t/ = (/b/ /c/) • /s/.
--
-- We use the infix operator '.', which is normally bound to function
-- composition in the standard library. Thus, nominal programs should
-- import the standard library like this:
--
-- > import Prelude hiding ((.))
(.) :: (Bindable a, Nominal t) => a -> t -> Bind a t
(.) = abst
infixr 5 .

-- | Open two abstractions at once. So
--
-- > f t = open t (\x y s -> body)
--
-- is equivalent to the nominal pattern matching
--
-- > f (x.y.s) = body
open2 :: (Bindable a, Bindable b, Nominal t) => Bind a (Bind b t) -> (a -> b -> t -> s) -> s
open2 term k = open term $ \a term' -> open term' $ \a' t -> k a a' t

-- | Like 'open2', but open two abstractions for printing.
open2_for_printing :: (Bindable a, Bindable b, Nominal t) => Support -> Bind a (Bind b t) -> (a -> b -> t -> Support -> s) -> s
open2_for_printing sup term k = open_for_printing sup term $ \a term' sup' -> open_for_printing sup' term' $ \a' t sup'' -> k a a' t sup''

instance (Bindable a, Eq a, Nominal t, Eq t) => Eq (Bind a t) where
  (==) = bindable_eq

-- ----------------------------------------------------------------------
-- * Bindable instances

instance Bindable Atom where
  newtype Bind Atom t = BindA (BindAtom t)
  bindable_action π (BindA body) = BindA (π • body)
  bindable_support (BindA body) = support body
  bindable_eq (BindA b1) (BindA b2) = b1 == b2
  abst a t = BindA (atom_abst a t)
  open (BindA body) k = atom_open body k
  open_for_printing sup (BindA body) k = atom_open_for_printing default_names sup body k

instance (Bindable a) => Bindable (AtomPlus a t) where
  data Bind (AtomPlus a t) s = BindAP t (Bind a s)
  bindable_action π (BindAP t body) = BindAP t (π • body)
  bindable_support (BindAP t body) = support body
  bindable_eq (BindAP t1 b1) (BindAP t2 b2) = open b1 $ \a _ -> AtomPlus a t1 == AtomPlus a t2 && b1 == b2
  abst (AtomPlus a t) body = BindAP t (abst a body)
  open (BindAP t body) k = open body $ \a s -> k (AtomPlus a t) s
  open_for_printing sup (BindAP t body) k = open_for_printing sup body $ \a s -> k (AtomPlus a t) s

instance (AtomKind a) => Bindable (AtomOfKind a) where
  newtype Bind (AtomOfKind a) t = BindAK (BindAtom t)
  bindable_action π (BindAK body) = BindAK (π • body)
  bindable_support (BindAK body) = support body
  bindable_eq (BindAK b1) (BindAK b2) = b1 == b2
  abst a t = BindAK body where
    BindA body = (abst (to_atom a) t)
  open (BindAK body) k = open (BindA body) (\a t -> k (from_atom a) t)
  open_for_printing sup b@(BindAK body) k = atom_open_for_printing ns sup body (\a t -> k (from_atom a) t)
    where
      ns = names (un b)
      un :: Bind a t -> a
      un = undefined

instance Bindable () where
  newtype Bind () t = BindUnit t
  bindable_action π (BindUnit body) = BindUnit (π • body)
  bindable_support (BindUnit body) = support body
  bindable_eq (BindUnit b1) (BindUnit b2) = b1 == b2
  abst () t = BindUnit t
  open (BindUnit t) k = k () t
  open_for_printing sup (BindUnit body) k = k () body sup

instance (Bindable a, Bindable b) => Bindable (a, b) where
  newtype Bind (a, b) t = BindPair (Bind a (Bind b t))
  bindable_action π (BindPair body) = BindPair (π • body)
  bindable_support (BindPair body) = support body
  bindable_eq (BindPair b1) (BindPair b2) = b1 == b2
  abst (a, b) t = BindPair (a . b . t)
  open (BindPair body) k = open2 body $ \a b s -> k (a, b) s
  open_for_printing sup (BindPair body) k = open2_for_printing sup body $ \a b -> k (a, b)

instance (Bindable a, Bindable b, Bindable c) => Bindable (a, b, c) where
  newtype Bind (a, b, c) t = BindTriple (Bind ((a, b), c) t)
  bindable_action π (BindTriple body) = BindTriple (π • body)
  bindable_support (BindTriple body) = support body
  bindable_eq (BindTriple b1) (BindTriple b2) = b1 == b2
  abst (a, b, c) t = BindTriple (((a, b), c) . t)
  open (BindTriple body) k = open body $ \((a, b), c) -> k (a, b, c)
  open_for_printing sup (BindTriple body) k = open_for_printing sup body $ \((a, b), c) -> k (a, b, c)

instance (Bindable a, Bindable b, Bindable c, Bindable d) => Bindable (a, b, c, d) where
  newtype Bind (a, b, c, d) t = BindQuadruple (Bind (((a, b), c), d) t)
  bindable_action π (BindQuadruple body) = BindQuadruple (π • body)
  bindable_support (BindQuadruple body) = support body
  bindable_eq (BindQuadruple b1) (BindQuadruple b2) = b1 == b2
  abst (a, b, c, d) t = BindQuadruple ((((a, b), c), d) . t)
  open (BindQuadruple body) k = open body $ \(((a, b), c), d) -> k (a, b, c, d)
  open_for_printing sup (BindQuadruple body) k = open_for_printing sup body $ \(((a, b), c), d) -> k (a, b, c, d)

instance (Bindable a) => Bindable [a] where
  data Bind [a] t =
    BindNil t
    | BindCons (Bind a (Bind [a] t))
  bindable_action π (BindNil body) = BindNil (π • body)
  bindable_action π (BindCons body) = BindCons (π • body)
  bindable_support (BindNil body) = support body
  bindable_support (BindCons body) = support body
  bindable_eq (BindNil b1) (BindNil b2) = b1 == b2
  bindable_eq (BindCons b1) (BindCons b2) = b1 == b2
  bindable_eq _ _ = False
  abst [] t = BindNil t
  abst (a:as) t = BindCons (a . as . t)
  open (BindNil t) k = k [] t
  open (BindCons body) k = open2 body $ \a as -> k (a:as)
  open_for_printing sup (BindNil body) k = k [] body sup
  open_for_printing sup (BindCons body) k = open2_for_printing sup body $ \a as -> k (a:as)
  

-- ----------------------------------------------------------------------
-- * The 'Atomic' class

-- | A type class for atom types. There are two suggested ways users can
-- generate additional types of atoms.
--
-- 1. By defining some new empty type /X/ that is an instance of
-- 'AtomKind'.  Optionally, a list of suggested names for the new
-- atoms can be provided.  (These will be used as the names of bound
-- variables unless otherwise specified). Then 'AtomOfKind' /X/ is a
-- new type of atoms.
-- 
-- > data X
-- > instance AtomKind X where
-- >   suggested_names = ["x", "y", "z"]
-- > newtype MyName = AtomOfKind X
-- 
-- 2. By cloning an existing 'Atomic' type, deriving 'Atomic',
-- 'Nominal', 'NominalSupport', 'NominalShow', 'Eq', and 'Ord', and
-- defining a 'Show' instance:
--
-- > {-# LANGUAGE GeneralizedNewtypeDeriving #-}
-- >
-- > newtype Variable = Variable Atom
-- >   deriving (Atomic, Nominal, NominalSupport, NominalShow, Eq, Ord)
-- > 
-- > instance Show Variable where
-- >   showsPrec = nominal_showsPrec
class (Nominal a, NominalSupport a, NominalShow a, Eq a, Ord a, Show a, Bindable a) => Atomic a where
  to_atom :: a -> Atom
  from_atom :: Atom -> a

  -- | The default variable names for the atom type.
  names :: a -> NameSuggestion

show_atomic :: (Atomic a) => a -> String
show_atomic a = show_atom (to_atom a)

to_bindatom :: (Atomic a, Nominal t) => Bind a t -> BindAtom t
to_bindatom body = open body $ \a t -> atom_abst (to_atom a) t

from_bindatom :: (Atomic a, Nominal t) => BindAtom t -> Bind a t
from_bindatom body = atom_open body $ \a t -> (from_atom a . t)

instance Atomic Atom where
  to_atom = id
  from_atom = id
  names a = default_names

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
merge :: (Atomic a, Nominal t, Nominal s) => Bind a t -> Bind a s -> Bind a (t,s)
merge at as = from_bindatom (atom_merge (to_bindatom at) (to_bindatom as))

-- | A convenience function for constructing binders. 
--
-- > bind (\x -> t)
--
-- is a convenient way to write the atom abstraction (x.t),
-- where /x/ is a fresh variable.
bind :: (Atomic a, Nominal t) => (a -> t) -> Bind a t
bind body = bind_namelist ns body
  where
    ns = names (un body)
    un :: (a -> t) -> a
    un = undefined

-- | A version of 'bind' that also takes a suggested name for the bound atom.
bind_named :: (Atomic a, Nominal t) => String -> (a -> t) -> Bind a t
bind_named n = bind_namelist [n]

-- | A version of 'bind' that also take a list of suggested names for the bound atom.
bind_namelist :: (Atomic a, Nominal t) => NameSuggestion -> (a -> t) -> Bind a t
bind_namelist ns f = with_fresh_namelist ns (\x -> x . f x)

-- ----------------------------------------------------------------------
-- * High-level functions

-- | Perform a computation in the presence of a fresh atom. For
-- soundness, the programmer must ensure that the atom created does
-- not escape the body of the 'with_fresh' block. Thus, the following
-- uses are permitted:
--   
-- > with_fresh (\a -> f a == g a)
-- > with_fresh (\a -> a . f a b c)
--
-- Here is an example of what is /not/ permitted:
--
-- > with_fresh (\a -> a)
--
-- Technically, the correctness condition is that in an application
--
-- > with_fresh (\a -> body),
--
-- we must have /a/ # /body/ (see Pitts 2002 for more details on what
-- this means). Haskell does not enforce this restriction, but if a
-- program violates this, referential transparency may be violated,
-- which may, in the worst case, lead to unsound compiler
-- optimizations and undefined behavior.

-- Implementation note: the use of 'unsafePerformIO' makes this
-- function not referentially transparent. For example, we have
--
-- > with_fresh id /= with_fresh id.
--
-- However, if the above-mentioned correctness criterion is satisfied,
-- then the programs will be referentially transparent (and all
-- definable functions will be equivariant).
with_fresh :: (Atomic a) => (a -> t) -> t
with_fresh body = with_fresh_namelist ns body
  where
    ns = names (un body)
    un :: (a -> t) -> a
    un = undefined

-- | A version of 'with_fresh' that permits a suggested name to be
-- given to the atom. The name is only a suggestion, and will be
-- changed, if necessary, to avoid clashes.
with_fresh_named :: (Atomic a) => String -> (a -> t) -> t
with_fresh_named n body =
  with_fresh_atom_named n (\a -> body (from_atom a))

-- | A version of 'with_fresh' that permits a list of suggested names
-- to be specified. The first suitable name in the list will be used
-- if possible.
with_fresh_namelist :: (Atomic a) => NameSuggestion -> (a -> t) -> t
with_fresh_namelist ns body =
  with_fresh_atom_namelist ns (\a -> body (from_atom a))

-- ----------------------------------------------------------------------
-- * Display of nominal values


-- | 'NominalShow' is a helper class to support pretty-printing of
-- nominal values. Most 'Nominal' types are also 'NominalShow', with
-- the exception of function types (for which we cannot compute the
-- support).

class (NominalSupport t) => NominalShow t where
  -- | A nominal version of 'showsPrec'. This function takes as its
  -- first argument the support of /t/. This is then passed into the
  -- subterms, making printing O(/n/) instead of O(/n/^2).
  -- 
  -- It is recommended to define a 'NominalShow' instance, rather than
  -- a 'Show' instance, for each nominal type, and then define the
  -- 'Show' instance using 'nominal_showsPrec'. For example:
  --
  -- > instance Show MyType where
  -- >   showsPrec = nominal_showsPrec
  --
  -- Please note: in defining 'nominal_showsPrecSup', neither 'show'
  -- nor 'nominal_show' should be used for the recursive cases, or
  -- else the benefit of fast printing will be lost.
  nominal_showsPrecSup :: Support -> Int -> t -> ShowS

  -- | Like 'show', but for nominal types.
  nominal_show :: t -> String
  nominal_show t = nominal_showsPrecSup (support t) 0 t ""

  -- | The method 'nominal_showList' is provided to allow the programmer to
  -- give a specialised way of showing lists of values, similarly to
  -- 'showList'. Mostly this is used in the 'NominalShow' instance of
  -- the 'Char' type, so that strings are shown in double quotes,
  -- rather than as character lists.
  nominal_showList :: Support -> [t] -> ShowS
  nominal_showList sup ts = showString $
    "["
    ++ intercalate "," [ nominal_showsPrecSup sup 0 t "" | t <- ts ]
    ++ "]"

  default nominal_showsPrecSup :: (Generic t, GNominalShow (Rep t)) => Support -> Int -> t -> ShowS
  nominal_showsPrecSup sup d x = gnominal_showsPrecSup Pre sup d (from x)

-- | This function should be used in the definition of 'Show'
-- instances for nominal types, like this:
--
-- > instance Show MyType where
-- >   showsPrec = nominal_showsPrec
nominal_showsPrec :: (NominalShow t) => Int -> t -> ShowS
nominal_showsPrec d t = nominal_showsPrecSup (support t) d t

-- | This function can be used in defining NominalShow instances for
-- non-nominal types, where the instance should be derived from an
-- ordinary 'Show' instance.
simple_showsPrecSup :: (Show t) => Support -> Int -> t -> ShowS
simple_showsPrecSup dup d x = showString (show x)

-- | Since we hide (.) from the standard library, and it is not legal syntax
-- to write @Prelude..@, we provide '∘' as an alternate notation for
-- composition. This is particularly useful in defining 'showsPrec'
-- and 'nominal_showsPrecSup'.
(∘) :: (b -> c) -> (a -> b) -> (a -> c)
(g ∘ f) x = g (f x)

-- Primitive cases.
instance NominalSupport Atom where
  support a = support_atom a

instance NominalShow Atom where
  nominal_showsPrecSup sup d t = showString (show_atomic t)

instance NominalSupport Literal where
  support (Literal s) = support_string s

instance NominalShow Literal where
  nominal_showsPrecSup = simple_showsPrecSup

instance NominalSupport ()
instance NominalShow ()

-- Derived cases.
instance NominalSupport Integer where
  support t = support ()

instance NominalShow Integer where
  nominal_showsPrecSup = simple_showsPrecSup

instance NominalSupport Int where
  support t = support ()

instance NominalShow Int where
  nominal_showsPrecSup = simple_showsPrecSup

instance NominalSupport Char where
  support t = support ()

instance NominalShow Char where
  nominal_showsPrecSup = simple_showsPrecSup
  nominal_showList sup ts = shows ts

instance (NominalSupport t, NominalSupport s) => NominalSupport (t,s)
instance (NominalSupport t, NominalSupport s, NominalSupport r) => NominalSupport (t,s,r)
instance (NominalSupport t, NominalSupport s, NominalSupport r, NominalSupport q) => NominalSupport (t,s,r,q)
instance (NominalSupport t, NominalSupport s, NominalSupport r, NominalSupport q, NominalSupport p) => NominalSupport (t,s,r,q,p)
instance (NominalSupport t, NominalSupport s, NominalSupport r, NominalSupport q, NominalSupport p, NominalSupport o) => NominalSupport (t,s,r,q,p,o)
instance (NominalSupport t, NominalSupport s, NominalSupport r, NominalSupport q, NominalSupport p, NominalSupport o, NominalSupport n) => NominalSupport (t,s,r,q,p,o,n)

instance (NominalShow t, NominalShow s) => NominalShow (t,s)
instance (NominalShow t, NominalShow s, NominalShow r) => NominalShow (t,s,r)
instance (NominalShow t, NominalShow s, NominalShow r, NominalShow q) => NominalShow (t,s,r,q)
instance (NominalShow t, NominalShow s, NominalShow r, NominalShow q, NominalShow p) => NominalShow (t,s,r,q,p)
instance (NominalShow t, NominalShow s, NominalShow r, NominalShow q, NominalShow p, NominalShow o) => NominalShow (t,s,r,q,p,o)
instance (NominalShow t, NominalShow s, NominalShow r, NominalShow q, NominalShow p, NominalShow o, NominalShow n) => NominalShow (t,s,r,q,p,o,n)

-- ... and so on for tuples.

instance (NominalSupport t) => NominalSupport [t]

instance (NominalShow t) => NominalShow [t] where
  -- Lists require special treatment.
  nominal_showsPrecSup sup d ts = nominal_showList sup ts

instance (Ord k, Nominal k, Nominal v) => Nominal (Map k v) where
  π • map = Map.fromList [ (π • k, π • v) | (k, v) <- Map.toList map ]

instance (Ord k, NominalSupport k, NominalSupport v) => NominalSupport (Map k v) where
  support map = support (Map.toList map)

instance (Ord k, NominalShow k, NominalShow v) => NominalShow (Map k v) where
  nominal_showsPrecSup sup d m =
    showParen (d > 10) $
      showString "fromList " ∘ nominal_showsPrecSup sup 11 (Map.toList m)

instance (NominalSupport t) => NominalSupport (Defer t) where
  support t = support (force t)

instance (NominalShow t) => NominalShow (Defer t) where
  nominal_showsPrecSup sup d t = nominal_showsPrecSup sup d (force t)

instance (Bindable a, NominalSupport t) => NominalSupport (Bind a t) where
  support = bindable_support

instance (Bindable a, NominalShow a, NominalShow t) => NominalShow (Bind a t) where
  nominal_showsPrecSup sup d t =
    open_for_printing sup t $ \a s sup' ->
      showParen (d > 5) $
        showString (nominal_show a ++ " . " ++ nominal_showsPrecSup sup' 5 s "")

instance (Bindable a, NominalShow a, NominalShow t) => Show (Bind a t) where
  showsPrec = nominal_showsPrec

instance (AtomKind a) => Nominal (AtomOfKind a) where
  π • a = from_atom (π • to_atom a)

instance (AtomKind a) => NominalSupport (AtomOfKind a) where
  support a = support (add_default_names (names a) (to_atom a))

instance (AtomKind a) => NominalShow (AtomOfKind a) where
  nominal_showsPrecSup sup d t = showString (show_atomic t)

instance (AtomKind a) => Show (AtomOfKind a) where
  show = show_atomic

instance (AtomKind a) => Atomic (AtomOfKind a) where
  to_atom (AtomOfKind a) = a
  from_atom a = AtomOfKind a
  names f = suggested_names (un f)
    where
      un :: AtomOfKind a -> a
      un = undefined

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

-- ----------------------------------------------------------------------
-- ** Generic NominalShow instances

-- The implementation follows along similar lines as
-- "Generics.Deriving.Show".

-- | This type keeps track of which separator to use for the next tuple.
data Separator = Rec | Tup | Inf String | Pre

class GNominalShow f where
  gnominal_showsPrecSup :: Separator -> Support -> Int -> f a -> ShowS
  isNullary :: f a -> Bool
  isNullary x = False

instance GNominalShow V1 where
  -- Does not occur, because V1 is an empty type.
  gnominal_showsPrecSup sep sup d t s = undefined 
  
instance GNominalShow U1 where
  gnominal_showsPrecSup sep sup d t s = s
  isNullary x = True

instance (GNominalShow a, GNominalShow b) => GNominalShow (a :*: b) where
  gnominal_showsPrecSup sep sup d (x :*: y) = 
    gnominal_showsPrecSup sep sup prec x
    ∘ showString separator
    ∘ gnominal_showsPrecSup sep sup prec y
    where
      (separator, prec) = case sep of
        Rec -> (", ", d)
        Tup -> (",", d)
        Inf s -> (" " ++ s ++ " ", d)
        Pre -> (" ", 11)

instance (GNominalShow a, GNominalShow b) => GNominalShow (a :+: b) where
  gnominal_showsPrecSup sep sup d (L1 x) = gnominal_showsPrecSup sep sup d x
  gnominal_showsPrecSup sep sup d (R1 x) = gnominal_showsPrecSup sep sup d x

instance (GNominalShow a) => GNominalShow (M1 D c a) where
  gnominal_showsPrecSup sep sup d (M1 x) = gnominal_showsPrecSup sep sup d x

instance (GNominalShow a, Constructor c) => GNominalShow (M1 C c a) where
  gnominal_showsPrecSup sep sup d c@(M1 x) =
    case fixity of
      Prefix
        | isNullary x -> showString name
        | isTuple name -> showParen True $ gnominal_showsPrecSup Tup sup 0 x
        | conIsRecord c -> showParen (d > 10) $
          showString name
          ∘ showString " "
          ∘ showString "{"
          ∘ gnominal_showsPrecSup Rec sup 0 x
          ∘ showString "}"
        | otherwise -> showParen (d > 10) $
        showString name
        ∘ showString " "
        ∘ gnominal_showsPrecSup Pre sup 11 x
      Infix assoc prec -> showParen (d > prec) $
        gnominal_showsPrecSup (Inf name) sup (prec+1) x
    where
      name = conName c
      fixity = conFixity c
      isTuple ('(' : ',' : _) = True
      isTuple _ = False

instance (GNominalShow a, Selector c) => GNominalShow (M1 S c a) where
  gnominal_showsPrecSup sep sup d s@(M1 x)
    | null name = gnominal_showsPrecSup sep sup d x
    | otherwise =
      showString name
      ∘ showString " = "
      ∘ gnominal_showsPrecSup sep sup d x
    where
      name = selName s

instance (NominalShow a) => GNominalShow (K1 i a) where
  gnominal_showsPrecSup sep sup d (K1 x) = nominal_showsPrecSup sup d x
