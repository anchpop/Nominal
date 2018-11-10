{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}

-- | This module provides a type class 'Bindable'. It contains things
-- (such as atoms, tuples of atoms, etc.) that can be abstracted by
-- binders.  Moreover, for each bindable type /a/ and nominal type
-- /t/, it defines a type 'Bind' /a/ /t/ of abstractions.
--
-- We also provide some generic programming so that instances of
-- 'Bindable' can be automatically derived in many cases.
--
-- For example, @(/x/,/y/)./t/@ binds a pair of atoms in /t/. It is
-- roughly equivalent to @/x/./y/./t/@, except that it is of type
-- 'Bind' ('Atom', 'Atom') /t/ instead of 'Bind' 'Atom' ('Bind' 'Atom'
-- /t/).
--
-- If a binder contains repeated atoms, they are regarded as
-- distinct. The binder is treated as if one atom occurrence was bound
-- at a time, in some fixed but unspecified order. For example,
-- @(/x/,/x/).(/x/,/x/)@ is equivalent to either @(/x/,/y/).(/x/,/x/)@
-- or @(/x/,/y/).(/y/,/y/)@. Which of the two alternatives is chosen
-- is implementation specific and user code should not rely on the
-- order of abstractions in such cases.
--
-- This module exposes implementation details of the Nominal library,
-- and should not normally be imported. Users of the library should
-- only import the top-level module "Nominal".

module Nominal.Bindable where

import Prelude hiding ((.))
import GHC.Generics

import Nominal.Atom
import Nominal.Nominal
import Nominal.NominalSupport

-- ----------------------------------------------------------------------
-- * Binding lists of atoms

-- | The type of abstractions of a list of atoms. It is equivalent to
-- @'Bind' ['Atom'] /t/@, but has a more low-level implementation.
data BindAtomList t =
  BindNil t
  | BindCons (BindAtom (BindAtomList t))
  deriving (Generic, Nominal)

-- | Abstract a list of atoms in a term.
atomlist_abst :: [Atom] -> t -> BindAtomList t
atomlist_abst [] t = BindNil t
atomlist_abst (a:as) t = BindCons (atom_abst a (atomlist_abst as t))

-- | Open a list abstraction.
--
-- The correct use of this function is subject to Pitts's freshness
-- condition.
atomlist_open :: (Nominal t) => BindAtomList t -> ([Atom] -> t -> s) -> s
atomlist_open (BindNil t) k = k [] t
atomlist_open (BindCons body) k =
  atom_open body $ \a body2 ->
  atomlist_open body2 $ \as t ->
  k (a:as) t

-- | Open a list abstraction for printing.
--
-- The correct use of this function is subject to Pitts's freshness
-- condition.
atomlist_open_for_printing :: (Nominal t) => Support -> BindAtomList t -> ([Atom] -> t -> Support -> s) -> s
atomlist_open_for_printing sup (BindNil t) k = k [] t sup
atomlist_open_for_printing sup (BindCons body) k =
  atom_open_for_printing sup body $ \a body2 sup' ->
  atomlist_open_for_printing sup' body2 $ \as t sup'' ->
  k (a:as) t sup''

-- | Merge a pair of list abstractions. If the lists are of different
-- lengths, return 'Nothing'.
atomlist_merge :: (Nominal t, Nominal s) => BindAtomList t -> BindAtomList s -> Maybe (BindAtomList (t,s))
atomlist_merge (BindNil t) (BindNil s) = Just (BindNil (t,s))
atomlist_merge (BindCons body1) (BindCons body2) =
  atom_open (atom_merge body1 body2) $ \x (t,s) -> do
    ts <- atomlist_merge t s
    return (BindCons (atom_abst x ts))
atomlist_merge _ _ = Nothing

-- ----------------------------------------------------------------------
-- * Binder combinators

-- | A representation of binders of type /a/. This is an abstract
-- type with no exposed structure. The only way to construct a value
-- of type 'NominalBinder' /a/ is through the 'Applicative' interface and by
-- using the functions 'binding' and 'nobinding'.

data NominalBinder a =
  NominalBinder [Atom] ([Atom] -> (a, [Atom]))

-- $ Implementation note: The behavior of a binders is determined by two
-- things: the list of bound atom occurrences (binding sites), and a
-- renaming function that takes such a list of atoms and returns a
-- term. For efficiency, the renaming function is stateful: it also
-- returns a list of atoms not yet used.
--
-- The binding sites must be serialized in some deterministic order,
-- and must be accepted in the same corresponding order by the
-- renaming function.
--
-- If an atom occurs at multiple binding sites, it must be serialized
-- multiple times. The corresponding renaming function must accept
-- fresh atoms and put them into the respective binding sites.
--
-- ==== Examples:
--
-- > binding x = NominalBinder [x] (\(x:zs) -> (x, zs))
-- >
-- > binding (x, y) = NominalBinder [x, y] (\(x:y:zs) -> ((x, y), zs))
-- >
-- > binding (x, NoBind y) = NominalBinder [x] (\(x:zs) -> ((x, NoBind y), zs))
-- >
-- > binding (x, x, y) = NominalBinder [x, x, y] (\(x:x':y:zs) -> ((x, x', y), zs))

-- | Constructor for non-binding binders. This can be used to mark
-- non-binding subterms when defining a 'Bindable' instance. See
-- <#CUSTOM "Defining custom instances"> for examples.
nobinding :: a -> NominalBinder a
nobinding a = NominalBinder [] (\xs -> (a, xs))

-- | Constructor for a binder binding a single atom.
atom_binding :: Atom -> NominalBinder Atom
atom_binding a = NominalBinder [a] (\(a:xs) -> (a, xs))

-- | Map a function over a 'NominalBinder'.
binder_map :: (a -> b) -> NominalBinder a -> NominalBinder b
binder_map f (NominalBinder xs g) = NominalBinder xs h where
  h xs = (f a, ys) where
    (a, ys) = g xs

-- | Combinator giving 'NominalBinder' an applicative structure. This
-- is used for constructing tuple binders.
binder_app :: NominalBinder (a -> b) -> NominalBinder a -> NominalBinder b
binder_app (NominalBinder xs f) (NominalBinder ys g) = NominalBinder (xs ++ ys) h where
  h zs = (a b, zs'') where
    (a, zs') = f zs
    (b, zs'') = g zs'

instance Functor NominalBinder where
  fmap = binder_map

instance Applicative NominalBinder where
  pure = nobinding
  f <*> b = binder_app f b
  
-- ----------------------------------------------------------------------
-- * The Bindable class

-- | 'Bind' /a/ /t/ is the type of /abstractions/, denoted [/A/]/T/
-- in the nominal logic literature. Its elements are pairs (/a/,/t/)
-- modulo alpha-equivalence. We also write /a/'.'/t/ for such an
-- equivalence class of pairs. For full technical details on what this
-- means, see Definition 4 of
-- <#PITTS2003 [Pitts 2003]>.

data Bind a t =
  Bind ([Atom] -> a) (BindAtomList t)

-- | A type is 'Bindable' if its elements can be abstracted. Such
-- elements are also called /binders/, or sometimes /patterns/.
-- Examples include atoms, tuples of atoms, list of atoms, etc.
--
-- In most cases, instances of 'Nominal' can be automatically
-- derived. See <#DERIVING "Deriving generic instances"> for
-- information on how to do so, and
-- <#CUSTOM "Defining custom instances"> for how to write custom
-- instances.
class (Nominal a) => Bindable a where
  -- | A function that maps a term to a binder. New binders can be
  -- constructed using the 'Applicative' structure of 'NominalBinder'.
  -- See <#CUSTOM "Defining custom instances"> for examples.
  binding :: a -> NominalBinder a
  
  default binding :: (Generic a, GBindable (Rep a)) => a -> NominalBinder a
  binding x = gbinding (from x) to

-- | Constructor for abstractions. The term /a/'.'/t/ represents the
-- equivalence class of pairs (/a/,/t/) modulo alpha-equivalence.
--
-- We use the infix operator @(@'.'@)@, which is normally bound to
-- function composition in the standard Haskell library. Thus, nominal
-- programs should import the standard library like this:
-- 
-- > import Prelude hiding ((.))
--
-- Note that @(@'.'@)@ is a abstraction operator of the
-- /object language/ (i.e., whatever datatype you are defining), not
-- of the /metalanguage/ (i.e., Haskell). A term such as /a/'.'/t/
-- only makes sense if the variable /a/ is already defined to be a
-- particular atom.  Thus, abstractions are often used in the context
-- of a scoped operation such as 'Nominal.with_fresh' or on the
-- right-hand side of an abstraction pattern match, as in the
-- following examples:
--
-- > with_fresh (\a -> a.a)
-- >
-- > subst m z (Abs (x :. t)) = Abs (x . subst m z t)
--
-- For building an abstraction by using a binder of the metalanguage,
-- see also the function 'Nominal.bind'.
(.) :: (Bindable a, Nominal t) => a -> t -> Bind a t
a . t = Bind (fst ∘ f) (atomlist_abst xs t)
  where
    NominalBinder xs f = binding a
infixr 5 .

-- | A pattern matching syntax for abstractions. The pattern
-- @(x :. t)@ is called an /abstraction pattern/. It matches any term
-- of type @('Bind' /a/ /b/)@. The result of matching the pattern
-- @(x :. t)@ against a value /y/'.'/s/ is to bind /x/ to a fresh name
-- and /t/ to a value such that /x/'.'/t/ = /y/'.'/s/.
-- Note that a different fresh /x/ is chosen each time an abstraction
-- patterns is used.
-- Here are some examples:
--
-- > foo (x :. t) = body
-- > 
-- > let (x :. t) = s in body
-- > 
-- > case t of
-- >   Var v -> body1
-- >   App m n -> body2
-- >   Abs (x :. t) -> body3
--   
-- Like all patterns, abstraction patterns can be nested. For example:
--
-- > foo1 (a :. b :. t) = ...
-- >
-- > foo2 (x :. (s,t)) = (x.s, x.t)
-- >
-- > foo3 (Abs (x :. Var y))
-- >   | x == y    = ...
-- >   | otherwise = ...
-- >
--
-- The correct use of abstraction patterns is subject to
-- <#CONDITION Pitts's freshness condition>.
-- Thus, for example, the following are permitted
--
-- > let (x :. t) = s in x.t,
-- > let (x :. t) = s in f x t == g x t,
--
-- whereas the following is not permitted:
--
-- > let (x :. t) = s in (x,t).
--
-- See <#CONDITION "Pitts's freshness condition"> for more details.
pattern (:.) :: (Nominal b, Bindable a) => a -> b -> Bind a b 
pattern a :. t <- ((\body -> open body (\a t -> (a,t))) -> (a, t))
 where
   a :. t = a . t
infixr 5 :.

-- | An alternative non-infix notation for @(@'.'@)@. This can be
-- useful when using qualified module names, because \"̈@Nominal..@\" is not
-- valid syntax.
abst :: (Bindable a, Nominal t) => a -> t -> Bind a t
abst = (.)

-- | An alternative notation for abstraction patterns.
--
-- > f t = open t (\x s -> body)
--
-- is precisely equivalent to
--
-- > f (x :. s) = body.
--
-- The correct use of this function is subject to
-- <#CONDITION Pitts's freshness condition>.
open :: (Bindable a, Nominal t) => Bind a t -> (a -> t -> s) -> s
open (Bind f body) k =
  atomlist_open body (\ys t -> k (f ys) t)
  
-- | A variant of 'open' which moreover chooses a name for the
-- bound atom that does not clash with any free name in its
-- scope. This function is mostly useful for building custom
-- pretty-printers for nominal terms. Except in pretty-printers, it is
-- equivalent to 'open'.
--
-- Usage:
--
-- > open_for_printing sup t (\x s sup' -> body)
--
-- Here, /sup/ = 'support' /t/ (this requires a 'NominalSupport'
-- instance). For printing to be efficient (roughly O(/n/)), the
-- support must be pre-computed in a bottom-up fashion, and then
-- passed into each subterm in a top-down fashion (rather than
-- re-computing it at each level, which would be O(/n/²)).  For this
-- reason, 'open_for_printing' takes the support of /t/ as an
-- additional argument, and provides /sup'/, the support of /s/, as an
-- additional parameter to the body.
--
-- The correct use of this function is subject to
-- <#CONDITION Pitts's freshness condition>.
open_for_printing :: (Bindable a, Nominal t) => Support -> Bind a t -> (a -> t -> Support -> s) -> s
open_for_printing sup (Bind f body) k =
  atomlist_open_for_printing sup body (\ys t sup' -> k (f ys) t sup')

instance (Nominal a, Nominal t, Eq a, Eq t) => Eq (Bind a t) where
  Bind f1 body1 == Bind f2 body2 =
    case atomlist_merge body1 body2 of
      Nothing -> False
      Just bodies ->
        atomlist_open bodies $ \xs (t1, t2) ->
          t1 == t2 && f1 xs == f2 xs

instance (Bindable a, Nominal t) => Nominal (Bind a t) where
  π • (Bind f body) = Bind (π • f) (π • body)

instance (Bindable a, NominalSupport a, NominalSupport t) => NominalSupport (Bind a t) where
  support (Bind f body) = atomlist_open body $ \xs t ->
    support_deletes xs (support (f xs, t))

-- ----------------------------------------------------------------------
-- * Non-binding binders

-- | The type constructor 'NoBind' permits data of arbitrary types
-- (including nominal types) to be embedded in binders without
-- becoming bound. For example, in the term
--
-- > m = (a, NoBind b).(a,b),
--
-- the atom /a/ is bound, but the atom /b/ remains free. Thus, /m/ is
-- alpha-equivalent to @(x, NoBind b).(x,b)@, but not to
-- @(x, NoBind c).(x,c)@.
--
-- A typical use case is using contexts as binders. A /context/ is a
-- map from atoms to some data (for example, a /typing context/ is a
-- map from atoms to types, and an /evaluation context/ is a map from
-- atoms to values). If we define contexts like this:
--
-- > type Context t = [(Atom, NoBind t)]
--
-- then we can use contexts as binders. Specifically, if
-- Γ = {/x/₁ ↦ /A/₁, …, /x/ₙ ↦ /A/ₙ} is a context, then (Γ . /t/)
-- binds the context to a term /t/. This means, /x/₁,…,/x/ₙ are bound
-- in /t/, but not any atoms that occur in /A/₁,…,/A/ₙ. Without the
-- use of 'NoBind', any atoms occurring on /A/₁,…,/A/ₙ would have been
-- bound as well.
--
-- Even though atoms under 'NoBind' are not /binding/, they can still
-- be /bound/ by other binders. For example, the term @/x/.(/x/,
-- 'NoBind' /x/)@ is alpha-equivalent to
-- @/y/.(/y/, 'NoBind' /y/)@. Another way to say this is that 'NoBind'
-- has a special behavior on the left, but not on the right of a dot.

newtype NoBind t = NoBind t
  deriving (Show, Eq, Ord, Generic, Nominal, NominalSupport)

-- ----------------------------------------------------------------------
-- * Bindable instances

-- $ Most of the time, instances of 'Bindable' should be derived using
-- @deriving (Generic, Nominal, Bindable)@, as in this example:
--
-- > {-# LANGUAGE DeriveGeneric #-}
-- > {-# LANGUAGE DeriveAnyClass #-}
-- >
-- > data Term = Var Atom | App Term Term | Abs (Bind Atom Term)
-- >   deriving (Generic, Nominal, Bindable)
--
-- In the case of non-nominal types (typically base types such as
-- 'Double'), a 'Bindable' instance can be defined using
-- 'basic_binding':
--
-- > instance Bindable MyType where
-- >   binding = basic_binding
--
-- In this case, an abstraction (/x/./t/) is equivalent to an ordinary
-- pair (/x/,/t/), since there is no bound atom that could be renamed.

-- | A helper function for defining 'Bindable' instances
-- for non-nominal types.
basic_binding :: a -> NominalBinder a
basic_binding = nobinding

-- Base cases

instance Bindable Atom where
  binding = atom_binding

instance Bindable Bool where
  binding = basic_binding
  
instance Bindable Integer where
  binding = basic_binding
  
instance Bindable Int where
  binding = basic_binding
  
instance Bindable Char where
  binding = basic_binding
  
instance Bindable Double where
  binding = basic_binding
  
instance Bindable Float where
  binding = basic_binding
  
instance Bindable Ordering where
  binding = basic_binding
  
instance Bindable (Basic t) where
  binding = basic_binding

instance Bindable Literal where
  binding = basic_binding

instance (Nominal t) => Bindable (NoBind t) where
  binding = nobinding
  
-- Generic instances
  
instance (Bindable a) => Bindable [a]
instance Bindable ()
instance (Bindable a, Bindable b) => Bindable (a, b)
instance (Bindable a, Bindable b, Bindable c) => Bindable (a, b, c)
instance (Bindable a, Bindable b, Bindable c, Bindable d) => Bindable (a, b, c, d)
instance (Bindable a, Bindable b, Bindable c, Bindable d, Bindable e) => Bindable (a, b, c, d, e)
instance (Bindable a, Bindable b, Bindable c, Bindable d, Bindable e, Bindable f) => Bindable (a, b, c, d, e, f)
instance (Bindable a, Bindable b, Bindable c, Bindable d, Bindable e, Bindable f, Bindable g) => Bindable (a, b, c, d, e, f, g)
instance (Bindable a) => Bindable (Maybe a)
instance (Bindable a, Bindable b) => Bindable (Either a b)

-- ----------------------------------------------------------------------
-- * Generic programming for Bindable

-- | A specialized combinator. Although this functionality is
-- expressible in terms of the applicative structure, we give a custom
-- CPS-based implementation for performance reasons. It improves the
-- overall performance by 14% (time) and 16% (space) in a typical
-- benchmark.
binder_gpair :: NominalBinder (a x) -> NominalBinder (b x) -> ((a :*: b) x -> c) -> NominalBinder c
binder_gpair (NominalBinder xs f) (NominalBinder ys g) k = NominalBinder (xs ++ ys) h where
  h zs = (k (a :*: b), zs'') where
    (a, zs') = f zs
    (b, zs'') = g zs'

-- | A version of the 'Bindable' class suitable for generic programming.
class GBindable f where
  gbinding :: f a -> (f a -> b) -> NominalBinder b

instance GBindable V1 where
  gbinding = undefined -- never occurs, because V1 is empty

instance GBindable U1 where
  gbinding a k = NominalBinder [] (\xs -> (k a, xs))

instance (GBindable a, GBindable b) => GBindable (a :*: b) where
  gbinding (a :*: b) k =
    binder_gpair (gbinding a id) (gbinding b id) k

instance (GBindable a, GBindable b) => GBindable (a :+: b) where
  gbinding (L1 a) k = gbinding a (\a -> k (L1 a))
  gbinding (R1 a) k = gbinding a (\a -> k (R1 a))

instance (GBindable a) => GBindable (M1 i c a) where
  gbinding (M1 a) k = gbinding a (\a -> k (M1 a))
  
instance (Bindable a) => GBindable (K1 i a) where
  gbinding (K1 a) k = binder_map k (K1 <$> binding a)

-- ----------------------------------------------------------------------
-- * Miscellaneous

-- | Function composition.
-- 
-- Since we hide (.) from the standard library, and the fully
-- qualified name of the "Prelude"'s dot operator, \"̈@Prelude..@\", is
-- not legal syntax, we provide '∘' as an alternate notation for
-- composition.
(∘) :: (b -> c) -> (a -> b) -> (a -> c)
(g ∘ f) x = g (f x)
