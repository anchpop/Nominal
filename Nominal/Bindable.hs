{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

-- | This module provides a type class 'Bindable'. It contains things
-- (such as atoms, tuples of atoms, etc.) that can be abstracted by
-- binders (sometimes also called /patterns/).  Moreover, for each
-- bindable type /a/ and nominal type /t/, it defines a type 'Bind'
-- /a/ /t/ of abstractions.
--
-- We also provide some generic programming so that instances of
-- 'Bindable' can be automatically derived in most cases.
--
-- For example, @(/x/,/y/)./t/@ binds a pair of atoms in /t/. It is
-- roughly equivalent to @/x/./y/./t/@, except that it is of type
-- 'Bind' ('Atom', 'Atom') /t/ instead of 'Bind' 'Atom' ('Bind' 'Atom'
-- /t/).
--
-- If a binder contains repeated atoms, they are regarded as
-- distinct. For example, @(/x/,/x/).(/x/,/x/)@ is equivalent to
-- either @(/x/,/y/).(/x/,/x/)@ or @(/x/,/y/).(/y/,/y/)@. In such
-- cases, the binding order is unspecified and should not be relied
-- upon.

module Nominal.Bindable where

import Prelude hiding ((.))
import Control.Applicative
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import GHC.Generics

import Nominal.ConcreteNames
import Nominal.Atom
import Nominal.Permutation
import Nominal.Nominal
import Nominal.NominalSupport

-- ----------------------------------------------------------------------
-- * Bind lists of atoms

-- | The type of abstractions of a list of atoms.
data BindAtomList t =
  BindNil t
  | BindCons (BindAtom (BindAtomList t))
  deriving (Generic, Nominal)

-- | Abstract a list of atoms in a term.
atomlist_abst :: [Atom] -> t -> BindAtomList t
atomlist_abst [] t = BindNil t
atomlist_abst (a:as) t = BindCons (atom_abst a (atomlist_abst as t))

-- | Open a list abstraction.
atomlist_open :: (Nominal t) => BindAtomList t -> ([Atom] -> t -> s) -> s
atomlist_open (BindNil t) k = k [] t
atomlist_open (BindCons body) k =
  atom_open body $ \a body2 ->
  atomlist_open body2 $ \as t ->
  k (a:as) t

-- | Open a list abstraction for printing.
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

-- | An abstract type for encapsulating the behavior of binders.
data Rebind a =
  -- | The behavior of a binder is determined by two things: the list
  -- of bound atom occurrences (binding sites), and a renaming
  -- function that takes such a list of atoms and returns an
  -- alpha-renamed version of the binder. For efficiency, the
  -- renaming function is stateful: it also returns a list of atoms
  -- not yet used.
  --
  -- The binding sites must be serialized in some deterministic order,
  -- and must be accepted in the same corresponding order by the
  -- renaming function.
  --
  -- If an atom occurs at multiple binding sites of the pattern, it must
  -- be serialized multiple times. The corresponding renaming function
  -- must accept fresh atoms and put them into the respective binding
  -- sites.
  --
  -- ==== Examples:
  --
  -- > binding x = Rebind [x] (\(x:zs) -> (x, zs))
  -- >
  -- > binding (x, y) = Rebind [x, y] (\(x:y:zs) -> ((x, y), zs))
  -- >
  -- > binding (x, NoBind(y)) = Rebind [x] (\(x:zs) -> ((x, NoBind(y)), zs))
  -- >
  -- > binding (x, x, y) = Rebind [x, x, y] (\(x:x':y:zs) -> ((x, x', y), zs))
  Rebind [Atom] ([Atom] -> (a, [Atom]))

instance Functor Rebind where
  fmap = rebind_map

instance Applicative Rebind where
  pure = nobinding
  f <*> b = rebind_map (\(f,b) -> f b) (rebind_pair f b)
  
-- | Constructor for non-binding patterns.
nobinding :: a -> Rebind a
nobinding a = Rebind [] (\xs -> (a, xs))

-- | Constructor for a pattern binding a single atom.
atom_binding :: Atom -> Rebind Atom
atom_binding a = Rebind [a] (\(a:xs) -> (a, xs))

-- | Combinator for constructing tuple binders.
rebind_pair :: Rebind a -> Rebind b -> Rebind (a,b)
rebind_pair (Rebind xs f) (Rebind ys g) = Rebind (xs ++ ys) h where
  h zs = ((a,b), zs'') where
    (a, zs') = f zs
    (b, zs'') = g zs'

-- | Map a function over a 'Rebind'.
rebind_map :: (a -> b) -> Rebind a -> Rebind b
rebind_map f (Rebind xs g) = Rebind xs h where
  h xs = (f a, ys) where
    (a, ys) = g xs

-- ----------------------------------------------------------------------
-- * The Bindable class

-- | 'Bind' /a/ /t/ is the type of atom abstractions, denoted [/A/]/T/
-- in the nominal logic literature. Its elements are pairs (/a/,/t/)
-- modulo alpha-equivalence. We also write /a/'.'/t/ for such an
-- equivalence class of pairs. For full technical details on what this
-- means, see Definition 4 of [Pitts 2002].

-- Implementation note: [Atom] must contain the same number of atoms
-- as are bound in BindAtomList.
data Bind a t =
  Bind ([Atom] -> a) (BindAtomList t)

-- | A type is 'Bindable' if its elements can be abstracted by
-- binders. Such elements are also called /patterns/. Examples include
-- atoms, tuples of atoms, list of atoms, etc.
class (Nominal a) => Bindable a where
  -- | A function that encapsulates the behavior of a pattern. New
  -- patterns can be constructed using the 'Applicative' structure of
  -- 'Rebind'.
  --
  -- ==== Example:
  --
  -- Here is how we could define a 'Bindable' instance for the
  -- @MyTree@ type. It is convenient, though not essential, to use
  -- "applicative do" notation.
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
  -- 'nobinding' in the recursive call. See 'NoBind' for further
  -- discussion of non-binding patterns.

  binding :: a -> Rebind a
  
  default binding :: (Generic a, GBindable (Rep a)) => a -> Rebind a
  binding x = rebind_map to (gbinding (from x))

-- | Atom abstraction: /a/'.'/t/ represents the equivalence class of
-- pairs (/a/,/t/) modulo alpha-equivalence. 
--
-- We use the infix operator @(@'.'@)@, which is normally bound to
-- function composition in the standard Haskell library. Thus, nominal
-- programs should import the standard library like this:
-- 
-- > import Prelude hiding ((.))
(.) :: (Bindable a) => a -> t -> Bind a t
a . t = Bind (fst ∘ f) (atomlist_abst xs t)
  where
    Rebind xs f = binding a
infixr 5 .

-- | An alternative non-infix notation for @(@'.'@)@. This can be
-- useful when using qualified module names, as \"̈@Nominal..@\" is not
-- valid syntax.
abst :: (Bindable a) => a -> t -> Bind a t
abst = (.)
  
-- | Destructor for atom abstraction. In an ideal programming idiom,
-- we would be able to define a function on atom abstractions by
-- pattern matching like this:
--
-- > f (a.s) = body.
--
-- Haskell doesn't let us provide this syntax, but using the 'open'
-- function, we can equivalently write:
--
-- > f t = open t (\a s -> body).
--
-- Each time an abstraction is opened, /a/ is guaranteed to be a fresh
-- atom.  To guarantee soundness (referential transparency and
-- equivariance), the body is subject to the same restriction as
-- 'Nominal.with_fresh', namely, /a/ must be fresh for the body (in symbols
-- /a/ # /body/).
open :: (Bindable a, Nominal t) => Bind a t -> (a -> t -> s) -> s
open (Bind f body) k =
  atomlist_open body (\ys t -> k (f ys) t)
  
-- | A variant of 'open' which moreover attempts to choose a name for
-- the bound atom that does not clash with any free name in its
-- scope. This function is mostly useful for building custom
-- pretty-printers for nominal terms. Except in pretty-printers, it is
-- equivalent to 'open'.
--
-- Usage:
--
-- > open_for_printing sup t (\x s sup' -> body)
--
-- Here, /sup/ = 'support' /t/ (this requires a 'NominalSupport'
-- instance). For printing to be efficient (roughly O(/n/)), the
-- support must be pre-computed in a bottom-up fashion, and then
-- passed into each subterm in a top-down fashion (rather than
-- re-computing it at each level, which would be O(/n/²)).  For this
-- reason, 'open_for_printing' takes the support of /t/ as an
-- additional argument, and provides /sup'/, the support of /s/, as an
-- additional parameter to the body.
open_for_printing :: (Bindable a, Nominal t) => Support -> Bind a t -> (a -> t -> Support -> s) -> s
open_for_printing sup (Bind f body) k =
  atomlist_open_for_printing sup body (\ys t sup' -> k (f ys) t sup')

-- | Function composition.
-- 
-- Since we hide (.) from the standard library, and the fully
-- qualified name of the "Prelude"'s dot operator, \"̈@Prelude..@\", is
-- not legal syntax, we provide '∘' as an alternate notation for
-- composition.
(∘) :: (b -> c) -> (a -> b) -> (a -> c)
(g ∘ f) x = g (f x)

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
-- * Non-binding patterns

-- | The type constructor 'NoBind' permits data of arbitrary types
-- (including nominal types) to be embedded in binders without
-- becoming bound. For example, in the term
--
-- > m = (a, NoBind b).(a,b),
--
-- the atom /a/ is bound, but the atom /b/ remains free. Thus, /m/ is
-- alpha-equivalent to @(x, NoBind b).(x,b)@, but not to
-- @(x, NoBind y).(x,y)@.
--
-- A typical use for this is using contexts as binders. A
-- /context/ is a map from atoms to some data (for example, a
-- /typing context/ is a map from atoms to types, and an
-- /evaluation context/ is a map from atoms to values). If we define
-- contexts like this:
--
-- > type Context t = Map Atom (NoBind t),
--
-- then we can use contexts as binders. Specifically, if Γ = {/x/₁
-- ↦ /A/₁, …, /x/ₙ ↦ /A/ₙ} is a context, then (Γ . /t/) binds the
-- context to a term /t/. This means, /x/₁,…,/x/ₙ are bound in /t/,
-- but not any atoms that occur in /A/₁,…,/A/ₙ. Without the use of
-- 'NoBind', any atoms occuring on /A/₁,…,/A/ₙ would have been bound
-- as well.
--
-- Even though atoms under 'NoBind' are not /binding/, they can still
-- be /bound/ by other binders. For example, the term @/x/.(/x/,
-- 'NoBind' /x/)@ is alpha-equivalent to @/y/.(/y/, 'NoBind'
-- /y/)@. Another way to say this is that 'NoBind' has a special
-- behavior on the left, but not on the right of a dot.

newtype NoBind t = NoBind t
  deriving (Show, Eq, Ord, Generic, Nominal, NominalSupport)

-- ----------------------------------------------------------------------
-- * Bindable instances

-- $ Most of the time, instances of 'Bindable' should be derived using
-- @deriving (Generic, Nominal, Bindable)@, as in this example:
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
-- In this case, a binder (/x/./t/) is equivalent to an ordinary pair
-- (/x/,/t/), since there is no bound atom that could be renamed.

-- | A helper function for defining 'Bindable' instances
-- for /non-nominal types only/. It can be used like this:
--
-- > instance Bindable MyType where
-- >   binding = basic_binding
basic_binding :: a -> Rebind a
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

-- Special instances

instance (Ord k, Bindable k, Bindable v) => Bindable (Map k v) where
  binding m = rebind_map Map.fromList (binding (Map.toList m))

instance (Ord k, Bindable k) => Bindable (Set k) where
  binding s = rebind_map Set.fromList (binding (Set.toList s))

-- ----------------------------------------------------------------------
-- * Generic programming for Bindable

-- | A version of the 'Bindable' class suitable for generic programming.
class GBindable f where
  gbinding :: f a -> Rebind (f a)

instance GBindable V1 where
  gbinding a = undefined -- never occurs, because V1 is empty

instance GBindable U1 where
  gbinding = basic_binding

instance (GBindable a, GBindable b) => GBindable (a :*: b) where
  gbinding (a :*: b) = rebind_map (\(x,y) -> x :*: y) (rebind_pair (gbinding a) (gbinding b))

instance (GBindable a, GBindable b) => GBindable (a :+: b) where
  gbinding (L1 a) = rebind_map L1 (gbinding a)
  gbinding (R1 a) = rebind_map R1 (gbinding a)

instance (GBindable a) => GBindable (M1 i c a) where
  gbinding (M1 a) = rebind_map M1 (gbinding a)
  
instance (Bindable a) => GBindable (K1 i a) where
  gbinding (K1 a) = rebind_map K1 (binding a)
