{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

-- | This module provides a type class 'Bindable'. It contains things
-- (such as atoms, tuples of atoms, etc.) that can be abstracted by
-- binders.  Moreover, for each bindable type /a/ and nominal type
-- /t/, it defines a type 'Bind' /a/ /t/ of abstractions.
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
-- * The Bindable class

-- | 'Bind' /a/ /t/ is the type of atom abstractions, denoted [/a/]/t/
-- in the nominal logic literature. Its elements are pairs (/a/,/t/)
-- modulo alpha-equivalence. We also write /a/'.'/t/ for such an
-- equivalence class of pairs. For more details on what this means,
-- see Definition 4 of [Pitts 2002].

-- Implementation note: [Atom] must contain the same number of atoms
-- as are bound in BindAtomList.
data Bind a t =
  Bind ([Atom] -> a) (BindAtomList t)

-- | A type is 'Bindable' if its elements can be abstracted by
-- binders. Such elements are also called /patterns/. Examples include
-- atoms, tuples of atoms, list of atoms, etc.
class (Nominal a) => Bindable a where
  -- | Return the list of atoms bound by the pattern, and a renaming
  -- function. The atoms must be returned in some deterministic order,
  -- and must be accepted in the same order by the renaming function.
  -- If an atom occurs in multiple binding sites of the pattern, it
  -- must be listed multiple times.
  --
  -- Examples:
  --
  -- > binding (x, y, Unbound(z)) = ([x,y], \[x',y'] -> (x', y', Unbound(z)))
  -- >
  -- > binding (x, x, y, y) = ([x,x,y,y], \[x',x'',y',y''] -> (x',x'',y',y''))
  binding :: a -> ([Atom], [Atom] -> a)

  default binding :: (Generic a, GBindable (Rep a)) => a -> ([Atom], [Atom] -> a)
  binding x = (xs, g)
    where
      (xs, f) = gbinding (from x)
      g x = to (f x)

-- | Atom abstraction: /a/'.'/t/ represents the equivalence class of
-- pairs (/a/,/t/) modulo alpha-equivalence. 
--
-- We use the infix operator @(@'.'@)@, which is normally bound to
-- function composition in the standard Haskell library. Thus, nominal
-- programs should import the standard library like this:
-- 
-- > import Prelude hiding ((.))
(.) :: (Bindable a) => a -> t -> Bind a t
a . t = Bind f (atomlist_abst xs t)
  where
    (xs, f) = binding a
infixr 5 .

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
  
-- | A variant of 'open' which moreover attempts to choose a name
-- for the bound atom that does not clash with any free name in its
-- scope. This requires a 'NominalSupport' instance. It is mostly
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
-- * Bindable instances

-- $ Most of the time, instances of 'Bindable' should be derived using
-- @deriving (Generic, Nominal, Bindable)@, as in this example:
--
-- > data Term = Var Atom | App Term Term | Abs (Bind Atom Term)
-- >   deriving (Generic, Nominal, Bindable)
--
-- In the case of non-nominal types (typically base types such as
-- 'Double'), a 'Bindable' instance can be defined using
-- 'base_binding':
--
-- > instance Bindable MyType where
-- >   binding = base_binding
--
-- In this case, a binder (/x/./t/) is equivalent to an ordinary pair
-- (/x/,/t/), since there is no bound atom that could be renamed.

-- | A helper function for defining 'Bindable' instances
-- for /non-nominal types only/. It can be used like this:
--
-- > instance Bindable MyType where
-- >   binding = base_binding
base_binding :: a -> ([Atom], [Atom] -> a)
base_binding a = ([], \[] -> a)

-- Base cases

instance Bindable Atom where
  binding a = ([a], \[a] -> a)

instance Bindable Bool where
  binding = base_binding
  
instance Bindable Integer where
  binding = base_binding
  
instance Bindable Int where
  binding = base_binding
  
instance Bindable Char where
  binding = base_binding
  
instance Bindable Double where
  binding = base_binding
  
instance Bindable Float where
  binding = base_binding
  
instance Bindable Literal where
  binding = base_binding

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
  binding m = (xs, g)
    where
      (xs, f) = binding (Map.toList m)
      g xs = Map.fromList (f xs)

instance (Ord k, Bindable k) => Bindable (Set k) where
  binding s = (xs, g)
    where
      (xs, f) = binding (Set.toList s)
      g xs = Set.fromList (f xs)

-- ----------------------------------------------------------------------
-- * Generic programming for Bindable

-- | A version of the 'Bindable' class suitable for generic programming.
class (GNominal f) => GBindable f where
  gbinding :: f a -> ([Atom], [Atom] -> f a)

instance GBindable V1 where
  gbinding a = undefined -- never occurs, because V1 is empty

instance GBindable U1 where
  gbinding U1 = ([], \xs -> U1)

instance (GBindable a, GBindable b) => GBindable (a :*: b) where
  gbinding (a :*: b) = (xs ++ ys, h)
    where
      (xs, f) = gbinding a
      (ys, g) = gbinding b
      n = length xs
      h zs = f xs :*: g ys
        where
          (xs, ys) = splitAt n zs 

instance (GBindable a, GBindable b) => GBindable (a :+: b) where
  gbinding (L1 a) = (xs, g)
    where
      (xs, f) = gbinding a
      g xs = L1 (f xs)
  gbinding (R1 a) = (xs, g)
    where
      (xs, f) = gbinding a
      g xs = R1 (f xs)

instance (GBindable a) => GBindable (M1 i c a) where
  gbinding (M1 a) = (xs, g)
    where
      (xs, f) = gbinding a
      g xs = M1 (f xs)
  
instance (Bindable a) => GBindable (K1 i a) where
  gbinding (K1 a) = (xs, g)
    where
      (xs, f) = binding a
      g xs = K1 (f xs)
