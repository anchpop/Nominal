{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}

-- | This module provides a type class 'Bindable'. It contains things
-- (such as atoms, tuples of atoms, etc.) that can be abstracted by
-- binders.  Moreover, for each bindable type /a/ and nominal type
-- /t/, it defines a type 'Bind' /a/ /t/ of abstractions.
--
-- We also provide some generic programming so that instances of
-- 'Bindable' can be automatically derived in most cases.
module Nominal.Bindable where

import Prelude hiding ((.))
import GHC.Generics

import Nominal.ConcreteNames
import Nominal.Atom
import Nominal.Permutation
import Nominal.Nominal
import Nominal.NominalSupport

-- ----------------------------------------------------------------------
-- * The Bindable class

-- | 'Bind' /a/ /t/ is the type of atom abstractions, denoted [/a/]/t/
-- in the nominal logic literature. Its elements are pairs (/a/,/t/)
-- modulo alpha-equivalence. We also write /a/'.'/t/ for such an
-- equivalence class of pairs. For more details on what this means,
-- see Definition 4 of [Pitts 2002].

-- Implementation note: the two alternatives of this datatype are not
-- really alternatives in the usual sense. Generic instances of
-- Bindable /a/ must /always/ use the alternative 'GBind', and
-- user-defined instances must /always/ use the alternative 'CBind'.
-- This unorthodox 2-track encoding is needed because the generic
-- deriving mechanism does not provide a way to generically derive
-- associated types of classes.
data Bind a t =
  CBind (CBind a t)          -- ^ This alternative is only used by
                             -- custom instances.
  | GBind (GBind (Rep a) t)  -- ^ This alternative is only used by
                             -- generic instances.

-- | A type is 'Bindable' if its elements can be abstracted by
-- binders. Examples include atoms, tuples of atoms, list of atoms,
-- etc.
class (Eq a, Nominal a, NominalSupport a) => Bindable a where
  -- | An optional custom implementation of the 'Bind' /a/ /t/
  -- datatype. This type must be defined by all custom 'Bindable'
  -- instances, but is not used by generic instances.
  type CBind a t
  
  -- | This is the @(•)@ function of 'Nominal'. We need to define it
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
  -- We use the infix operator @(@'.'@)@, which is normally bound to
  -- function composition in the standard library. Thus, nominal
  -- programs should import the standard library like this:
  --
  -- > import Prelude hiding ((.))
  bindable_abst :: (Nominal t) => a -> t -> Bind a t
  
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
  bindable_open :: (Nominal t) => Bind a t -> (a -> t -> s) -> s

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
  bindable_open_for_printing :: (Nominal t) => Support -> Bind a t -> (a -> t -> Support -> s) -> s

  -- Generic implementations
  type instance CBind a t = ()

  default bindable_action :: (Generic a, GBindable (Rep a), Nominal t) => Permutation -> Bind a t -> Bind a t
  bindable_action π (GBind b) = GBind (gbindable_action π b)
  
  default bindable_support :: (Generic a, GBindable (Rep a), NominalSupport t) => Bind a t -> Support
  bindable_support (GBind b) = gbindable_support b

  default bindable_eq :: (Generic a, GBindable (Rep a), Nominal t, Eq t) => Bind a t -> Bind a t -> Bool
  bindable_eq (GBind b1) (GBind b2) = gbindable_eq b1 b2

  default bindable_abst :: (Generic a, GBindable (Rep a), Nominal t) => a -> t -> Bind a t
  bindable_abst a t = GBind (gbindable_abst (from a) t)

  default bindable_open :: (Generic a, GBindable (Rep a), Nominal t) => Bind a t -> (a -> t -> s) -> s
  bindable_open (GBind b) body = gbindable_open b (\a t -> body (to a) t)

  default bindable_open_for_printing :: (Generic a, GBindable (Rep a), Nominal t) => Support -> Bind a t -> (a -> t -> Support -> s) -> s
  bindable_open_for_printing sup (GBind b) body = gbindable_open_for_printing sup b (\a t sup' -> body (to a) t sup')

instance (Bindable a, Nominal t) => Nominal (Bind a t) where
  π • body = bindable_action π body

instance (Bindable a, NominalSupport t) => NominalSupport (Bind a t) where
  support = bindable_support

-- | Atom abstraction: /a/'.'/t/ represents the equivalence class of
-- pairs (/a/,/t/) modulo alpha-equivalence. 
--
-- We use the infix operator @(@'.'@)@, which is normally bound to
-- function composition in the standard Haskell library. Thus, nominal
-- programs should import the standard library like this:
-- 
-- > import Prelude hiding ((.))
(.) :: (Bindable a, Nominal t) => a -> t -> Bind a t
(.) = bindable_abst
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
open = bindable_open
  
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
open_for_printing = bindable_open_for_printing

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

instance (Bindable a, Nominal t, Eq t) => Eq (Bind a t) where
  (==) = bindable_eq

-- ----------------------------------------------------------------------
-- Bindable instances

instance Bindable Atom where
  type CBind Atom t = BindAtom t
  bindable_action π (CBind body) = CBind (π • body)
  bindable_support (CBind body) = support body
  bindable_eq (CBind b1) (CBind b2) = b1 == b2
  bindable_abst a t = CBind (atom_abst a t)
  bindable_open (CBind body) k = atom_open body k
  bindable_open_for_printing sup (CBind body) k = atom_open_for_printing sup body k

instance (Bindable a) => Bindable [a]
instance Bindable ()
instance (Bindable a, Bindable b) => Bindable (a, b)
instance (Bindable a, Bindable b, Bindable c) => Bindable (a, b, c)
instance (Bindable a, Bindable b, Bindable c, Bindable d) => Bindable (a, b, c, d)
instance (Bindable a, Bindable b, Bindable c, Bindable d, Bindable e) => Bindable (a, b, c, d, e)
instance (Bindable a, Bindable b, Bindable c, Bindable d, Bindable e, Bindable f) => Bindable (a, b, c, d, e, f)
instance (Bindable a, Bindable b, Bindable c, Bindable d, Bindable e, Bindable f, Bindable g) => Bindable (a, b, c, d, e, f, g)
  
-- ----------------------------------------------------------------------
-- * Generic Bindable instances

-- | A version of the 'Bindable' class suitable for generic programming.
class (GNominal f) => GBindable f where
  data GBind f t
  gbindable_action :: (Nominal t) => Permutation -> GBind f t -> GBind f t
  gbindable_support :: (NominalSupport t) => GBind f t -> Support
  gbindable_eq :: (Nominal t, Eq t) => GBind f t -> GBind f t -> Bool
  gbindable_abst :: (Nominal t) => f a -> t -> GBind f t
  gbindable_open :: (Nominal t) => GBind f t -> (f a -> t -> s) -> s
  gbindable_open_for_printing :: (Nominal t) => Support -> GBind f t -> (f a -> t -> Support -> s) -> s

instance (GBindable a, Nominal t) => Nominal (GBind a t) where
  π • body = gbindable_action π body

instance (GBindable a, NominalSupport t) => NominalSupport (GBind a t) where
  support = gbindable_support

instance (GBindable a, Nominal t, Eq t) => Eq (GBind a t) where
  (==) = gbindable_eq

instance GBindable V1 where
  data GBind V1 t -- empty type
  gbindable_action π x = undefined -- Never occurs, because V1 is empty
  gbindable_support x = undefined
  gbindable_eq x y = undefined
  gbindable_abst a t = undefined
  gbindable_open x body = undefined
  gbindable_open_for_printing sup x body = undefined

instance GBindable U1 where
  newtype GBind U1 t = GBindU1 t
  gbindable_action π (GBindU1 t) = GBindU1 (π • t)
  gbindable_support (GBindU1 t) = support t
  gbindable_eq (GBindU1 t) (GBindU1 s) = t == s
  gbindable_abst U1 t = GBindU1 t
  gbindable_open (GBindU1 t) body = body U1 t
  gbindable_open_for_printing sup (GBindU1 t) body = body U1 t sup

instance (GBindable a, GBindable b) => GBindable (a :*: b) where
  newtype GBind (a :*: b) t = GBindPair (GBind a (GBind b t))
  gbindable_action π (GBindPair body) = GBindPair (π • body)
  gbindable_support (GBindPair body) = support body
  gbindable_eq (GBindPair b1) (GBindPair b2) = b1 == b2
  gbindable_abst (a :*: b) t = GBindPair (gbindable_abst a (gbindable_abst b t))
  gbindable_open (GBindPair body) k =
    gbindable_open body $ \a body2 -> gbindable_open body2 $ \b t -> k (a :*: b) t
  gbindable_open_for_printing sup (GBindPair body) k =
    gbindable_open_for_printing sup body $ \a body2 sup2 ->
      gbindable_open_for_printing sup2 body2 $ \b t sup3 ->
        k (a :*: b) t sup3   

instance (GBindable a, GBindable b) => GBindable (a :+: b) where
  data GBind (a :+: b) t = GBindL1 (GBind a t) | GBindR1 (GBind b t)
  gbindable_action π (GBindL1 body) = GBindL1 (π • body)
  gbindable_action π (GBindR1 body) = GBindR1 (π • body)
  gbindable_support (GBindL1 body) = support body
  gbindable_support (GBindR1 body) = support body
  gbindable_eq (GBindL1 b1) (GBindL1 b2) = b1 == b2
  gbindable_eq (GBindR1 b1) (GBindR1 b2) = b1 == b2
  gbindable_eq _ _ = False
  gbindable_abst (L1 a) t = GBindL1 (gbindable_abst a t)
  gbindable_abst (R1 a) t = GBindR1 (gbindable_abst a t)
  gbindable_open (GBindL1 body) k = gbindable_open body $ \a t -> k (L1 a) t
  gbindable_open (GBindR1 body) k = gbindable_open body $ \a t -> k (R1 a) t
  gbindable_open_for_printing sup (GBindL1 body) k = gbindable_open_for_printing sup body $ \a t sup2 -> k (L1 a) t sup2
  gbindable_open_for_printing sup (GBindR1 body) k = gbindable_open_for_printing sup body $ \a t sup2 -> k (R1 a) t sup2

instance (GBindable a) => GBindable (M1 i c a) where
  data GBind (M1 i c a) t = GBindM1 (GBind a t)
  gbindable_action π (GBindM1 body) = GBindM1 (π • body)
  gbindable_support (GBindM1 body) = support body
  gbindable_eq (GBindM1 b1) (GBindM1 b2) = b1 == b2
  gbindable_abst (M1 a) t = GBindM1 (gbindable_abst a t)
  gbindable_open (GBindM1 body) k = gbindable_open body $ \a t -> k (M1 a) t
  gbindable_open_for_printing sup (GBindM1 body) k = gbindable_open_for_printing sup body $ \a t sup2 -> k (M1 a) t sup2

instance (Bindable a) => GBindable (K1 i a) where
  data GBind (K1 i a) t = GBindK1 (Bind a t)
  gbindable_action π (GBindK1 body) = GBindK1 (π • body)
  gbindable_support (GBindK1 body) = support body
  gbindable_eq (GBindK1 b1) (GBindK1 b2) = b1 == b2
  gbindable_abst (K1 a) t = GBindK1 (a . t)
  gbindable_open (GBindK1 body) k = open body $ \a t -> k (K1 a) t
  gbindable_open_for_printing sup (GBindK1 body) k = open_for_printing sup body $ \a t sup2 -> k (K1 a) t sup2

