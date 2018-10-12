{-# LANGUAGE TypeFamilies #-}

-- | This module provides a type class 'Bindable' of things (such as
-- atoms, tuples of atoms, etc.) that can be abstracted by binders.
-- Moreover, for each bindable type /a/ and nominal type /t/, it
-- defines a type 'Bind' /a/ /t/ of abstractions. 

module Nominal.Bindable where

import Prelude hiding ((.))

import Nominal.ConcreteNames
import Nominal.Atom
import Nominal.Permutation
import Nominal.Nominal
import Nominal.NominalSupport

-- ----------------------------------------------------------------------
-- * The Bindable class

-- | The 'Bindable' class contains types of things (such as atoms,
-- tuples of atoms, etc.) that can be abstracted by binders.

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

instance (Bindable a, NominalSupport t) => NominalSupport (Bind a t) where
  support = bindable_support

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

-- | Since we hide (.) from the standard library, and it is not legal
-- syntax to write \"̈@Prelude..@\", we provide '∘' as an alternate
-- notation for composition.
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

instance (Bindable a, Eq a, Nominal t, Eq t) => Eq (Bind a t) where
  (==) = bindable_eq

-- ----------------------------------------------------------------------
-- Bindable instances

instance Bindable Atom where
  newtype Bind Atom t = BindA (BindAtom t)
  bindable_action π (BindA body) = BindA (π • body)
  bindable_support (BindA body) = support body
  bindable_eq (BindA b1) (BindA b2) = b1 == b2
  abst a t = BindA (atom_abst a t)
  open (BindA body) k = atom_open body k
  open_for_printing sup (BindA body) k = atom_open_for_printing default_names sup body k

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
  

