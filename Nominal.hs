-- | A package for working with binders.

-- Todo: implement a proper Show instance for nominal types (and
-- atoms). This should include some proper alpha-renaming. This
-- probably requires computing the free atoms of a term.

module Nominal (
  Atom,
  with_fresh,
  with_fresh_named,
  BindAtom,
  (.),
  open,
  Nominal(..),
)
where

import Data.IORef
import System.IO.Unsafe
import Prelude hiding ((.))

-- | An atom is an globally unique, opaque value with a suggested name.
data Atom = Atom Integer String
             deriving (Eq)

instance Show Atom where
  show (Atom x n) = n ++ show x

-- | A global counter for atoms. The use of 'unsafePerformIO' here is
-- safe, because 'Integer' is a monomorphic type.
global_atom_counter :: IORef Integer
global_atom_counter = unsafePerformIO (newIORef 0)

-- | Create a new atom with the given suggested name.
new_atom_named :: String -> IO Atom
new_atom_named n = do
  x <- readIORef global_atom_counter
  writeIORef global_atom_counter (x+1)
  return (Atom x n)

-- | Return the suggested name of an atom.
atom_name :: Atom -> String
atom_name (Atom x n) = n

-- | Perform a computation in the presence of a fresh atom. The use of
-- 'unsafePerformIO' here is not technically safe, because
-- 'with_fresh' is not really referentially transparent. It is,
-- however, referentially transparent and equivariant provided that
-- its use is governed by a syntactic restriction, namely, that the
-- atom created does not escape the body of the 'with_fresh'
-- block. Formally, 'with_fresh' should only be used in the context
--
-- > with_fresh (\a -> body),
--
-- where /a/ # /body/. (Note that this is not the same as saying that
-- /a/ does not occur freely in the body. It may occur freely, but
-- must be fresh. For example, /a/ occurs freely in /a/./a/, but it
-- still fresh for it).
-- 
-- For example, this is /not/ permitted:
--
-- > with_fresh (\a -> a)
--
-- The following uses are permitted:
--
-- > with_fresh (\a -> f a == g a)
--
-- > with_fresh (\a -> a . f a b c)
{-# NOINLINE with_fresh_named #-}
with_fresh_named :: String -> (Atom -> t) -> t
with_fresh_named n body = unsafePerformIO $ do
  a <- new_atom_named n
  return (body a)

-- | A version of 'with_fresh_named' when we don't want to 
-- name the atom.
with_fresh :: (Atom -> t) -> t
with_fresh = with_fresh_named "x"

-- | A type is Nominal if the group of finitely supported permutations
-- of atoms acts on it. We can speak of the support of an element of
-- this type. We can also bind an atom in such a type.

-- Language note: in an ideal programming language, 'Nominal'
-- instances for new datatypes could be derived with 'deriving'.
class Nominal t where
  -- | 'swap' /a/ /b/ /t/: replace /a/ by /b/ and /b/ by /a/ in /t/.
  swap :: Atom -> Atom -> t -> t
  
instance Nominal Atom where
  swap a b t = if t == a then b else if t == b then a else t

instance Nominal Integer where
  swap a b t = t

instance Nominal Int where
  swap a b t = t

instance Nominal Char where
  swap a b t = t

instance (Nominal t) => Nominal [t] where
  swap a b ts = map (swap a b) ts

instance Nominal () where
  swap a b t = t

instance (Nominal t, Nominal s) => Nominal (t,s) where
  swap a b (t, s) = (swap a b t, swap a b s)

instance (Nominal t, Nominal s, Nominal r) => Nominal (t,s,r) where
  swap a b (t, s, r) = (swap a b t, swap a b s, swap a b r)

instance (Nominal t, Nominal s) => Nominal (t -> s) where
  swap a b f = \x -> swap a b (f (swap a b x))

-- | BindAtom t is the type of atom abstractions, denoted [Atom]t
-- in nominal logic. Its elements are of the form a.v modulo
-- alpha-equivalence. For more details on what this means, see
-- Definition 4 of [Pitts 2002].

-- Implementation note: we currently use an HOAS encoding. It remains
-- to see whether this is efficient. An important invariant of the
-- HOAS encoding is that the underlying function must only be applied
-- to /fresh/ atoms.
-- 
-- It would also be possible to use a DeBruijn encoding or a nameful
-- encoding. Maybe we'll eventually provide all three, or a
-- combination.
data BindAtom t = AtomAbstraction String (Atom -> t)

-- | Atom abstraction: /a/./t/ represents the equivalence class of pairs
-- (/a/,/t/) modulo alpha-equivalence. Here, (/a/,/t/) ~ (/b/,/s/) iff
-- for fresh /c/, 'swap' /a/ /c/ /t/ = 'swap' /b/ /c/ /s/.
(.) :: (Nominal t) => Atom -> t -> BindAtom t
a.t = AtomAbstraction (atom_name a) (\x -> swap a x t)

infixr 5 .

-- | Unpack an atom abstraction. To be equivariant and referentially
-- transparent, this is subject to the same restriction as
-- 'with_fresh', i.e., in
--
-- > open t (\a s -> body),
--
-- we must have /a/ # /body/.

-- Language note: open t (\x s -> body) serves as a kind of
-- \"let\"-binding for abstractions. In an ideal programming language,
-- it would be possible to pattern-match on an element of 'BindAtom'
-- /t/, i.e., we could write
--
-- > f (x.s) = body
--
-- instead of
--
-- > f t = open t (\x s -> body).
open :: BindAtom t -> (Atom -> t -> s) -> s
open (AtomAbstraction n f) body =
  with_fresh_named n (\a -> body a (f a))

instance (Eq t) => Eq (BindAtom t) where
  AtomAbstraction n f == AtomAbstraction m g =
    with_fresh (\a -> f a == g a)

instance (Nominal t) => Nominal (BindAtom t) where
  -- Implementation note: here, we crucially use the assumption that
  -- in the HOAS encoding, f will only be applied to fresh names.
  swap a b (AtomAbstraction n f) = AtomAbstraction n (\x -> swap a b (f x))

instance (Show t) => Show (BindAtom t) where
  showsPrec d (AtomAbstraction n f) = showParen (d > 5) $
    with_fresh_named n $ \a ->
      showString (show a ++ ".") `compose` showsPrec 5 (f a)
    where
      compose f g x = f (g x) -- because hidden from Prelude
