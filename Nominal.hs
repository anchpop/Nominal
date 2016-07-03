-- | A package for working with binders.

-- Todo: implement a proper Show instance for nominal types (and
-- atoms). This should include some proper alpha-renaming. This
-- probably requires computing the free atoms of a term.

module Nominal (
  Atom,
  BindAtom,
  with_fresh,
  with_fresh_named,
  (.),
  open,
  open_for_printing,
  Nominal(..),
  NominalSupport(..),
)
where

import Prelude hiding ((.))
import Data.IORef
import System.IO.Unsafe
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Char

-- | An atom is an globally unique, opaque value with a suggested name.
data Atom = Atom Integer String
             deriving (Eq, Ord)

instance Show Atom where
  show (Atom x n) = n

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

-- | A type is 'Nominal' if the group of finitely supported permutations
-- of atoms acts on it. We can speak of the support of an element of
-- this type. We can also bind an atom in such a type.

-- Language note: in an ideal programming language, 'Nominal'
-- instances for new datatypes could be derived with 'deriving'.
class Nominal t where
  -- | 'swap' /a/ /b/ /t/: replace /a/ by /b/ and /b/ by /a/ in /t/.
  swap :: Atom -> Atom -> t -> t

-- | A type is 'NominalSupport' if we can moreover compute its support,
-- which is the finite set of atoms occurring freely in it. Most
-- 'Nominal' types are also 'NominalSupport', with the exception of
-- function types (for which we cannot compute the support).
class NominalSupport t where
  -- | Compute the set of free atoms.
  support :: t -> Set Atom

instance Nominal Atom where
  swap a b t = if t == a then b else if t == b then a else t

instance NominalSupport Atom where
  support x = Set.singleton x

instance Nominal Integer where
  swap a b t = t
instance NominalSupport Integer where
  support t = Set.empty

instance Nominal Int where
  swap a b t = t
instance NominalSupport Int where
  support t = Set.empty

instance Nominal Char where
  swap a b t = t
instance NominalSupport Char where
  support t = Set.empty

instance (Nominal t) => Nominal [t] where
  swap a b ts = map (swap a b) ts
instance (NominalSupport t) => NominalSupport [t] where
  support ts = Set.unions (map support ts)

instance Nominal () where
  swap a b t = t
instance NominalSupport () where
  support t = Set.empty

instance (Nominal t, Nominal s) => Nominal (t,s) where
  swap a b (t, s) = (swap a b t, swap a b s)
instance (NominalSupport t, NominalSupport s) => NominalSupport (t,s) where
  support (t, s) = support t `Set.union` support s

instance (Nominal t, Nominal s, Nominal r) => Nominal (t,s,r) where
  swap a b (t, s, r) = (swap a b t, swap a b s, swap a b r)
instance (NominalSupport t, NominalSupport s, NominalSupport r) => NominalSupport (t,s,r) where
  support (t, s, r) = support t `Set.union` support s `Set.union` support r

-- ... and so on for tuples.

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

-- | Pattern matching for atom abstraction. In an ideal programming
-- idiom, we would be able to define a function on atom abstractions
-- like this:
--
-- > f (x.s) = body.
--
-- Haskell doesn't provide this syntax, but the 'open' function
-- provides the equivalent syntax
--
-- > f t = open t (\x s -> body).
--
-- To be referentially transparent and equivariant, the body is
-- subject to the same restriction as 'with_fresh', namely,
-- /x/ must be fresh for the body (in symbols /x/ # /body/).
open :: BindAtom t -> (Atom -> t -> s) -> s
open (AtomAbstraction n f) body =
  with_fresh_named n (\a -> body a (f a))

-- | A variant of 'open' which moreover attempts to choose a name for
-- the bound name that does not clash with any free name in its
-- scope. This requires a 'NominalSupport' instance. It is mostly
-- useful for building custom pretty-printers for nominal
-- terms. Except in pretty-printers, 'open' is equivalent.
open_for_printing :: (NominalSupport t) => BindAtom t -> (Atom -> t -> s) -> s
open_for_printing t@(AtomAbstraction n f) body =
  with_fresh_named n1 (\a -> body a (f a))
  where
    sup = support t
    n1 = rename_fresh sup n
    
instance (Eq t) => Eq (BindAtom t) where
  AtomAbstraction n f == AtomAbstraction m g =
    with_fresh (\a -> f a == g a)

instance (Nominal t) => Nominal (BindAtom t) where
  -- Implementation note: here, we crucially use the assumption that
  -- in the HOAS encoding, f will only be applied to fresh names.
  swap a b (AtomAbstraction n f) = AtomAbstraction n (\x -> swap a b (f x))

instance (NominalSupport t) => NominalSupport (BindAtom t) where
  support (AtomAbstraction n f) =
    with_fresh (\a -> Set.delete a (support (f a)))

-- Convert a digit to a subscript.
to_subscript :: Char -> Char
to_subscript '0' = '₀'
to_subscript '1' = '₁'
to_subscript '2' = '₂'
to_subscript '3' = '₃'
to_subscript '4' = '₄'
to_subscript '5' = '₅'
to_subscript '6' = '₆'
to_subscript '7' = '₇'
to_subscript '8' = '₈'
to_subscript '9' = '₉'
to_subscript c = c

-- An infinite list of identifiers, based on the suggested name.
varnames :: String -> [String]
varnames x0 = x1 : x : [ x ++ map to_subscript (show n) | n <- [1..] ]
  where
    (x, x1) = case takeWhile isAlpha x0 of
         "" -> ("x", "x") -- Treat no_name as a special case.
         x -> (x, x0)

-- Compute a string that is not the name of any atom in the set, based
-- on the supplied suggestion.
rename_fresh :: Set Atom -> String -> String
rename_fresh atoms n = n'
  where
    n' = head [ x | x <- varnames n, not (used x) ]
    used x = x `Set.member` as
    as = Set.map atom_name atoms

instance (Show t, NominalSupport t) => Show (BindAtom t) where
  showsPrec d t = open_for_printing t $ \a s ->
    showParen (d > 5) $
      showString (show a ++ ".") `compose` showsPrec 5 s
    where
      compose f g x = f (g x) -- because hidden from Prelude
