-- | A package for working with binders.

-- Todo: implement a proper Show instance for nominal types (and
-- atoms). This should include some proper alpha-renaming. This
-- probably requires computing the free atoms of a term.

module Nominal (
  Atom,
  Atomic,
  Bind,
  with_fresh,
  with_fresh_named,
  with_fresh_namelist,
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

-- | An atom is an globally unique, opaque value with some optional
-- name suggestions.
data Atom = Atom Integer [String]
             deriving (Eq, Ord)

instance Show Atom where
  show (Atom x ns) = head (varnames ns)

-- | A type class for atom types. Users can generate additional types
-- of atoms by cloning 'Atom' and deriving 'Atomic', 'Nominal',
-- 'NominalSupport', 'Eq', and 'Show':
--
-- > newtype Variable = Variable Atom
-- >   deriving (Atomic, Nominal, NominalSupport, Eq, Show)
class (Nominal a, NominalSupport a, Eq a, Show a) => Atomic a where
  to_atom :: a -> Atom
  from_atom :: Atom -> a

instance Atomic Atom where
  to_atom = id
  from_atom = id

-- | A global counter for atoms. The use of 'unsafePerformIO' here is
-- safe, because 'Integer' is a monomorphic type.
global_atom_counter :: IORef Integer
global_atom_counter = unsafePerformIO (newIORef 0)

-- | Create a new atom with the given name suggestions.
new_atom_named :: [String] -> IO Atom
new_atom_named ns = do
  x <- readIORef global_atom_counter
  writeIORef global_atom_counter (x+1)
  return (Atom x ns)

-- | Return the suggested names of an atom.
atom_names :: Atom -> [String]
atom_names (Atom x ns) = ns

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
{-# NOINLINE with_fresh_namelist #-}
with_fresh_namelist :: (Atomic a) => [String] -> (a -> t) -> t
with_fresh_namelist ns body = unsafePerformIO $ do
  a <- new_atom_named ns
  return (body (from_atom a))
         
with_fresh_named :: (Atomic a) => String -> (a -> t) -> t
with_fresh_named n = with_fresh_namelist [n]

-- | A version of 'with_fresh_named' when we don't want to 
-- name the atom.
with_fresh :: (Atomic a) => (a -> t) -> t
with_fresh = with_fresh_namelist ["x", "y", "z", "u", "v", "w", "r", "s", "t", "p", "q"]

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

-- | Bind a t is the type of atom abstractions, denoted [a]t
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
data Bind a t = AtomAbstraction [String] (a -> t)

-- | Atom abstraction: /a/./t/ represents the equivalence class of pairs
-- (/a/,/t/) modulo alpha-equivalence. Here, (/a/,/t/) ~ (/b/,/s/) iff
-- for fresh /c/, 'swap' /a/ /c/ /t/ = 'swap' /b/ /c/ /s/.
(.) :: (Atomic a, Nominal t) => a -> t -> Bind a t
a.t = AtomAbstraction (atom_names (to_atom a)) (\x -> swap (to_atom a) (to_atom x) t)

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
open :: (Atomic a) => Bind a t -> (a -> t -> s) -> s
open (AtomAbstraction ns f) body =
  with_fresh_namelist ns (\a -> body a (f a))

-- | A variant of 'open' which moreover attempts to choose a name for
-- the bound name that does not clash with any free name in its
-- scope. This requires a 'NominalSupport' instance. It is mostly
-- useful for building custom pretty-printers for nominal
-- terms. Except in pretty-printers, 'open' is equivalent.
open_for_printing :: (Atomic a, NominalSupport t) => Bind a t -> (a -> t -> s) -> s
open_for_printing t@(AtomAbstraction ns f) body =
  with_fresh_named n1 (\a -> body a (f a))
  where
    sup = support t
    n1 = rename_fresh sup ns
    
instance (Atomic a, Eq t) => Eq (Bind a t) where
  AtomAbstraction n f == AtomAbstraction m g =
    with_fresh (\a -> f a == g a)

instance (Nominal t) => Nominal (Bind a t) where
  -- Implementation note: here, we crucially use the assumption that
  -- in the HOAS encoding, f will only be applied to fresh names.
  swap a b (AtomAbstraction n f) = AtomAbstraction n (\x -> swap a b (f x))

instance (Atomic a, NominalSupport t) => NominalSupport (Bind a t) where
  support (AtomAbstraction n f) =
    with_fresh (\a -> Set.delete (to_atom a) (support (f a)))

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

-- An infinite list of identifiers, based on the suggested names.
varnames :: [String] -> [String]
varnames xs0 = xs1 ++ xs3 ++ [ x ++ map to_subscript (show n) | n <- [1..], x <- xs3 ]
  where
    xs1 = [ x | x <- xs0, x /= "" ]
    xs2 = [ y | x <- xs0, let y = takeWhile isAlpha x, y /= "" ]
    xs3 = if xs2 == [] then ["x"] else xs2

-- Compute a string that is not the name of any atom in the set, based
-- on the supplied suggestions.
rename_fresh :: Set Atom -> [String] -> String
rename_fresh atoms ns = n'
  where
    n' = head [ x | x <- varnames ns, not (used x) ]
    used x = x `Set.member` as
    as = Set.map show atoms

instance (Atomic a, Show a, Show t, NominalSupport t) => Show (Bind a t) where
  showsPrec d t = open_for_printing t $ \a s ->
    showParen (d > 5) $
      showString (show a ++ ".") `compose` showsPrec 5 s
    where
      compose f g x = f (g x) -- because hidden from Prelude
