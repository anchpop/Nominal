{-# LANGUAGE GeneralizedNewtypeDeriving #-}

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
  bind,
  open,
  open_for_printing,
  merge,
  Nominal(..),
  NominalShow(..),
  Support,
  Literal(..),
  AtomKind(..),
  AtomOfKind,
)
where

import Prelude hiding ((.))
import Data.IORef
import System.IO.Unsafe
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Char
import Data.List
import Data.Unique

-- ----------------------------------------------------------------------
-- * Concrete names

-- | A name suggestion. Since bound atoms sometimes have to be
-- renamed, we need a way to generate suitable concrete names.  This
-- should be configurable on a per-atom basis, with a fallback default
-- behavior for each atom type.
--
-- A name suggestion is essentially a list of possible names. The
-- first useable name from the list is chosen. If the list is finite
-- and contains no useable names, then "Nominal" will apply its
-- default behavior, which is to generate more names by appending
-- numerical subscripts. A client can override this default behavior
-- by specifying an infinite list of name suggestions.
--
-- An empty list of name suggestions counts as no suggestion, in which
-- case an atom-type specific default will be used.
--
-- When merging two atoms (see 'merge'), we concatenate their name
-- suggestions. In particular, if one name has a user-specified
-- suggestion and the other one does not, we always use the
-- user-specified one.
type NameSuggestion = [String]

-- | The names to use if nothing else was specified.
default_names :: NameSuggestion
default_names = ["x", "y", "z", "u", "v", "w", "r", "s", "t", "p", "q"]

-- | Convert a digit to a subscript.
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

-- | An infinite list of strings, based on the suggested names.
varnames :: NameSuggestion -> [String]
varnames xs0 = xs1 ++ xs3 ++ [ x ++ map to_subscript (show n) | n <- [1..], x <- xs3 ]
  where
    xs1 = [ x | x <- xs0, x /= "" ]
    xs2 = [ y | x <- xs0, let y = takeWhile isAlpha x, y /= "" ]
    xs3 = if xs2 == [] then default_names else xs2

-- | Compute a string that is not in the given set, and whose name is
-- based on the supplied suggestions.
rename_fresh :: Set String -> NameSuggestion -> String
rename_fresh as ns = n'
  where
    n' = head [ x | x <- varnames ns, not (used x) ]
    used x = x `Set.member` as

-- | Merge two name suggestions. Essentially this appends them, but we
-- try to avoid duplication.
combine_names :: NameSuggestion -> NameSuggestion -> NameSuggestion
combine_names xs ys = xs ++ (ys \\ xs)

-- ----------------------------------------------------------------------
-- * Atoms

-- | An atom is an globally unique, opaque value with some optional
-- name suggestions.
data Atom = Atom Unique NameSuggestion
             deriving (Eq, Ord)

-- | Create a new atom with the given name suggestions.
new_atom_namelist :: NameSuggestion -> IO Atom
new_atom_namelist ns = do
  x <- newUnique
  return (Atom x ns)

-- | Return the suggested names of an atom.
atom_names :: Atom -> NameSuggestion
atom_names (Atom x ns) = ns

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
-- 'Nominal', 'NominalShow', 'Eq', and 'Ord', and defining a 'Show'
-- instance:
--
-- > {-# LANGUAGE GeneralizedNewtypeDeriving #-}
-- >
-- > newtype Variable = Variable Atom
-- >   deriving (Atomic, Nominal, NominalShow, Eq, Ord)
-- > 
-- > instance Show Variable where
-- >   show (Variable x) = show x
class (Nominal a, NominalShow a, Eq a, Ord a, Show a) => Atomic a where
  to_atom :: a -> Atom
  from_atom :: Atom -> a
  -- | The default variable names for the atom type.
  names :: a -> NameSuggestion

show_atom :: (Atomic a) => a -> String
show_atom a = head (varnames ns)
  where
    ns2 = case ns of [] -> names a; oetherwise -> ns
    Atom x ns = to_atom a

instance Atomic Atom where
  to_atom = id
  from_atom = id
  names a = default_names

instance Show Atom where
  show = show_atom

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
with_fresh f = with_fresh_namelist [] f

-- | A version of 'with_fresh' that permits a suggested name to be
-- given to the atom. The name is only a suggestion, and will be
-- changed, if necessary, to avoid clashes.
with_fresh_named :: (Atomic a) => String -> (a -> t) -> t
with_fresh_named n = with_fresh_namelist [n]

-- | A version of 'with_fresh' that permits a list of suggested names
-- to be specified. The first suitable name in the list will be used
-- if possible.
{-# NOINLINE with_fresh_namelist #-}
with_fresh_namelist :: (Atomic a) => NameSuggestion -> (a -> t) -> t
with_fresh_namelist ns body = unsafePerformIO $ do
  a <- new_atom_namelist ns
  return (body (from_atom a))

-- ----------------------------------------------------------------------
-- * Atom abstraction

-- | A type is 'Nominal' if the group of finitely supported permutations
-- of atoms acts on it. We can abstract over an atom in such a type.

-- Language note: in an ideal programming language, 'Nominal'
-- instances for new datatypes could be derived with 'deriving'.
class Nominal t where
  -- | 'swap' /a/ /b/ /t/: replace /a/ by /b/ and /b/ by /a/ in /t/.
  swap :: (Atom, Atom) -> t -> t

instance Nominal Atom where
  swap (a,b) t = if t == a then b else if t == b then a else t

instance Nominal Integer where
  swap π t = t

instance Nominal Int where
  swap π t = t

instance Nominal Char where
  swap π t = t

instance (Nominal t) => Nominal [t] where
  swap π ts = map (swap π) ts

instance Nominal () where
  swap π t = t

instance (Nominal t, Nominal s) => Nominal (t,s) where
  swap π (t, s) = (swap π t, swap π s)

instance (Nominal t, Nominal s, Nominal r) => Nominal (t,s,r) where
  swap π (t, s, r) = (swap π t, swap π s, swap π r)

instance (Nominal t, Nominal s) => Nominal (t -> s) where
  swap π f = \x -> swap π (f (swap π x))

-- | Bind a t is the type of atom abstractions, denoted [a]t
-- in the nominal logic literature. Its elements are of the form (a.v)
-- modulo alpha-equivalence. For more details on what this means, see
-- Definition 4 of [Pitts 2002].

-- Implementation note: we currently use an HOAS encoding. It remains
-- to see whether this is efficient. An important invariant of the
-- HOAS encoding is that the underlying function must only be applied
-- to /fresh/ atoms.
-- 
-- It would also be possible to use a DeBruijn encoding or a nameful
-- encoding. It remains to be seen which encoding is the most
-- efficient in practice.
data Bind a t = AtomAbstraction NameSuggestion (a -> t)

-- | Atom abstraction: (/a/./t/) represents the equivalence class of pairs
-- (/a/,/t/) modulo alpha-equivalence. Here, (/a/,/t/) ~ (/b/,/s/) iff
-- for fresh /c/, 'swap' /a/ /c/ /t/ = 'swap' /b/ /c/ /s/. 
--
-- We use the infix operator '.', which is normally bound to function
-- composition in the standard library. Thus, nominal programs should
-- import the standard library like this:
--
-- > import Prelude hiding ((.))
(.) :: (Atomic a, Nominal t) => a -> t -> Bind a t
a.t = AtomAbstraction (atom_names (to_atom a)) (\x -> swap (to_atom a, to_atom x) t)

infixr 5 .

-- | 'abst' /x/ /t/ is an alternative prefix notation for (/x/./t/).
abst :: (Atomic a, Nominal t) => a -> t -> Bind a t
abst = (.)

-- | A convenience function for constructing binders. 
--
-- > bind (\x -> t)
--
-- is a convenient way to write the atom abstraction (x.t),
-- where /x/ is a fresh variable.
bind :: (Atomic a, Nominal t) => (a -> t) -> Bind a t
bind f = with_fresh (\x -> x . f x)

-- | Pattern matching for atom abstraction. In an ideal programming
-- idiom, we would be able to define a function on atom abstractions
-- like this:
--
-- > f (x.s) = body.
--
-- Haskell doesn't let us provide this syntax, but the 'open' function
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

instance (Atomic a, Eq t) => Eq (Bind a t) where
  AtomAbstraction n f == AtomAbstraction m g =
    with_fresh (\a -> f a == g a)

instance (Nominal t) => Nominal (Bind a t) where
  -- Implementation note: here, we crucially use the assumption that
  -- in the HOAS encoding, f will only be applied to fresh names.
  swap π (AtomAbstraction n f) = AtomAbstraction n (\x -> swap π (f x))

-- | Sometimes, it is necessary to open two abstractions, using the
-- /same/ fresh name for both of them. An example of this is the
-- typing rule for lambda abstraction in dependent type theory:
--
-- >           Gamma, x:t  |-  e : s
-- >      ------------------------------------
-- >        Gamma |-  Lam (x.e) : Pi t (x.s)
--
-- In the bottom-up reading of this rule, we are given the terms
-- @Lam@ /body/ and @Pi@ /t/ /body'/, and we require a fresh name /x/
-- and terms /e/, /s/ such that /body/ = (/x/./e/) and /body'/ = (/x/./s/).
-- Crucially, the same atom /x/ should be used in both /e/ and /s/,
-- because we subsequently need to check that /e/ has type /s/ in some
-- scope that is common to /e/ and /s/.
--
-- The 'merge' primitive permits us to deal with such situations.
-- Its defining property is
--
-- > merge (x.e) (x.s) = (x.(e,s)).
--
-- We can therefore solve the above problem:
--
-- > open (merge body body') (\x (e,s) -> .....)
--
-- Moreover, the 'merge' primitive can be used to define other
-- merge-like functionality. For example, it is easy to define a function
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
merge (AtomAbstraction ns f) (AtomAbstraction ns' g) = (AtomAbstraction ns'' h) where
  ns'' = combine_names ns ns'
  h x = (f x, g x)

-- ----------------------------------------------------------------------
-- * Display of nominal values

-- | Something to be avoided can be an atom or a string.
data Avoidee = A Atom | S String
             deriving (Eq, Ord)

-- | This type provides an internal representation for the support of
-- a nominal term, i.e., the set of atoms occurring in it. This is an
-- opaque type with no exposed structure. The only way to construct a
-- value of type 'Support' is to use the function 'support'.
newtype Support = Support (Set Avoidee)

support_empty :: Support
support_empty = Support Set.empty

support_unions :: [Support] -> Support
support_unions xs = Support (Set.unions [ x | Support x <- xs ])

support_union :: Support -> Support -> Support
support_union (Support x) (Support y) = Support (Set.union x y)

support_atom :: Atom -> Support
support_atom a = Support (Set.singleton (A a))

support_delete :: Atom -> Support -> Support
support_delete a (Support s) = Support (Set.delete (A a) s)

support_string :: String -> Support
support_string s = Support (Set.singleton (S s))

newtype Literal = Literal String

instance Nominal Literal where
  swap π t = t

instance NominalShow Literal where
  support (Literal s) = support_string s

strings_of_support :: Support -> Set String
strings_of_support (Support s) = Set.map name s where
  name (A a) = show a
  name (S s) = s
                 
-- | 'NominalShow' is a helper class to support pretty-printing of
-- nominal values. Most 'Nominal' types are also 'NominalShow', with
-- the exception of function types (for which we cannot compute the
-- support).

class NominalShow t where
  -- | Compute a set of atoms and strings that should not be usd as
  -- the names of bound variables. Usually this is defined by
  -- straightforward recursive clauses. The recursive clauses must
  -- apply 'support' to a tuple or list of immediate subterms.
  --
  -- > instance NominalShow Term where
  -- >   support (Var x) = support x
  -- >   support (App t s) = support (t, s)
  -- >   support (Abs t) = support t
  -- >   support (MultiApp t args) = support (t, [args])
  -- >   support Unit = support ()
  --
  -- If your nominal type uses additional constants, identifiers, or
  -- reserved keywords that are not implemented as 'Atom's, but whose
  -- names you wouldn't like to clash with the names of bound
  -- variables, declare them with 'Literal' applied to a string:
  --
  -- >   support (Const str) = support (Literal str)
  support :: t -> Support

-- Primitive cases.
instance NominalShow Atom where
  support a = support_atom a

instance (NominalShow t) => NominalShow [t] where
  support ts = support_unions (map support ts)

instance (NominalShow t, NominalShow s) => NominalShow (t,s) where
  support (t, s) = support_union (support t) (support s)

instance NominalShow () where
  support t = support_empty

-- Derived cases.
instance NominalShow Integer where
  support t = support ()

instance NominalShow Int where
  support t = support ()

instance NominalShow Char where
  support t = support ()

instance (NominalShow t, NominalShow s, NominalShow r) => NominalShow (t,s,r) where
  support (t, s, r) = support (t, (s, r))

-- ... and so on for tuples.

-- | A variant of 'open' which moreover attempts to choose a name for
-- the bound name that does not clash with any free name in its
-- scope. This requires a 'NominalShow' instance. It is mostly
-- useful for building custom pretty-printers for nominal
-- terms. Except in pretty-printers, 'open' is equivalent.
open_for_printing :: (Atomic a, NominalShow t) => Bind a t -> (a -> t -> s) -> s
open_for_printing t@(AtomAbstraction ns f) body =
  with_fresh_named n1 (\a -> body a (f a))
  where
    sup = support t
    n1 = rename_fresh (strings_of_support sup) ns
    name (A a) = show a
    name (S s) = s
    
instance (Atomic a, NominalShow t) => NominalShow (Bind a t) where
  support (AtomAbstraction n f) =
    with_fresh (\a -> support_delete (to_atom a) (support (f a)))

instance (Atomic a, Show a, Show t, NominalShow t) => Show (Bind a t) where
  showsPrec d t = open_for_printing t $ \a s ->
    showParen (d > 5) $
      showString (show a ++ ".") `compose` showsPrec 5 s
    where
      compose f g x = f (g x) -- because hidden from Prelude

-- ----------------------------------------------------------------------
-- * Multiple atom types

-- | The type class 'AtomKind' requires a single method, which is
-- moreover optional: a list of suggested names for this kind of atom.
-- For example:
--
-- > data VarName
-- > instance AtomKind VarName where suggested_names = ["x", "y", "z"]
--
-- > data TypeName
-- > instance AtomKind TypeName where suggested_names = ["a", "b", "c"]
--
-- It is possible to have infinitely many kinds of atoms, for example:
--
-- > data Zero
-- > data Succ a
-- > instance AtomKind Zero
-- > instance AtomKind (Succ a)
--
-- Then Zero, Succ Zero, Succ (Succ Zero), etc., will all be atom kinds.
class AtomKind a where
  suggested_names :: a -> NameSuggestion
  suggested_names a = names a'
    where
      a' :: Atom
      a' = undefined

-- | The type of atoms of a given kind. For example:
--
-- > type Variable = AtomOfKind VarName
-- > type Type = AtomOfKind TypeName
newtype AtomOfKind a = AtomOfKind Atom
  deriving (Nominal, NominalShow, Eq, Ord)

instance Show (AtomOfKind a) where
  show (AtomOfKind a) = show a

instance (AtomKind a) => Atomic (AtomOfKind a) where
  to_atom (AtomOfKind a) = a
  from_atom a = AtomOfKind a
  names f = suggested_names (un f)
    where
      un :: AtomOfKind a -> a
      un f = undefined
