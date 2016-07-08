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
  Permutation,
  NominalShow(..),
  Support,
  Literal(..),
  AtomKind(..),
  AtomOfKind,
  cp,
)
where

import Prelude hiding ((.))
import Data.IORef
import System.IO.Unsafe
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
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

-- | Create a fresh atom with the given name suggestions.
fresh_atom_namelist :: NameSuggestion -> IO Atom
fresh_atom_namelist ns = do
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
-- >   showsPrec = nominal_showsPrec
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
  a <- fresh_atom_namelist ns
  return (body (from_atom a))

-- ----------------------------------------------------------------------
-- * Atom abstraction

-- | A type is 'Nominal' if the group of finitely supported permutations
-- of atoms acts on it. We can abstract over an atom in such a type.

-- Language note: in an ideal programming language, 'Nominal'
-- instances for new datatypes could be derived with 'deriving'.
class Nominal t where
  -- | Apply a permutation of atoms to a term.
  (•) :: Permutation -> t -> t
  
instance Nominal Atom where
  (•) = perm_apply_atom

instance Nominal Integer where
  π • t = t

instance Nominal Int where
  π • t = t

instance Nominal Char where
  π • t = t

instance (Nominal t) => Nominal [t] where
  π • t = map (π •) t

instance Nominal () where
  π • t = t

instance (Nominal t, Nominal s) => Nominal (t,s) where
  π • (t, s) = (π • t, π • s)

instance (Nominal t, Nominal s, Nominal r) => Nominal (t,s,r) where
  π • (t, s, r) = (π • t, π • s, π • r)

instance (Nominal t, Nominal s) => Nominal (t -> s) where
  π • f = \x -> π • (f (π' • x))
    where
      π' = perm_invert π

-- ----------------------------------------------------------------------
-- * The monoid of permutations

-- | The monoid of finitely supported permutations on atoms. This is
-- carefully engineered for efficiency.
newtype Perm = Perm (Map Atom Atom)
             deriving (Eq, Show)

-- | The identity permutation. O(1).
p_identity :: Perm
p_identity = Perm Map.empty

-- | Compose two permutations. O(/m/) where /m/ is the size of the right permutation.
p_composeR :: Perm -> Perm -> Perm
p_composeR s@(Perm sigma) (Perm tau) = Perm rho
  where
    rho = Map.foldrWithKey f sigma tau
    f a b rho = rho'
      where
        c = p_apply_atom s b
        rho'
          | a == c = Map.delete a rho
          | otherwise = Map.insert a c rho

-- | Compose two permutations. O(/n/) where /n/ is the size of the left permutation.
-- This also requires the inverse of the right permutation as an input.
p_composeL :: Perm -> Perm -> Perm -> Perm
p_composeL (Perm sigma) (Perm tau) t'@(Perm tau_inv) = Perm rho
  where
    rho = Map.foldrWithKey f tau sigma
    f a b rho = rho'
      where
        c = p_apply_atom t' a
        rho'
          | c == b = Map.delete c rho
          | otherwise = Map.insert c b rho

-- | Apply a permutation to an atom. O(1).
p_apply_atom :: Perm -> Atom -> Atom
p_apply_atom (Perm sigma) a =
  case Map.lookup a sigma of
    Nothing -> a
    Just b -> b

-- | Swap /a/ and /b/. O(1)
p_swap :: Atom -> Atom -> Perm
p_swap a b
  | a == b = p_identity
  | otherwise = Perm (Map.singleton a b `Map.union` Map.singleton b a)

-- | Return the domain of a permutation. O(n).
p_domain :: Perm -> [Atom]
p_domain (Perm sigma) = Map.keys sigma

-- ----------------------------------------------------------------------
-- * The group of permutations

-- | The group of finitely supported permutations on atoms.

-- Implementation note: if we used 'Perm' directly, inverting a
-- permutation would be O(n). We make inverting O(1) by storing a
-- permutation and its inverse. Because of laziness, the inverse will
-- not be computed unless it is used.
data Permutation = Permutation Perm Perm
             deriving (Eq)

-- | The identity permutation. O(1).
perm_identity :: Permutation
perm_identity = Permutation p_identity p_identity

-- | Compose two permutations. O(/m/) where /m/ is the size of the
-- right permutation.
perm_composeR :: Permutation -> Permutation -> Permutation
perm_composeR (Permutation sigma sinv) (Permutation tau tinv) = Permutation rho rinv
  where
    rho = p_composeR sigma tau
    rinv = p_composeL tinv sinv sigma

-- | Compose two permutations. O(/n/) where /n/ is the size of the
-- left permutation.
perm_composeL :: Permutation -> Permutation -> Permutation
perm_composeL (Permutation sigma sinv) (Permutation tau tinv) = Permutation rho rinv
  where
    rho = p_composeL sigma tau tinv
    rinv = p_composeR tinv sinv

-- | Invert a permutation. O(1).
perm_invert :: Permutation -> Permutation
perm_invert (Permutation sigma sinv) = Permutation sinv sigma

-- | Apply a permutation to an atom. O(1).
perm_apply_atom :: Permutation -> Atom -> Atom
perm_apply_atom (Permutation sigma sinv) = p_apply_atom sigma

-- | Swap /a/ and /b/. O(1).
perm_swap :: Atom -> Atom -> Permutation
perm_swap a b = Permutation sigma sigma
  where
    sigma = p_swap a b

-- | The domain of a permutation. O(/n/).
perm_domain :: Permutation -> [Atom]
perm_domain (Permutation sigma sinv) = p_domain sigma

-- | Make a permutation from a list of swaps. This is mostly useful
-- for testing. O(/n/).
perm_of_swaps :: [(Atom, Atom)] -> Permutation
perm_of_swaps xs = aux xs where
  aux [] = perm_identity
  aux ((a,b):t) = perm_swap a b `perm_composeL` perm_of_swaps t

-- | Turn a permutation into a list of swaps. This is mostly useful
-- for testing. O(/n/).
swaps_of_perm :: Permutation -> [(Atom, Atom)]
swaps_of_perm sigma = [ y | Just y <- ys ]
  where
    domain = perm_domain sigma
    (tau, ys) = mapAccumL f sigma domain
    f acc a
      | a == b = (acc', Nothing)
      | otherwise = (acc', Just (a, b))
      where
        b = perm_apply_atom acc a
        acc' = perm_composeL (perm_swap a b) acc

-- ----------------------------------------------------------------------
-- * Defer

-- | 'Defer' /t/ is the type /t/, but equipped with an explicit substitution.
-- This is used to cache substitutions so that they can be optimized
-- and applied all at once.
data Defer t = Defer Permutation t

instance Nominal (Defer t) where
  -- This is where 'Defer' pays off. Rather than using 'force',
  -- we compile the permutations for later efficient use.
  π • (Defer sigma t) = Defer (perm_composeR π sigma) t
  
force :: (Nominal t) => Defer t -> t
force (Defer sigma t) = sigma • t

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
data Bind a t = Bind NameSuggestion (a -> Defer t)

-- | Atom abstraction: 'atom_abst' /a/ /t/ represents the equivalence
-- class of pairs (/a/,/t/) modulo alpha-equivalence. We first define
-- this for 'Atom' and later generalize to other 'Atomic' types.
atom_abst :: Atom -> t -> Bind Atom t
atom_abst a t = Bind (atom_names a) (\x -> Defer (perm_swap a x) t)

-- | Atom abstraction: (/a/./t/) represents the equivalence class of pairs
-- (/a/,/t/) modulo alpha-equivalence. Here, (/a/,/t/) ~ (/b/,/s/) iff
-- for fresh /c/, (/a/ /c/) • /t/ = (/b/ /c/) • /s/.
--
-- We use the infix operator '.', which is normally bound to function
-- composition in the standard library. Thus, nominal programs should
-- import the standard library like this:
--
-- > import Prelude hiding ((.))
(.) :: (Atomic a, Nominal t) => a -> t -> Bind a t
a.t = Bind ns f
  where
    Bind ns g = atom_abst (to_atom a) t
    f x = g (to_atom x)

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
open :: (Atomic a, Nominal t) => Bind a t -> (a -> t -> s) -> s
open (Bind ns f) body =
  with_fresh_namelist ns (\a -> body a (force (f a)))

instance (Atomic a, Nominal t, Eq t) => Eq (Bind a t) where
  Bind n f == Bind m g =
    with_fresh (\a -> force (f a) == force (g a))

instance (Nominal t) => Nominal (Bind a t) where
  -- Implementation note: here, we crucially use the assumption that
  -- in the HOAS encoding, the binder will only be opened with fresh
  -- atoms.
  π • (Bind n f) = Bind n (\x -> π • (f x))

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
merge (Bind ns f) (Bind ns' g) = (Bind ns'' h) where
  ns'' = combine_names ns ns'
  h x = Defer perm_identity (force (f x), force (g x))

-- ----------------------------------------------------------------------
-- * Display of nominal values

-- | Something to be avoided can be an atom or a string.
data Avoidee = A Atom | S String
             deriving (Eq, Ord, Show)

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

strings_of_support :: Support -> Set String
strings_of_support (Support s) = Set.map name s where
  name (A a) = show a
  name (S s) = s
                 
newtype Literal = Literal String
                deriving (Show)

instance Nominal Literal where
  π • t = t

-- | 'NominalShow' is a helper class to support pretty-printing of
-- nominal values. Most 'Nominal' types are also 'NominalShow', with
-- the exception of function types (for which we cannot compute the
-- support).

class (Nominal t) => NominalShow t where
  -- | Compute a set of atoms and strings that should not be used as
  -- the names of bound variables. Usually this is defined by
  -- straightforward recursive clauses. The recursive clauses must
  -- apply 'support' to a tuple or list (or combination thereof) of
  -- immediate subterms.
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
  nominal_showsPrecSup sup d t s = nominal_show t ++ s

  -- | For primitive types that don't have any subterms, cannot contain
  -- binders, and don't require parenthesis, it may be more convenient
  -- to define 'nominal_show' instead of 'nominal_showsPrecSup'. For
  -- such types, it is also okay to derive a 'Show' instance and
  -- define 'nominal_show' as 'show'.
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

  {-# MINIMAL (nominal_showsPrecSup | nominal_show), support #-}

-- | This function should be used in the definition of 'Show'
-- instances for nominal types, like this:
--
-- > instance Show MyType where
-- >   showsPrec = nominal_showsPrec
nominal_showsPrec :: (NominalShow t) => Int -> t -> ShowS
nominal_showsPrec d t = nominal_showsPrecSup (support t) d t

-- | Since we hide (.) from the standard library, and it is not legal syntax
-- to write @Prelude..@, we provide 'cp' as an alternate notation for
-- composition. This is particularly useful in defining 'showsPrec'
-- and 'nominal_showsPrecSup'.
cp :: (b -> c) -> (a -> b) -> (a -> c)
cp g f x = g (f x)

-- Primitive cases.
instance Show Atom where
  show = show_atom

instance NominalShow Atom where
  support a = support_atom a
  nominal_show = show_atom

instance NominalShow Literal where
  support (Literal s) = support_string s
  nominal_show = show

instance (NominalShow t) => NominalShow [t] where
  support ts = support_unions (map support ts)
  nominal_showsPrecSup sup d ts = nominal_showList sup ts

instance (NominalShow t, NominalShow s) => NominalShow (t,s) where
  support (t, s) = support_union (support t) (support s)
  nominal_showsPrecSup sup d (t, s) = showString $
    "("
    ++ nominal_showsPrecSup sup 0 t ""
    ++ ","
    ++ nominal_showsPrecSup sup 0 s ""
    ++ ")"
        
instance NominalShow () where
  support t = support_empty
  nominal_show = show

-- Derived cases.
instance NominalShow Integer where
  support t = support ()
  nominal_show = show

instance NominalShow Int where
  support t = support ()
  nominal_show = show

instance NominalShow Char where
  support t = support ()
  nominal_show = show
  nominal_showList sup ts = shows ts

instance (NominalShow t, NominalShow s, NominalShow r) => NominalShow (t,s,r) where
  support (t, s, r) = support (t, (s, r))
  nominal_showsPrecSup sup d (t, s, r) = showString $
    "("
    ++ nominal_showsPrecSup sup 0 t ""
    ++ ","
    ++ nominal_showsPrecSup sup 0 s ""
    ++ ","
    ++ nominal_showsPrecSup sup 0 r ""
    ++ ")"

-- ... and so on for tuples.

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
open_for_printing :: (Atomic a, NominalShow t) => Support -> Bind a t -> (a -> t -> Support -> s) -> s
open_for_printing sup t@(Bind ns f) body =
  with_fresh_named n1 (\a -> body a (force (f a)) (sup' a))
  where
    n1 = rename_fresh (strings_of_support sup) ns
    name (A a) = show a
    name (S s) = s
    sup' a = support_union sup (support_atom (to_atom a))

instance (NominalShow t) => NominalShow (Defer t) where
  support t = support (force t)
  nominal_showsPrecSup sup d t = nominal_showsPrecSup sup d (force t)
  
instance (Atomic a, NominalShow t) => NominalShow (Bind a t) where
  support (Bind n f) =
    with_fresh (\a -> support_delete (to_atom a) (support (f a)))
  nominal_showsPrecSup sup d t =
    open_for_printing sup t $ \a s sup' ->
      showParen (d > 5) $
        showString (show a ++ "." ++ nominal_showsPrecSup sup' 5 s "")

instance (Atomic a, NominalShow t) => Show (Bind a t) where
  showsPrec = nominal_showsPrec

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
