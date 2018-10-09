{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}

-- | A package for working with binders.

module Nominal (
  Atom,
  Atomic,
  with_fresh,
  with_fresh_named,
  with_fresh_namelist,
  bind,
  bind_named,
  bind_namelist,
  Nominal(..),
  Permutation,
  NominalSupport(..),
  NominalShow(..),
  Support,
  Literal(..),
  AtomKind(..),
  AtomOfKind,
  (∘),
  nominal_showsPrec,
  NameSuggestion,
  Bindable(..),
  merge,
  (.),
  AtomPlus(..),
  with_fresh_plus,
  with_fresh_named_plus,
  with_fresh_namelist_plus,
  Generic
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
import GHC.Generics

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

-- | Check if the character is a letter or underscore.
isAlphaOrWild :: Char -> Bool
isAlphaOrWild c = isAlpha c || c == '_'

-- | An infinite list of strings, based on the suggested names.
varnames :: NameSuggestion -> [String]
varnames xs0 = xs1 ++ xs3 ++ [ x ++ map to_subscript (show n) | n <- [1..], x <- xs3 ]
  where
    xs1 = [ x | x <- xs0, x /= "" ]
    xs2 = [ y | x <- xs0, let y = takeWhile isAlphaOrWild x, y /= "" ]
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
-- * A global variable

-- | A global variable holding a set of strings already used for free
-- names.
global_used :: IORef (Set String)
global_used = unsafePerformIO $ do
  newIORef Set.empty

-- | Create a globally new concrete name based on the given name
-- suggestion.
global_new :: NameSuggestion -> String
global_new ns = unsafePerformIO $ do
  used <- readIORef global_used
  let n = rename_fresh used ns
  writeIORef global_used (Set.insert n used)
  return n

-- ----------------------------------------------------------------------
-- * Atoms

-- | An atom is a globally unique, opaque value with a concrete name
-- and some optional name suggestions.
data Atom = Atom Unique String NameSuggestion

instance Eq Atom where
  -- We only compare the unique identifier, because the name
  -- suggestions may be large or even infinite.
  Atom x n ns == Atom x' n' ns' = x == x'

instance Ord Atom where
  -- We only compare the unique identifier, because the name
  -- suggestions may be large or even infinite.
  compare (Atom x n ns) (Atom x' n' ns') = compare x x'

-- | Create a fresh atom with the given name suggestions.

-- Implementation note: the call to global_new is purposely done
-- outside the IO monad, so that an actual concrete name will only be
-- computed on demand.
fresh_atom_namelist :: NameSuggestion -> IO Atom
fresh_atom_namelist ns = do
  x <- newUnique
  return (Atom x (global_new ns) ns)

-- | Create a fresh atom with the given concrete name.
fresh_atom_named :: String -> IO Atom
fresh_atom_named n = do
  x <- newUnique
  return (Atom x n [n])

-- | Return the suggested names of an atom.
atom_names :: Atom -> NameSuggestion
atom_names (Atom x n ns) = ns

-- | Make sure the atom has name suggestions, by adding the specified
-- ones if none are present.
add_default_names :: NameSuggestion -> Atom -> Atom
add_default_names ns (Atom x n []) = Atom x n ns
add_default_names ns (Atom x n ns') = Atom x n ns'

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

force :: (Nominal t) => Defer t -> t
force (Defer sigma t) = sigma • t

instance Nominal (Defer t) where
  -- This is where 'Defer' pays off. Rather than using 'force',
  -- we compile the permutations for later efficient use.
  π • (Defer sigma t) = Defer (perm_composeR π sigma) t
  
-- ----------------------------------------------------------------------
-- * Nominal types

-- | A type is 'Nominal' if the group of finitely supported permutations
-- of atoms acts on it. We can abstract over an atom in such a type.

-- Language note: in an ideal programming language, 'Nominal'
-- instances for new datatypes could be derived with 'deriving'.
class Nominal t where
  -- | Apply a permutation of atoms to a term.
  (•) :: Permutation -> t -> t

  default (•) :: (Generic t, GNominal (Rep t)) => Permutation -> t -> t
  π • x = to (gbullet π (from x))
  
instance Nominal Atom where
  (•) = perm_apply_atom

instance Nominal Integer where
  π • t = t

instance Nominal Int where
  π • t = t

instance Nominal Char where
  π • t = t

instance (Nominal t) => Nominal [t]
instance Nominal ()
instance (Nominal t, Nominal s) => Nominal (t,s)
instance (Nominal t, Nominal s, Nominal r) => Nominal (t,s,r)
instance (Nominal t, Nominal s, Nominal r, Nominal q) => Nominal (t,s,r,q)
instance (Nominal t, Nominal s, Nominal r, Nominal q, Nominal p) => Nominal (t,s,r,q,p)
instance (Nominal t, Nominal s, Nominal r, Nominal q, Nominal p, Nominal o) => Nominal (t,s,r,q,p,o)
instance (Nominal t, Nominal s, Nominal r, Nominal q, Nominal p, Nominal o, Nominal n) => Nominal (t,s,r,q,p,o,n)

instance (Nominal t, Nominal s) => Nominal (t -> s) where
  π • f = \x -> π • (f (π' • x))
    where
      π' = perm_invert π

instance (Nominal t) => Nominal (BindAtom t) where
  π • (BindAtom n f) = BindAtom n (\x -> π • (f x))

instance (NominalSupport t) => NominalSupport (BindAtom t) where
  support (BindAtom n f) =
    with_fresh (\a -> support_delete a (support (f a)))

instance (Nominal t, Eq t) => Eq (BindAtom t) where
  b1 == b2 = atom_open (atom_merge b1 b2) $ \a (t1,t2) -> t1 == t2

-- ----------------------------------------------------------------------
-- * Atom abstraction

-- | 'BindAtom' /t/ is the type of atom abstractions, denoted [a]t in
-- the nominal logic literature. Its elements are of the form (a.v)
-- modulo alpha-equivalence. For more details on what this means, see
-- Definition 4 of [Pitts 2002].

-- Implementation note: we currently use an HOAS encoding. It remains
-- to be seen whether this is efficient. An important invariant of the
-- HOAS encoding is that the underlying function must only be applied
-- to /fresh/ atoms.
-- 
-- It would also be possible to use a DeBruijn encoding or a nameful
-- encoding. It remains to be seen which encoding is the most
-- efficient in practice.
data BindAtom t = BindAtom NameSuggestion (Atom -> Defer t)

-- | Atom abstraction: 'atom_abst' /a/ /t/ represents the equivalence
-- class of pairs (/a/,/t/) modulo alpha-equivalence. We first define
-- this for 'Atom' and later generalize to other 'Atomic' types.
atom_abst :: Atom -> t -> BindAtom t
atom_abst a t = BindAtom (atom_names a) (\x -> Defer (perm_swap a x) t)

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
atom_open :: (Nominal t) => BindAtom t -> (Atom -> t -> s) -> s
atom_open (BindAtom ns f) body =
  with_fresh_namelist ns (\a -> body a (force (f a)))

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
atom_open_for_printing :: (Nominal t) => NameSuggestion -> Support -> BindAtom t -> (Atom -> t -> Support -> s) -> s
atom_open_for_printing ns2 sup t@(BindAtom ns f) body =
  with_fresh_named n1 (\a -> body a (force (f a)) (sup' a))
  where
    ns1 = if null ns then ns2 else ns
    n1 = rename_fresh (strings_of_support sup) ns1
    sup' a = support_insert a sup

-- | Sometimes, it is necessary to open two abstractions, using the
-- /same/ fresh name for both of them. An example of this is the
-- typing rule for lambda abstraction in dependent type theory:
--
-- >           Gamma, x:t  |-  e : s
-- >      ------------------------------------
-- >        Gamma |-  Lam (x.e) : Pi t (x.s)
--
-- In the bottom-up reading of this rule, we are given the terms @Lam@
-- /body/ and @Pi@ /t/ /body'/, and we require a fresh name /x/ and
-- terms /e/, /s/ such that /body/ = (/x/./e/) and /body'/ =
-- (/x/./s/).  Crucially, the same atom /x/ should be used in both /e/
-- and /s/, because we subsequently need to check that /e/ has type
-- /s/ in some scope that is common to /e/ and /s/.
--
-- The 'merge' primitive permits us to deal with such situations.  Its
-- defining property is
--
-- > merge (x.e) (x.s) = (x.(e,s)).
--
-- We can therefore solve the above problem:
--
-- > open (merge body body') (\x (e,s) -> .....)
--
-- Moreover, the 'merge' primitive can be used to define other
-- merge-like functionality. For example, it is easy to define a
-- function
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
atom_merge :: (Nominal t, Nominal s) => BindAtom t -> BindAtom s -> BindAtom (t,s)
atom_merge (BindAtom ns f) (BindAtom ns' g) = (BindAtom ns'' h) where
  ns'' = combine_names ns ns'
  h x = Defer perm_identity (force (f x), force (g x))

-- ----------------------------------------------------------------------
-- * The Bindable class

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
-- * Bindable instances

instance Bindable Atom where
  newtype Bind Atom t = BindA (BindAtom t)
  bindable_action π (BindA body) = BindA (π • body)
  bindable_support (BindA body) = support body
  bindable_eq (BindA b1) (BindA b2) = b1 == b2
  abst a t = BindA (atom_abst a t)
  open (BindA body) k = atom_open body k
  open_for_printing sup (BindA body) k = atom_open_for_printing default_names sup body k

instance (Bindable a) => Bindable (AtomPlus a t) where
  data Bind (AtomPlus a t) s = BindAP t (Bind a s)
  bindable_action π (BindAP t body) = BindAP t (π • body)
  bindable_support (BindAP t body) = support body
  bindable_eq (BindAP t1 b1) (BindAP t2 b2) = open b1 $ \a _ -> AtomPlus a t1 == AtomPlus a t2 && b1 == b2
  abst (AtomPlus a t) body = BindAP t (abst a body)
  open (BindAP t body) k = open body $ \a s -> k (AtomPlus a t) s
  open_for_printing sup (BindAP t body) k = open_for_printing sup body $ \a s -> k (AtomPlus a t) s

instance (AtomKind a) => Bindable (AtomOfKind a) where
  newtype Bind (AtomOfKind a) t = BindAK (BindAtom t)
  bindable_action π (BindAK body) = BindAK (π • body)
  bindable_support (BindAK body) = support body
  bindable_eq (BindAK b1) (BindAK b2) = b1 == b2
  abst a t = BindAK body where
    BindA body = (abst (to_atom a) t)
  open (BindAK body) k = open (BindA body) (\a t -> k (from_atom a) t)
  open_for_printing sup b@(BindAK body) k = atom_open_for_printing ns sup body (\a t -> k (from_atom a) t)
    where
      ns = names (un b)
      un :: Bind a t -> a
      un = undefined

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
-- 'Nominal', 'NominalSupport', 'NominalShow', 'Eq', and 'Ord', and
-- defining a 'Show' instance:
--
-- > {-# LANGUAGE GeneralizedNewtypeDeriving #-}
-- >
-- > newtype Variable = Variable Atom
-- >   deriving (Atomic, Nominal, NominalSupport, NominalShow, Eq, Ord)
-- > 
-- > instance Show Variable where
-- >   showsPrec = nominal_showsPrec
class (Nominal a, NominalSupport a, NominalShow a, Eq a, Ord a, Show a, Bindable a) => Atomic a where
  to_atom :: a -> Atom
  from_atom :: Atom -> a

  -- | The default variable names for the atom type.
  names :: a -> NameSuggestion

show_atom :: (Atomic a) => a -> String
show_atom a = n
  where
    Atom x n ns = to_atom a

to_bindatom :: (Atomic a, Nominal t) => Bind a t -> BindAtom t
to_bindatom body = open body $ \a t -> atom_abst (to_atom a) t

from_bindatom :: (Atomic a, Nominal t) => BindAtom t -> Bind a t
from_bindatom body = atom_open body $ \a t -> (from_atom a . t)

instance Atomic Atom where
  to_atom = id
  from_atom = id
  names a = default_names

-- | Sometimes, it is necessary to open two abstractions, using the
-- /same/ fresh name for both of them. An example of this is the
-- typing rule for lambda abstraction in dependent type theory:
--
-- >           Gamma, x:t  |-  e : s
-- >      ------------------------------------
-- >        Gamma |-  Lam (x.e) : Pi t (x.s)
--
-- In the bottom-up reading of this rule, we are given the terms @Lam@
-- /body/ and @Pi@ /t/ /body'/, and we require a fresh name /x/ and
-- terms /e/, /s/ such that /body/ = (/x/./e/) and /body'/ =
-- (/x/./s/).  Crucially, the same atom /x/ should be used in both /e/
-- and /s/, because we subsequently need to check that /e/ has type
-- /s/ in some scope that is common to /e/ and /s/.
--
-- The 'merge' primitive permits us to deal with such situations.  Its
-- defining property is
--
-- > merge (x.e) (x.s) = (x.(e,s)).
--
-- We can therefore solve the above problem:
--
-- > open (merge body body') (\x (e,s) -> .....)
--
-- Moreover, the 'merge' primitive can be used to define other
-- merge-like functionality. For example, it is easy to define a
-- function
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
merge at as = from_bindatom (atom_merge (to_bindatom at) (to_bindatom as))

-- | A convenience function for constructing binders. 
--
-- > bind (\x -> t)
--
-- is a convenient way to write the atom abstraction (x.t),
-- where /x/ is a fresh variable.
bind :: (Atomic a, Nominal t) => (a -> t) -> Bind a t
bind body = bind_namelist ns body
  where
    ns = names (un body)
    un :: (a -> t) -> a
    un = undefined

-- | A version of 'bind' that also takes a suggested name for the bound atom.
bind_named :: (Atomic a, Nominal t) => String -> (a -> t) -> Bind a t
bind_named n = bind_namelist [n]

-- | A version of 'bind' that also take a list of suggested names for the bound atom.
bind_namelist :: (Atomic a, Nominal t) => NameSuggestion -> (a -> t) -> Bind a t
bind_namelist ns f = with_fresh_namelist ns (\x -> x . f x)

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
with_fresh body = with_fresh_namelist ns body
  where
    ns = names (un body)
    un :: (a -> t) -> a
    un = undefined

-- | A version of 'with_fresh' that permits a suggested name to be
-- given to the atom. The name is only a suggestion, and will be
-- changed, if necessary, to avoid clashes.
with_fresh_named :: (Atomic a) => String -> (a -> t) -> t
with_fresh_named n body = unsafePerformIO $ do
  a <- fresh_atom_named n
  return (body (from_atom a))

-- | A version of 'with_fresh' that permits a list of suggested names
-- to be specified. The first suitable name in the list will be used
-- if possible.
{-# NOINLINE with_fresh_namelist #-}
with_fresh_namelist :: (Atomic a) => NameSuggestion -> (a -> t) -> t
with_fresh_namelist ns body = unsafePerformIO $ do
  a <- fresh_atom_namelist ns
  return (body (from_atom a))

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

support_insert :: Atom -> Support -> Support
support_insert a (Support x) = Support (Set.insert (A a) x)

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

-- | 'NominalSupport' is a subclass of 'Nominal' consisting of those
-- types for which the support can be calculated. With the exception
-- of function types, most 'Nominal' types are also 'NominalSupport'.
class (Nominal t) => NominalSupport t where
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

  default support :: (Generic t, GNominalSupport (Rep t)) => t -> Support
  support x = gsupport (from x)

-- | 'NominalShow' is a helper class to support pretty-printing of
-- nominal values. Most 'Nominal' types are also 'NominalShow', with
-- the exception of function types (for which we cannot compute the
-- support).

class (NominalSupport t) => NominalShow t where
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

  -- | Like 'show', but for nominal types.
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

  default nominal_showsPrecSup :: (Generic t, GNominalShow (Rep t)) => Support -> Int -> t -> ShowS
  nominal_showsPrecSup sup d x = gnominal_showsPrecSup Pre sup d (from x)

-- | This function should be used in the definition of 'Show'
-- instances for nominal types, like this:
--
-- > instance Show MyType where
-- >   showsPrec = nominal_showsPrec
nominal_showsPrec :: (NominalShow t) => Int -> t -> ShowS
nominal_showsPrec d t = nominal_showsPrecSup (support t) d t

-- | This function can be used in defining NominalShow instances for
-- non-nominal types, where the instance should be derived from an
-- ordinary 'Show' instance.
simple_showsPrecSup :: (Show t) => Support -> Int -> t -> ShowS
simple_showsPrecSup dup d x = showString (show x)

-- | Since we hide (.) from the standard library, and it is not legal syntax
-- to write @Prelude..@, we provide '∘' as an alternate notation for
-- composition. This is particularly useful in defining 'showsPrec'
-- and 'nominal_showsPrecSup'.
(∘) :: (b -> c) -> (a -> b) -> (a -> c)
(g ∘ f) x = g (f x)

-- Primitive cases.
instance Show Atom where
  show = show_atom

instance NominalSupport Atom where
  support a = support_atom a

instance NominalShow Atom where
  nominal_showsPrecSup sup d t = showString (show_atom t)

instance NominalSupport Literal where
  support (Literal s) = support_string s

instance NominalShow Literal where
  nominal_showsPrecSup = simple_showsPrecSup

instance NominalSupport ()
instance NominalShow ()

-- Derived cases.
instance NominalSupport Integer where
  support t = support ()

instance NominalShow Integer where
  nominal_showsPrecSup = simple_showsPrecSup

instance NominalSupport Int where
  support t = support ()

instance NominalShow Int where
  nominal_showsPrecSup = simple_showsPrecSup

instance NominalSupport Char where
  support t = support ()

instance NominalShow Char where
  nominal_showsPrecSup = simple_showsPrecSup
  nominal_showList sup ts = shows ts

instance (NominalSupport t, NominalSupport s) => NominalSupport (t,s)
instance (NominalSupport t, NominalSupport s, NominalSupport r) => NominalSupport (t,s,r)
instance (NominalSupport t, NominalSupport s, NominalSupport r, NominalSupport q) => NominalSupport (t,s,r,q)
instance (NominalSupport t, NominalSupport s, NominalSupport r, NominalSupport q, NominalSupport p) => NominalSupport (t,s,r,q,p)
instance (NominalSupport t, NominalSupport s, NominalSupport r, NominalSupport q, NominalSupport p, NominalSupport o) => NominalSupport (t,s,r,q,p,o)
instance (NominalSupport t, NominalSupport s, NominalSupport r, NominalSupport q, NominalSupport p, NominalSupport o, NominalSupport n) => NominalSupport (t,s,r,q,p,o,n)

instance (NominalShow t, NominalShow s) => NominalShow (t,s)
instance (NominalShow t, NominalShow s, NominalShow r) => NominalShow (t,s,r)
instance (NominalShow t, NominalShow s, NominalShow r, NominalShow q) => NominalShow (t,s,r,q)
instance (NominalShow t, NominalShow s, NominalShow r, NominalShow q, NominalShow p) => NominalShow (t,s,r,q,p)
instance (NominalShow t, NominalShow s, NominalShow r, NominalShow q, NominalShow p, NominalShow o) => NominalShow (t,s,r,q,p,o)
instance (NominalShow t, NominalShow s, NominalShow r, NominalShow q, NominalShow p, NominalShow o, NominalShow n) => NominalShow (t,s,r,q,p,o,n)

-- ... and so on for tuples.

instance (NominalSupport t) => NominalSupport [t]

instance (NominalShow t) => NominalShow [t] where
  -- Lists require special treatment.
  nominal_showsPrecSup sup d ts = nominal_showList sup ts

instance (Ord k, Nominal k, Nominal v) => Nominal (Map k v) where
  π • map = Map.fromList [ (π • k, π • v) | (k, v) <- Map.toList map ]

instance (Ord k, NominalSupport k, NominalSupport v) => NominalSupport (Map k v) where
  support map = support (Map.toList map)

instance (Ord k, NominalShow k, NominalShow v) => NominalShow (Map k v) where
  nominal_showsPrecSup sup d m =
    showParen (d > 10) $
      showString "fromList " ∘ nominal_showsPrecSup sup 11 (Map.toList m)

instance (NominalSupport t) => NominalSupport (Defer t) where
  support t = support (force t)

instance (NominalShow t) => NominalShow (Defer t) where
  nominal_showsPrecSup sup d t = nominal_showsPrecSup sup d (force t)

instance (Bindable a, NominalSupport t) => NominalSupport (Bind a t) where
  support = bindable_support

instance (Bindable a, NominalShow a, NominalShow t) => NominalShow (Bind a t) where
  nominal_showsPrecSup sup d t =
    open_for_printing sup t $ \a s sup' ->
      showParen (d > 5) $
        showString (nominal_show a ++ " . " ++ nominal_showsPrecSup sup' 5 s "")

instance (Bindable a, NominalShow a, NominalShow t) => Show (Bind a t) where
  showsPrec = nominal_showsPrec

-- ----------------------------------------------------------------------
-- * Multiple atom types

-- | The type class 'AtomKind' requires a single method, which is
-- moreover optional: a list of suggested names for this kind of atom.
-- For example:
--
-- > data VarName
-- > instance AtomKind VarName where suggested_names a = ["x", "y", "z"]
--
-- > data TypeName
-- > instance AtomKind TypeName where suggested_names a = ["a", "b", "c"]
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
  suggested_names a = default_names

-- | The type of atoms of a given kind. For example:
--
-- > type Variable = AtomOfKind VarName
-- > type Type = AtomOfKind TypeName
newtype AtomOfKind a = AtomOfKind Atom
  deriving (Nominal, Eq, Ord)

instance (AtomKind a) => NominalSupport (AtomOfKind a) where
  support a = support (add_default_names (names a) (to_atom a))

instance (AtomKind a) => NominalShow (AtomOfKind a) where
  nominal_showsPrecSup sup d t = showString (show_atom t)

instance (AtomKind a) => Show (AtomOfKind a) where
  show = show_atom

instance (AtomKind a) => Atomic (AtomOfKind a) where
  to_atom (AtomOfKind a) = a
  from_atom a = AtomOfKind a
  names f = suggested_names (un f)
    where
      un :: AtomOfKind a -> a
      un = undefined

-- ----------------------------------------------------------------------
-- * AtomPlus

-- | A type of atoms that are equipped with additional information.
-- The information should not itself be nominal. Examples are: bound
-- variables that are equipped with information about the binding
-- site; type variables that are equipped with flags or boolean
-- constraints.
--
-- Here, /a/ is an 'Atomic' instance, and /t/ is the type of the
-- additional information stored in the atom.
data AtomPlus a t = AtomPlus a t
  deriving (Show)

instance (Nominal a) => Nominal (AtomPlus a t) where
  π • AtomPlus a t = AtomPlus (π • a) t

instance (Eq a) => Eq (AtomPlus a t) where
  -- We only compare the unique identifier, for efficiency.
  AtomPlus x t == AtomPlus x' t' = x == x'

instance (Ord a) => Ord (AtomPlus a t) where
  -- We only compare the unique identifier, for efficiency.
  compare (AtomPlus x t) (AtomPlus x' t') = compare x x'

instance (NominalSupport a) => NominalSupport (AtomPlus a t) where
  support (AtomPlus x t) = support x

instance (NominalSupport a, Show a, Show t) => NominalShow (AtomPlus a t) where
  nominal_showsPrecSup = simple_showsPrecSup

with_fresh_plus :: (Atomic a) => t -> (AtomPlus a t -> s) -> s
with_fresh_plus t k =
  with_fresh $ \a -> k (AtomPlus a t)
    

with_fresh_named_plus :: (Atomic a) => t -> String -> (AtomPlus a t -> s) -> s
with_fresh_named_plus t n k =
  with_fresh_named n $ \a -> k (AtomPlus a t)

with_fresh_namelist_plus :: (Atomic a) => t -> NameSuggestion -> (AtomPlus a t -> s) -> s
with_fresh_namelist_plus t n k =
  with_fresh_namelist n $ \a -> k (AtomPlus a t)

-- ----------------------------------------------------------------------
-- * Generic programming

-- $ This allows the user to automatically derive 'Nominal',
-- 'NominalSupport', and 'NominalShow' instances. All the user has to
-- do is add the language options DeriveGeneric and DeriveAnyClass, and
-- add
--
-- > deriving (Generic, Nominal, NominalSupport, NominalShow)
--
-- to any nominal datatype.

-- ----------------------------------------------------------------------
-- ** Generic Nominal instances

class GNominal f where
  gbullet :: Permutation -> f a -> f a

instance GNominal V1 where
  gbullet π x = undefined  -- Does not occur, because V1 is an empty type.

instance GNominal U1 where
  gbullet π U1 = U1

instance (GNominal a, GNominal b) => GNominal (a :*: b) where
  gbullet π (a :*: b) = gbullet π a :*: gbullet π b

instance (GNominal a, GNominal b) => GNominal (a :+: b) where
  gbullet π (L1 x) = L1 (gbullet π x)
  gbullet π (R1 x) = R1 (gbullet π x)

instance (GNominal a) => GNominal (M1 i c a) where
  gbullet π (M1 x) = M1 (gbullet π x)

instance (Nominal a) => GNominal (K1 i a) where
  gbullet π (K1 x) = K1 (π • x)

-- ----------------------------------------------------------------------
-- ** Generic NominalSupport instances

class GNominalSupport f where
  gsupport :: f a -> Support

instance GNominalSupport V1 where
  gsupport x = undefined -- Does not occur, because V1 is an empty type.

instance GNominalSupport U1 where
  gsupport U1 = support_empty

instance (GNominalSupport a, GNominalSupport b) => GNominalSupport (a :*: b) where
  gsupport (a :*: b) = support_union (gsupport a) (gsupport b)

instance (GNominalSupport a, GNominalSupport b) => GNominalSupport (a :+: b) where
  gsupport (L1 x) = gsupport x
  gsupport (R1 x) = gsupport x

instance (GNominalSupport a) => GNominalSupport (M1 i c a) where
  gsupport (M1 x) = gsupport x

instance (NominalSupport a) => GNominalSupport (K1 i a) where
  gsupport (K1 x) = support x

-- ----------------------------------------------------------------------
-- ** Generic NominalShow instances

-- The implementation follows along similar lines as
-- "Generics.Deriving.Show".

-- | This type keeps track of which separator to use for the next tuple.
data Separator = Rec | Tup | Inf String | Pre

class GNominalShow f where
  gnominal_showsPrecSup :: Separator -> Support -> Int -> f a -> ShowS
  isNullary :: f a -> Bool
  isNullary x = False

instance GNominalShow V1 where
  -- Does not occur, because V1 is an empty type.
  gnominal_showsPrecSup sep sup d t s = undefined 
  
instance GNominalShow U1 where
  gnominal_showsPrecSup sep sup d t s = s
  isNullary x = True

instance (GNominalShow a, GNominalShow b) => GNominalShow (a :*: b) where
  gnominal_showsPrecSup sep sup d (x :*: y) = 
    gnominal_showsPrecSup sep sup prec x
    ∘ showString separator
    ∘ gnominal_showsPrecSup sep sup prec y
    where
      (separator, prec) = case sep of
        Rec -> (", ", d)
        Tup -> (",", d)
        Inf s -> (" " ++ s ++ " ", d)
        Pre -> (" ", 11)

instance (GNominalShow a, GNominalShow b) => GNominalShow (a :+: b) where
  gnominal_showsPrecSup sep sup d (L1 x) = gnominal_showsPrecSup sep sup d x
  gnominal_showsPrecSup sep sup d (R1 x) = gnominal_showsPrecSup sep sup d x

instance (GNominalShow a) => GNominalShow (M1 D c a) where
  gnominal_showsPrecSup sep sup d (M1 x) = gnominal_showsPrecSup sep sup d x

instance (GNominalShow a, Constructor c) => GNominalShow (M1 C c a) where
  gnominal_showsPrecSup sep sup d c@(M1 x) =
    case fixity of
      Prefix
        | isNullary x -> showString name
        | isTuple name -> showParen True $ gnominal_showsPrecSup Tup sup 0 x
        | conIsRecord c -> showParen (d > 10) $
          showString name
          ∘ showString " "
          ∘ showString "{"
          ∘ gnominal_showsPrecSup Rec sup 0 x
          ∘ showString "}"
        | otherwise -> showParen (d > 10) $
        showString name
        ∘ showString " "
        ∘ gnominal_showsPrecSup Pre sup 11 x
      Infix assoc prec -> showParen (d > prec) $
        gnominal_showsPrecSup (Inf name) sup (prec+1) x
    where
      name = conName c
      fixity = conFixity c
      isTuple ('(' : ',' : _) = True
      isTuple _ = False

instance (GNominalShow a, Selector c) => GNominalShow (M1 S c a) where
  gnominal_showsPrecSup sep sup d s@(M1 x)
    | null name = gnominal_showsPrecSup sep sup d x
    | otherwise =
      showString name
      ∘ showString " = "
      ∘ gnominal_showsPrecSup sep sup d x
    where
      name = selName s

instance (NominalShow a) => GNominalShow (K1 i a) where
  gnominal_showsPrecSup sep sup d (K1 x) = nominal_showsPrecSup sup d x
