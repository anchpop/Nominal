-- | This module provides an efficient implementation of finitely
-- supported permutations of atoms.  Compositions and inverses can
-- both be computed with O(/n/) 'Map' lookup operations.
--
-- This module exposes implementation details of the Nominal library,
-- and should not normally be imported. Users of the library should
-- only import the top-level module "Nominal".

module Nominal.Permutation where

import Data.List
import Data.Map (Map)
import qualified Data.Map as Map

import Nominal.Atom

-- ----------------------------------------------------------------------
-- * The monoid of permutations

-- | The monoid of finitely supported permutations on atoms.
newtype Perm = Perm (Map Atom Atom)
             deriving (Eq, Show)

-- | The identity permutation. O(1).
p_identity :: Perm
p_identity = Perm Map.empty

-- | Compose two permutations. O(/m/) where /m/ is the size of the
-- right permutation.
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

-- | Compose two permutations. O(/n/) where /n/ is the size of the
-- left permutation.  This also requires the inverse of the right
-- permutation as an input.
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

-- | Swap /a/ and /b/. O(1).
p_swap :: Atom -> Atom -> Perm
p_swap a b
  | a == b = p_identity
  | otherwise = Perm (Map.singleton a b `Map.union` Map.singleton b a)

-- | Return the domain of a permutation. O(n).
p_domain :: Perm -> [Atom]
p_domain (Perm sigma) = Map.keys sigma

-- ----------------------------------------------------------------------
-- * The group of permutations

-- | The group of finitely supported permutations on atoms.  This is
-- an abstract type with no exposed structure.
data NominalPermutation = Permutation Perm Perm
  -- ^ Implementation note: If we used 'Perm' directly, inverting a
  -- permutation would be O(n). We make inverting O(1) by storing a
  -- permutation together with its inverse. Because of laziness, the
  -- inverse will not be computed unless it is used.
  deriving (Eq)

-- | A type synonym.
type Permutation = NominalPermutation

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

-- | Swap the given pairs of atoms.
perm_swaps :: [(Atom,Atom)] -> Permutation
perm_swaps [] = perm_identity
perm_swaps ((a,b):xs) = perm_swap a b `perm_composeL` perm_swaps xs

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

