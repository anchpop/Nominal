{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}

-- | This module provides the 'Nominal' type class. A type is
-- 'Nominal' if the group of finitely supported permutations of atoms
-- acts on it. We can abstract over an atom in such a type.
--
-- We also provide some generic programming so that instances of
-- 'Nominal' can be automatically derived in most cases. All the user
-- has to do is add the language options @DeriveGeneric@ and
-- @DeriveAnyClass@ and import "GHC.Generics". Then @deriving
-- (Generic, Nominal)@ can be added to most datatype declarations.
-- Example:
--
-- > {-# LANGUAGE DeriveGeneric #-}
-- > {-# LANGUAGE DeriveAnyClass #-}
-- > import GHC.Generics
-- >
-- > data Term = Var Variable | App Term Term | Abs (Bind Variable Term)
-- >   deriving (Generic, Nominal)

module Nominal.Nominal where

import GHC.Generics

import Nominal.Atoms
import Nominal.Permutations

-- ----------------------------------------------------------------------
-- * The Nominal class

-- | A type is 'Nominal' if the group of finitely supported permutations
-- of atoms acts on it.
class Nominal t where
  -- | Apply a permutation of atoms to a term.
  (•) :: Permutation -> t -> t

  default (•) :: (Generic t, GNominal (Rep t)) => Permutation -> t -> t
  π • x = to (gbullet π (from x))

-- Some common instances

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

-- ----------------------------------------------------------------------
-- * Generic Nominal instances

-- | A version of the 'Nominal' class suitable for generic programming.
class GNominal f where
  gbullet :: Permutation -> f a -> f a

instance GNominal V1 where
  gbullet π x = undefined -- Does not occur, because V1 is an empty type.

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

