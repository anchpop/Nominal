{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

-- | This file illustrates how to derive generic instances for
-- 'Nominal', 'NominalSupport', 'NominalShow', and 'Bindable'.

module GenericInstances where

import Nominal
import Prelude hiding ((.))

-- ----------------------------------------------------------------------
-- * Example 1: MyTree

data MyTree a = Leaf | Branch a (MyTree a) (MyTree a)
  deriving (Generic, Nominal, NominalSupport, NominalShow, Show, Bindable)

-- ----------------------------------------------------------------------
-- * Example 2: lambda calculus

-- It does not make sense to derive a 'Binable' instance for lambda
-- terms, since lambda terms cannot be used as binders.

data Term = Var Atom | App Term Term | Abs (Bind Atom Term)
  deriving (Generic, Nominal, NominalSupport, NominalShow, Show)
