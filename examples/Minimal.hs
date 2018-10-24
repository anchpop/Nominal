{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

-- | A minimal example illustrating the "Nominal" library.

import Nominal
import Prelude hiding ((.))

-- | Untyped lambda terms, up to alpha-equivalence.
data Term = Var Atom | App Term Term | Abs (Bind Atom Term)
  deriving (Generic, Nominal)

-- | Capture-avoiding substitution.
subst :: Term -> Atom -> Term -> Term
subst m x (Var y)
  | x == y = m
  | otherwise = Var y
subst m x (App t s) = App (subst m x t) (subst m x s)
subst m x (Abs body) = open body (\y s -> Abs (y . subst m x s))
