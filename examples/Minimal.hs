{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

-- | A minimal example illustrating the "Nominal" library.

module Minimal where

import Nominal
import Prelude hiding ((.))

-- | Untyped lambda terms, up to alpha-equivalence.
data Term = Var Atom | App Term Term | Abs (Bind Atom Term)
  deriving (Generic, Nominal)

-- | Capture-avoiding substitution.
subst :: Term -> Atom -> Term -> Term
subst m z (Var x)
  | x == z    = m
  | otherwise = Var x
subst m z (App t s) = App (subst m z t) (subst m z s)
subst m z (Abs (x :. t)) = Abs (x . subst m z t)
  
