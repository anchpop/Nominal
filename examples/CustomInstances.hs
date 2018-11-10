{-# LANGUAGE ApplicativeDo #-}

-- | This file illustrates how to write manual instances for
-- 'Nominal', 'NominalSupport', 'NominalShow', and 'Bindable'.
--
-- Note: this is usually unnecessary, as these instances can be
-- derived. See "GenericInstances" for how to derive these instances
-- automatically.

module CustomInstances where

import Nominal
import Prelude hiding ((.))

-- ----------------------------------------------------------------------
-- * Example 1: MyTree

data MyTree a = Leaf | Branch a (MyTree a) (MyTree a)

instance (Nominal a) => Nominal (MyTree a) where
  π • Leaf = Leaf
  π • (Branch a l r) = Branch (π • a) (π • l) (π • r)

instance (NominalSupport a) => NominalSupport (MyTree a) where
  support Leaf = support ()
  support (Branch a l r) = support (a, l, r)

instance (NominalShow a) => NominalShow (MyTree a) where
  showsPrecSup sup d Leaf = showString "Leaf"
  showsPrecSup sup d (Branch a l r) =
    showParen (d > 10) $
      showString "Branch "
      ∘ showsPrecSup sup 11 a
      ∘ showString " "
      ∘ showsPrecSup sup 11 l
      ∘ showString " "
      ∘ showsPrecSup sup 11 r 

instance (Bindable a) => Bindable (MyTree a) where
  binding Leaf = do
    pure Leaf
  binding (Branch a l r) = do
    a' <- binding a
    l' <- binding l
    r' <- binding r
    pure (Branch a' l' r')

-- ----------------------------------------------------------------------
-- * Example 2: lambda calculus

data Term = Var Atom | App Term Term | Abs (Bind Atom Term)

instance Nominal Term where
  π • Var x = Var (π • x)
  π • App m n = App (π • m) (π • n)
  π • Abs body = Abs (π • body)

instance NominalSupport Term where
  support (Var x) = support x
  support (App m n) = support (m, n)
  support (Abs body) = support body

instance NominalShow Term where
  showsPrecSup sup d (Var x) =
    showParen (d > 10) $
      showString "Var "
      ∘ showsPrecSup sup 11 x
  showsPrecSup sup d (App m n) =       
    showParen (d > 10) $
      showString "App "
      ∘ showsPrecSup sup 11 m
      ∘ showString " "
      ∘ showsPrecSup sup 11 n
  showsPrecSup sup d (Abs body) =
    open_for_printing sup body $ \x m sup ->
      showParen (d > 10) $
        showString "Abs ("
        ∘ showsPrecSup sup 6 x
        ∘ showString " . "
        ∘ showsPrecSup sup 5 m
        ∘ showString ")"

instance Show Term where
  showsPrec = nominal_showsPrec

-- It does not make sense to define a 'Binable' instance for lambda
-- terms, since lambda terms cannot be used as binders.

-- ----------------------------------------------------------------------
-- * Example 3: basic types

-- $ A type is /basic/ or /non-nominal/ if its elements cannot contain
-- atoms.

data MyBaseType = MyString String | MyInt Int
  deriving (Show)

instance Nominal MyBaseType where
  (•) = basic_action

instance NominalSupport MyBaseType where
  support = basic_support

instance NominalShow MyBaseType where
  showsPrecSup = basic_showsPrecSup

instance Bindable MyBaseType where
  binding = basic_binding
  


