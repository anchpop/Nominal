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
  module GHC.Generics
)
where

import Prelude hiding ((.))
import Data.Map (Map)
import qualified Data.Map as Map
import Data.List
import GHC.Generics

import Nominal.ConcreteNames
import Nominal.Atom
import Nominal.Permutation
import Nominal.Nominal
import Nominal.NominalSupport
import Nominal.Bindable
import Nominal.Atomic

-- ----------------------------------------------------------------------
-- * Display of nominal values


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
instance NominalShow Atom where
  nominal_showsPrecSup sup d t = showString (show_atomic t)

instance NominalShow Literal where
  nominal_showsPrecSup = simple_showsPrecSup

instance NominalShow ()

-- Derived cases.
instance NominalShow Integer where
  nominal_showsPrecSup = simple_showsPrecSup

instance NominalShow Int where
  nominal_showsPrecSup = simple_showsPrecSup

instance NominalShow Char where
  nominal_showsPrecSup = simple_showsPrecSup
  nominal_showList sup ts = shows ts

instance (NominalShow t, NominalShow s) => NominalShow (t,s)
instance (NominalShow t, NominalShow s, NominalShow r) => NominalShow (t,s,r)
instance (NominalShow t, NominalShow s, NominalShow r, NominalShow q) => NominalShow (t,s,r,q)
instance (NominalShow t, NominalShow s, NominalShow r, NominalShow q, NominalShow p) => NominalShow (t,s,r,q,p)
instance (NominalShow t, NominalShow s, NominalShow r, NominalShow q, NominalShow p, NominalShow o) => NominalShow (t,s,r,q,p,o)
instance (NominalShow t, NominalShow s, NominalShow r, NominalShow q, NominalShow p, NominalShow o, NominalShow n) => NominalShow (t,s,r,q,p,o,n)

-- ... and so on for tuples.

instance (NominalShow t) => NominalShow [t] where
  -- Lists require special treatment.
  nominal_showsPrecSup sup d ts = nominal_showList sup ts

instance (Ord k, NominalShow k, NominalShow v) => NominalShow (Map k v) where
  nominal_showsPrecSup sup d m =
    showParen (d > 10) $
      showString "fromList " ∘ nominal_showsPrecSup sup 11 (Map.toList m)

instance (NominalShow t) => NominalShow (Defer t) where
  nominal_showsPrecSup sup d t = nominal_showsPrecSup sup d (force t)

instance (Bindable a, NominalShow a, NominalShow t) => NominalShow (Bind a t) where
  nominal_showsPrecSup sup d t =
    open_for_printing sup t $ \a s sup' ->
      showParen (d > 5) $
        showString (nominal_show a ++ " . " ++ nominal_showsPrecSup sup' 5 s "")

instance (Bindable a, NominalShow a, NominalShow t) => Show (Bind a t) where
  showsPrec = nominal_showsPrec

instance (AtomKind a) => NominalShow (AtomOfKind a) where
  nominal_showsPrecSup sup d t = showString (show_atomic t)

instance (AtomKind a) => Show (AtomOfKind a) where
  show = show_atomic

instance (AtomKind a) => Atomic (AtomOfKind a) where
  to_atom (AtomOfKind a) = a
  from_atom a = AtomOfKind a
  names f = atomofkind_names f

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

instance (Bindable a) => Bindable (AtomPlus a t) where
  data Bind (AtomPlus a t) s = BindAP t (Bind a s)
  bindable_action π (BindAP t body) = BindAP t (π • body)
  bindable_support (BindAP t body) = support body
  bindable_eq (BindAP t1 b1) (BindAP t2 b2) = open b1 $ \a _ -> AtomPlus a t1 == AtomPlus a t2 && b1 == b2
  abst (AtomPlus a t) body = BindAP t (abst a body)
  open (BindAP t body) k = open body $ \a s -> k (AtomPlus a t) s
  open_for_printing sup (BindAP t body) k = open_for_printing sup body $ \a s -> k (AtomPlus a t) s

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
