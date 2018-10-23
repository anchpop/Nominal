{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}

-- | This module provides the 'NominalShow' type class, which is an
-- extension of 'Show' with support for renaming of bound variables.
-- We also provide generic programming so that instances of
-- 'NominalShow' can be automatically derived in most cases.

module Nominal.NominalShow where

import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import GHC.Generics

import Nominal.Atom
import Nominal.Nominal
import Nominal.NominalSupport
import Nominal.Bindable
import Nominal.Atomic

-- ----------------------------------------------------------------------
-- * Display of nominal values

-- | 'NominalShow' is similar to 'Show', but with support for renaming
-- of bound variables. With the exception of function types, most
-- 'Nominal' types are also 'NominalShow'. In most cases, instances of
-- 'NominalShow' can be automatically derived.

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
  -- Please note: in defining 'showsPrecSup', neither 'show'
  -- nor 'nominal_show' should be used for the recursive cases, or
  -- else the benefit of fast printing will be lost.
  showsPrecSup :: Support -> Int -> t -> ShowS

  -- | The method 'nominal_showList' is provided to allow the programmer to
  -- give a specialised way of showing lists of values, similarly to
  -- 'showList'. Mostly this is used in the 'NominalShow' instance of
  -- the 'Char' type, so that strings are shown in double quotes,
  -- rather than as character lists.
  nominal_showList :: Support -> [t] -> ShowS
  nominal_showList sup ts = showString $
    "["
    ++ intercalate "," [ showsPrecSup sup 0 t "" | t <- ts ]
    ++ "]"

  default showsPrecSup :: (Generic t, GNominalShow (Rep t)) => Support -> Int -> t -> ShowS
  showsPrecSup sup d x = gshowsPrecSup Pre sup d (from x)

-- | Like 'show', but for nominal types.  Usually all instances of
-- 'NominalShow' are also instances of 'Show', so 'show' can also be
-- used.
nominal_show :: (NominalShow t) => t -> String
nominal_show t = showsPrecSup (support t) 0 t ""

-- | This function should be used in the definition of 'Show'
-- instances for nominal types, like this:
--
-- > instance Show MyType where
-- >   showsPrec = nominal_showsPrec
nominal_showsPrec :: (NominalShow t) => Int -> t -> ShowS
nominal_showsPrec d t = showsPrecSup (support t) d t

-- ----------------------------------------------------------------------
-- * NominalShow instances

-- | A helper function for defining 'NominalShow' instances
-- for /non-nominal types only/. It can be used like this:
--
-- > instance NominalShow MyType where
-- >   showsPrecSup = base_showsPrecSup
base_showsPrecSup :: (Show t) => Support -> Int -> t -> ShowS
base_showsPrecSup dup d x = showString (show x)

-- Base cases

instance NominalShow Atom where
  showsPrecSup sup d t = showString (atomic_show t)

instance NominalShow Bool where
  showsPrecSup = base_showsPrecSup

instance NominalShow Integer where
  showsPrecSup = base_showsPrecSup

instance NominalShow Int where
  showsPrecSup = base_showsPrecSup

instance NominalShow Char where
  showsPrecSup = base_showsPrecSup
  nominal_showList sup ts = shows ts

instance NominalShow Double where
  showsPrecSup = base_showsPrecSup

instance NominalShow Float where
  showsPrecSup = base_showsPrecSup

instance (Show t) => NominalShow (Basic t) where
  showsPrecSup = base_showsPrecSup

instance NominalShow Literal where
  showsPrecSup = base_showsPrecSup

-- Generic instances

instance NominalShow ()
instance (NominalShow t, NominalShow s) => NominalShow (t,s)
instance (NominalShow t, NominalShow s, NominalShow r) => NominalShow (t,s,r)
instance (NominalShow t, NominalShow s, NominalShow r, NominalShow q) => NominalShow (t,s,r,q)
instance (NominalShow t, NominalShow s, NominalShow r, NominalShow q, NominalShow p) => NominalShow (t,s,r,q,p)
instance (NominalShow t, NominalShow s, NominalShow r, NominalShow q, NominalShow p, NominalShow o) => NominalShow (t,s,r,q,p,o)
instance (NominalShow t, NominalShow s, NominalShow r, NominalShow q, NominalShow p, NominalShow o, NominalShow n) => NominalShow (t,s,r,q,p,o,n)

-- Special instances

instance (NominalShow t) => NominalShow [t] where
  showsPrecSup sup d ts = nominal_showList sup ts

instance (NominalShow t) => NominalShow (Defer t) where
  showsPrecSup sup d t = showsPrecSup sup d (force t)

instance (AtomKind a) => NominalShow (AtomOfKind a) where
  showsPrecSup sup d t = showString (atomic_show t)

instance (Bindable a, NominalShow a, NominalShow t) => NominalShow (Bind a t) where
  showsPrecSup sup d t =
    open_for_printing sup t $ \a s sup' ->
      showParen (d > 5) $
        showString (nominal_show a ++ " . " ++ showsPrecSup sup' 5 s "")

instance (Ord k, NominalShow k, NominalShow v) => NominalShow (Map k v) where
  showsPrecSup sup d m =
    showParen (d > 10) $
      showString "fromList " ∘ showsPrecSup sup 11 (Map.toList m)

instance (Ord k, NominalShow k) => NominalShow (Set k) where
  showsPrecSup sup d s =
    showParen (d > 10) $
      showString "fromList " ∘ showsPrecSup sup 11 (Set.toList s)

instance (Bindable a, NominalShow a, NominalShow t) => Show (Bind a t) where
  showsPrec = nominal_showsPrec

-- ----------------------------------------------------------------------
-- * Generic programming for NominalShow

-- | This type keeps track of which separator to use for the next tuple.
data Separator = Rec | Tup | Inf String | Pre

-- | A version of the 'NominalShow' class suitable for generic
-- programming. The implementation uses ideas from
-- "Generics.Deriving.Show".
class GNominalShow f where
  gshowsPrecSup :: Separator -> Support -> Int -> f a -> ShowS
  isNullary :: f a -> Bool
  isNullary x = False

instance GNominalShow V1 where
  -- Does not occur, because V1 is an empty type.
  gshowsPrecSup sep sup d t s = undefined 
  
instance GNominalShow U1 where
  gshowsPrecSup sep sup d t s = s
  isNullary x = True

instance (GNominalShow a, GNominalShow b) => GNominalShow (a :*: b) where
  gshowsPrecSup sep sup d (x :*: y) = 
    gshowsPrecSup sep sup prec x
    ∘ showString separator
    ∘ gshowsPrecSup sep sup prec y
    where
      (separator, prec) = case sep of
        Rec -> (", ", d)
        Tup -> (",", d)
        Inf s -> (" " ++ s ++ " ", d)
        Pre -> (" ", 11)

instance (GNominalShow a, GNominalShow b) => GNominalShow (a :+: b) where
  gshowsPrecSup sep sup d (L1 x) = gshowsPrecSup sep sup d x
  gshowsPrecSup sep sup d (R1 x) = gshowsPrecSup sep sup d x

instance (GNominalShow a) => GNominalShow (M1 D c a) where
  gshowsPrecSup sep sup d (M1 x) = gshowsPrecSup sep sup d x

instance (GNominalShow a, Constructor c) => GNominalShow (M1 C c a) where
  gshowsPrecSup sep sup d c@(M1 x) =
    case fixity of
      Prefix
        | isNullary x -> showString name
        | isTuple name -> showParen True $ gshowsPrecSup Tup sup 0 x
        | conIsRecord c -> showParen (d > 10) $
          showString name
          ∘ showString " "
          ∘ showString "{"
          ∘ gshowsPrecSup Rec sup 0 x
          ∘ showString "}"
        | otherwise -> showParen (d > 10) $
        showString name
        ∘ showString " "
        ∘ gshowsPrecSup Pre sup 11 x
      Infix assoc prec -> showParen (d > prec) $
        gshowsPrecSup (Inf name) sup (prec+1) x
    where
      name = conName c
      fixity = conFixity c
      isTuple ('(' : ',' : _) = True
      isTuple _ = False

instance (GNominalShow a, Selector c) => GNominalShow (M1 S c a) where
  gshowsPrecSup sep sup d s@(M1 x)
    | null name = gshowsPrecSup sep sup d x
    | otherwise =
      showString name
      ∘ showString " = "
      ∘ gshowsPrecSup sep sup d x
    where
      name = selName s

instance (NominalShow a) => GNominalShow (K1 i a) where
  gshowsPrecSup sep sup d (K1 x) = showsPrecSup sup d x
