{-# OPTIONS_GHC -fno-cse -fno-full-laziness #-}

-- | This model provides three primitive functions that use
-- 'unsafePerformIO'. These functions are only safe if used correctly.

module Nominal.Unsafe where

import Data.IORef
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Unique
import System.IO.Unsafe (unsafePerformIO)

import Nominal.ConcreteNames

-- | A global variable holding a set of strings already used for free
-- names.
-- 
-- The use of 'unsafePerformIO' in this function is safe, because it
-- is only called once and serves to create a global reference cell.
{-# NOINLINE global_used #-}
global_used :: IORef (Set String)
global_used = unsafePerformIO $ do
  newIORef Set.empty

-- | Create a globally new concrete name based on the given name
-- suggestion.
-- 
-- The use of 'unsafePerformIO' in this function is safe only if the
-- user respects the correctness condition (see 'with_fresh' and other
-- analogous functions). In that case, globally fresh names will never
-- be generated, the globally new names are never used, and
-- referential transparency holds.
--
-- However, the mechanism provided by 'global_new' a useful
-- convenience, for example for the generation of error messages from
-- inside a function body where fresh names are in scope.
{-# NOINLINE global_new #-}
global_new :: NameSuggestion -> String
global_new ns = unsafePerformIO $ do
  used <- readIORef global_used
  let n = rename_fresh used ns
  writeIORef global_used (Set.insert n used)
  return n

-- | Perform a subcomputation in the presence of a globally unique
-- value. This is similar to 'newUnique', but uses a continuation
-- monad instead of the 'IO' monad. To ensure referential
-- transparency, the unique value must not escape the function body.
--
-- The use of 'unsafePerformIO' in this function is only safe if the
-- user respects the correctness condition (see 'with_fresh' and other
-- analogous functions).
{-# NOINLINE with_unique #-}
with_unique :: (Unique -> a) -> a
with_unique body = unsafePerformIO $ do
  x <- newUnique
  return (body x)

