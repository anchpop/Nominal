{-# OPTIONS_GHC -fno-cse -fno-full-laziness #-}

-- | This module provides three primitive functions that use
-- 'unsafePerformIO'. These functions are only safe if used correctly.
-- How to use each function correctly is specified in its documentation.

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
-- suggestion. This ensures that fresh names have distinct names when
-- they are not bound. (The naming of bound names is handled by a
-- different mechanism). Although technically there should never be
-- any global fresh names, this is still a useful convenience, for
-- example when generating an error message from inside a function
-- body where fresh names are in scope.
-- 
-- The use of 'unsafePerformIO' in this function is safe if the user
-- respects the correctness conditions associated with the function
-- 'with_fresh' and other analogous functions.
{-# NOINLINE global_new #-}
global_new :: NameGen -> String
global_new ng = unsafePerformIO $ do
  used <- readIORef global_used
  let n = rename_fresh used ng
  writeIORef global_used (Set.insert n used)
  return n

-- | Perform a subcomputation in the presence of a globally unique
-- value. This is similar to 'newUnique', but uses a continuation
-- monad instead of the 'IO' monad. To ensure referential
-- transparency, the unique value must not escape the function body.
--
-- The use of 'unsafePerformIO' in this function is safe if the user
-- respects the correctness conditions associated with the function
-- 'with_fresh' and other analogous functions.
{-# NOINLINE with_unique #-}
with_unique :: (Unique -> a) -> a
with_unique body = unsafePerformIO $ do
  x <- newUnique
  return (body x)

