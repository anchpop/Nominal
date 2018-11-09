{-# OPTIONS_GHC -fno-cse -fno-full-laziness #-}

-- | This module provides three primitive functions that use
-- 'unsafePerformIO'. These functions are only safe if used correctly.
-- How to use each function correctly is specified in its documentation.
--
-- This module exposes implementation details of the Nominal library,
-- and should not normally be imported. Users of the library should
-- only import the top-level module "Nominal".

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
-- is only called once and serves to create a unique global reference
-- cell.
{-# NOINLINE global_used #-}
global_used :: IORef (Set String)
global_used = unsafePerformIO $ do
  newIORef Set.empty

-- | Create a globally new concrete name based on the given name
-- suggestion. This ensures that fresh names have distinct names when
-- they are not bound.
global_new_io :: NameGen -> IO String
global_new_io ng = do
  used <- readIORef global_used
  let n = rename_fresh used ng
  writeIORef global_used (Set.insert n used)
  return n

-- | Create a globally new concrete name based on the given name
-- suggestion.
-- 
-- The use of 'unsafePerformIO' in this function is safe, provided
-- that the user only uses API functions and respects Pitts's
-- freshness condition.
{-# NOINLINE global_new #-}
global_new :: NameGen -> String
global_new ng = unsafePerformIO (global_new_io ng)

-- | Perform a subcomputation in the presence of a globally unique
-- value. This is similar to 'newUnique', but uses a continuation
-- monad instead of the 'IO' monad. To ensure referential
-- transparency, the unique value must not escape the function body.
--
-- The use of 'unsafePerformIO' in this function is safe, provided
-- that the user only uses API functions and respects Pitts's
-- freshness condition.
{-# NOINLINE with_unique #-}
with_unique :: (Unique -> a) -> a
with_unique k = unsafePerformIO $ do
  x <- newUnique
  return (k x)

-- | Unsafely embed the 'IO' monad in a continuation monad.
--
-- The use of 'unsafePerformIO' in this function is safe, provided
-- that the user only uses API functions and respects Pitts's
-- freshness condition.
unsafe_with :: IO a -> (a -> b) -> b
unsafe_with comp k = unsafePerformIO $ do
  a <- comp
  return (k a)
