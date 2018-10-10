-- | This module provides a way to generate infinitely many distinct
-- concrete variable names from a list of name suggestions.
--
-- Since bound atoms must sometimes be renamed, we need a way to
-- generate suitable concrete names.  This should be configurable on a
-- per-atom basis, with a fallback default behavior for each atom
-- type.
--
-- A name suggestion is essentially a list of possible names. The
-- first useable name from the list is chosen. If the list is finite
-- and contains no useable names, then we will generate more names by
-- appending numerical subscripts. A client can override this default
-- behavior by specifying an infinite list of name suggestions.
--
-- An empty list of name suggestions counts as no suggestion, in which
-- case a default will be used.
--
-- When merging two atoms (see 'Nominal.merge'), we concatenate their
-- name suggestions. In particular, if one name has a user-specified
-- suggestion and the other one does not, we always use the
-- user-specified one.

module Nominal.ConcreteNames where

import Data.Char
import Data.List
import Data.Set (Set)
import qualified Data.Set as Set

-- | A name suggestion is a list of possible names. 
type NameSuggestion = [String]

-- | The names to use if nothing else was specified.
default_names :: NameSuggestion
default_names = ["x", "y", "z", "u", "v", "w", "r", "s", "t", "p", "q"]

-- | Convert a digit to a subscript.
to_subscript :: Char -> Char
to_subscript '0' = '₀'
to_subscript '1' = '₁'
to_subscript '2' = '₂'
to_subscript '3' = '₃'
to_subscript '4' = '₄'
to_subscript '5' = '₅'
to_subscript '6' = '₆'
to_subscript '7' = '₇'
to_subscript '8' = '₈'
to_subscript '9' = '₉'
to_subscript c = c

-- | Check if a character is a letter or underscore.
isAlphaOrWild :: Char -> Bool
isAlphaOrWild c = isAlpha c || c == '_'

-- | An infinite list of strings, based on the suggested names.
varnames :: NameSuggestion -> [String]
varnames xs0 = xs1 ++ xs3 ++ [ x ++ map to_subscript (show n) | n <- [1..], x <- xs3 ]
  where
    xs1 = [ x | x <- xs0, x /= "" ]
    xs2 = [ y | x <- xs0, let y = takeWhile isAlphaOrWild x, y /= "" ]
    xs3 = if xs2 == [] then default_names else xs2

-- | Compute a string that is not in the given set, and whose name is
-- based on the supplied suggestions.
rename_fresh :: Set String -> NameSuggestion -> String
rename_fresh as ns = n'
  where
    n' = head [ x | x <- varnames ns, not (used x) ]
    used x = x `Set.member` as

-- | Merge two name suggestions. Essentially this appends them, but we
-- try to avoid duplication.
combine_names :: NameSuggestion -> NameSuggestion -> NameSuggestion
combine_names xs ys = xs ++ (ys \\ xs)

