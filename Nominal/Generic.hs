-- | The sole purpose of this module is to allow us to re-export the
-- 'Generic' class without having to re-export its documentation or
-- the entire "GHC.Generics" module.
--
-- This module exposes implementation details of the Nominal library,
-- and should not normally be imported. Users of the library should
-- only import the top-level module "Nominal".

module Nominal.Generic (
  Generic
  )
where

import GHC.Generics
