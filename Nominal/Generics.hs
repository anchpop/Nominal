-- | The sole purpose of this module is to allow us to re-export the
-- 'Generic' class without having to re-export its documentation or
-- the entire "GHC.Generics" module.

module Nominal.Generics (
  Generic
  )
where

import GHC.Generics
