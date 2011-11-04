{-# LANGUAGE TypeFamilies #-}
module Data.Term.Family (
    module Data.Id.Family,
    module Data.Rule.Family,
    module Data.Term.Family,
    module Data.Var.Family
    ) where

import Data.Id.Family
import Data.Rule.Family
import Data.Var.Family
import Data.Set (Set)
import Data.Map (Map)

type family TermFM (m :: * -> *) :: * -> *
type family TermF  t :: * -> *

type instance TermF  [t] = TermF  t
type instance TermF (Set t) = TermF t
type instance TermF (Map k a) = TermF a