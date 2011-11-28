{-# LANGUAGE TypeFamilies #-}
module Data.Id.Family where

import Data.Set (Set)
import Data.Map (Map)

type family Id a
type family Id1 (f :: * -> *)

type instance Id [a] = Id a
type instance Id (Set a) = Id a
type instance Id (Map k a) = Id a