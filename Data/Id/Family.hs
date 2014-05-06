{-# LANGUAGE TypeFamilies, PolyKinds #-}
module Data.Id.Family where

import Data.Set (Set)
import Data.Map (Map)

type family Id (f :: k)

type instance Id [a] = Id a
type instance Id (Set a) = Id a
type instance Id (Map k a) = Id a
