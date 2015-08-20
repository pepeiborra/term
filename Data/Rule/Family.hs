{-# LANGUAGE TypeFamilies #-}

module Data.Rule.Family where

import Data.Set (Set)
import Data.Map (Map)

type family Rule (trs :: *) :: *
--type family Rule1 (trs :: *)

type instance Rule (Maybe a) = Rule a
type instance Rule [a] = Rule a
type instance Rule (Set a) = Rule a
type instance Rule (Map k a) = Rule a
