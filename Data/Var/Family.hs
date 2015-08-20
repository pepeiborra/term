{-# LANGUAGE TypeFamilies,PolyKinds #-}
module Data.Var.Family where

import Data.Set (Set)
import Data.Map (Map)

type family Var  (t :: k)

type instance Var (Maybe a) = Var a
type instance Var  [t] = Var t
type instance Var (Set t) = Var t
type instance Var (Map k t) = Var t
