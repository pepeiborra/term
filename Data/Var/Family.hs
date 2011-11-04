{-# LANGUAGE TypeFamilies #-}
module Data.Var.Family where

import Data.Set (Set)
import Data.Map (Map)

type family VarM (m :: * -> *) :: *
type family Var  t :: *

type instance Var  [t] = Var t
type instance Var (Set t) = Var t
type instance Var (Map k t) = Var t