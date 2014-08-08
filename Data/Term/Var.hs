{-# LANGUAGE TypeFamilies #-}
module Data.Term.Var where

import Control.Monad.Free
import Control.Monad.Variant (Rename(..))
import Data.Term.Base
import Data.Term.Substitutions
import qualified Data.Var.Family as Family
import qualified Data.Set as Set

data Var = VName String | VAuto Int deriving (Eq, Ord, Show)

instance Enum Var where
    fromEnum (VAuto i) = i
    fromEnum (VName _) = 0
    toEnum = VAuto

var :: Functor f =>  String -> Free f Var
var  = return . VName

var' :: Functor f => Int -> Free f Var
var' = return . VAuto

instance Rename Var where rename _ = id


type instance Family.Var Var = Var
instance GetVars Var where
  getVars = Set.singleton
