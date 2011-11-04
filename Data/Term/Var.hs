module Data.Term.Var where

import Control.Monad.Free
import Data.Term hiding (Var)

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