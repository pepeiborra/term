module Data.Term.Var where

import Control.Monad.Free

data Var = VName String | VAuto Int deriving (Eq, Ord, Show)

var :: Functor f =>  String -> Free f Var
var  = return . VName

var' :: Functor f => Int -> Free f Var
var' = return . VAuto
