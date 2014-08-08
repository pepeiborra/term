{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}

module Data.Term.Variables where

import Control.Monad.Env
import Control.Monad.State
import Control.Monad.Variant (MonadVariant, Rename, runVariant')
import qualified Control.Monad.Variant as MonadVariant
import Data.Foldable
import Data.List
import Data.Monoid
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Term.Base
import Data.Traversable as T

import Data.Term.MEnv
import Data.Term.Family
import Data.Var.Family
