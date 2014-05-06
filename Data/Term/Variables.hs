{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}

module Data.Term.Variables where

import Control.Monad.State
import Control.Monad.Variant (MonadVariant, Rename, runVariant')
import qualified Control.Monad.Variant as MonadVariant
import Data.Foldable
import Data.List
import Data.Monoid
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Term (MonadEnv, Term, TermF, Substitution, evalMEnv, fresh)
import qualified Data.Term as MonadEnv
import Data.Traversable as T
import qualified Data.Term.Var
import Data.Term.IOVar

import Data.Var.Family

class GetVars t where
  getVars :: Ord (Var t) => t -> Set (Var t)

instance (Functor termF, Foldable termF, Ord var) => GetVars (Term termF var) where
   getVars = Set.fromList . toList

-- type instance Var (f t) = Var t
instance GetVars t => GetVars [t] where getVars = foldMap getVars
instance GetVars t => GetVars (Set t) where getVars = foldMap getVars
-- instance (GetVars t var, Foldable f, Foldable g) => GetVars (g(f t)) var where getVars = (foldMap.foldMap) getVars

type instance Var Data.Term.Var.Var = Data.Term.Var.Var
instance GetVars Data.Term.Var.Var where
  getVars = Set.singleton

type instance Var (IOVar t) = IOVar t
instance GetVars (IOVar t) where
  getVars = Set.singleton


class GetFresh thing where
    getFreshM :: (TermF thing ~ TermF m, Var thing ~ Var m, Traversable (TermF thing), MonadEnv m, MonadVariant m) => thing -> m thing

instance (Traversable termF) => GetFresh (Term termF var) where getFreshM = fresh
instance (Ord a, GetFresh a) => GetFresh (Set a)          where getFreshM = liftM Set.fromList . getFreshM . Set.toList
instance GetFresh t => GetFresh [t] where getFreshM = getFreshMdefault

getFreshMdefault :: (Traversable t, GetFresh a, MonadVariant m, MonadEnv m, Var a ~ Var m, term ~ TermF a, term ~ TermF m, Traversable term) => t a -> m (t a)
getFreshMdefault = T.mapM getFreshM

getFresh :: (MonadVariant m, Ord (Var m), GetFresh thing, Traversable (TermF thing), Var thing ~ Var m) =>
            thing -> m thing
getFresh t = evalMEnv (getFreshM t)

getVariant :: (v ~ Var t, v ~ Var t', Ord v, Enum v, Rename v, GetFresh t, GetVars t', Traversable (TermF t)) => t -> t' -> t
getVariant u t = runVariant' ([toEnum 0..] \\ Set.toList (getVars t)) (getFresh u)
