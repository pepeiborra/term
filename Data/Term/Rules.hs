{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, UndecidableInstances, TypeSynonymInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE CPP #-}

{-| This module works with and abstract notion of rule.

    A rule is a set of terms (generally a pair) which must
    be treated as a whole. Concrete examples include
    term rewriting rules and prolog clauses.

    To do this the module provides
    generalizations of the unify, match, equiv, fresh and vars
    operations which work with sets of terms.
-}
module Data.Term.Rules
  (GetVars(..),
   GetUnifier(..), unifies', equiv',
   GetMatcher(..), matches',
   GetFresh(..), getFresh
  ) where

import Control.Monad
import Control.Monad.Trans
import Control.Monad.Free
#ifdef TRANSFORMERS
import Control.Monad.Trans.State (evalState, execStateT, evalStateT)
#else
import Control.Monad.State (evalState, execStateT, evalStateT)
#endif
import Data.Foldable (Foldable, foldMap, toList)
import Data.Maybe
import Data.Monoid
import qualified Data.Set as Set
import Data.Term
import Data.Term.Var
import Data.Term.IOVar
import Data.Traversable (Traversable)
import qualified Data.Traversable as T

-- -----------
-- * Variables
-- -----------
class Ord var => GetVars var t | t -> var where getVars :: t -> [var]
instance (Functor termF, Foldable termF, Ord var) => GetVars var (Free termF var) where getVars = snub . toList
instance (GetVars var t, Foldable f) => GetVars var (f t) where getVars = snub . foldMap getVars
--instance (GetVars t var, Foldable f, Foldable g) => GetVars (g(f t)) var where getVars = (foldMap.foldMap) getVars

instance GetVars Var Var where getVars v = [v]
instance GetVars (IOVar t) (IOVar t) where getVars v = [v]

-- ------------------------------------------
-- * GetFresh: Variants
-- ------------------------------------------

class (Traversable termF) => GetFresh (termF :: * -> *) var thing | thing -> termF var where
    getFresh' :: (MonadTrans t, MonadFresh var m, MonadEnv termF var (t m)) => thing -> t m thing
instance (Traversable termF) => GetFresh termF var (Free termF var) where
    getFresh' t = fresh t
instance (Traversable termF, GetFresh termF var t, Traversable f) => GetFresh termF var (f t) where
    getFresh' t = T.mapM getFresh' t

getFresh :: forall t v m thing. (Ord v, MonadFresh v m, GetFresh t v thing) => thing -> m thing
getFresh t = evalStateT (getFresh' t) (mempty :: Substitution t v)

-- -------------
-- * Unification
-- -------------
unifies' :: forall termF v t. (Ord v, GetUnifier termF v t) => t -> t -> Bool
unifies' s t = isJust (evalStateT (getUnifier s t) (mempty :: Substitution termF v))

class Functor termF => GetUnifier termF var t | t -> termF var
    where getUnifier :: MonadEnv termF var m => t -> t -> m ()

instance (Eq var, Unify f) => GetUnifier f var (Free f var) where
  getUnifier t u = unify t u
instance (GetUnifier termF var t, Eq (f ()), Functor f, Foldable f) => GetUnifier termF var (f t) where
  getUnifier t u | fmap (const ()) t == fmap (const ()) u = zipWithM_ getUnifier (toList t) (toList u)
                 | otherwise = fail "structure mismatch"

-- ------------
-- * Matching
-- ------------
matches' :: forall termF v t. (Ord v, GetMatcher termF v t) => t -> t -> Bool
matches' s t = isJust (evalStateT (getMatcher s t) (mempty :: Substitution termF v))

class Functor termF =>  GetMatcher termF var t | t -> termF var
    where getMatcher :: MonadEnv termF var m => t -> t -> m ()

instance (Eq var, Match f) => GetMatcher f var (Free f var) where
  getMatcher t u = match t u
instance (GetMatcher termF var t, Eq (f ()), Functor f, Foldable f) => GetMatcher termF var (f t) where
  getMatcher t u | fmap (const ()) t == fmap (const ()) u = zipWithM_ getMatcher (toList t) (toList u)
                 | otherwise = fail "structure mismatch"

-- ----------------------------
-- * Equivalence up to renaming
-- ----------------------------

equiv' :: forall termF var t.
         (Ord var, Enum var, Ord (termF (Free termF var)),
         GetUnifier termF var t, GetVars var t, GetFresh termF var t) => t -> t -> Bool
equiv' t u = case execStateT (getUnifier t' u) mempty of
              Just x -> isRenaming x
              _   -> False
 where
     t' = getFresh t `evalStateT` (mempty :: Substitution termF var) `evalState` freshVars
     freshVars = [toEnum i ..]
     i = maximum (0 : map fromEnum (getVars t)) + 1

-- -----------
-- Combinators
-- -----------
snub = Set.toList . Set.fromList