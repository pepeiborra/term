{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, UndecidableInstances, TypeSynonymInstances #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE CPP #-}

{-| This module works with an abstract notion of rule.

    A rule is a set of terms (generally a pair) which must
    be treated as a whole. Concrete examples include
    term rewriting rules and prolog clauses.

    To do this the module provides
    generalizations of the unify, match, equiv, fresh and vars
    operations which work with sets of terms.
-}
module Data.Term.Rules
  (GetVars(..),
   GetUnifier(..), getUnifier, unifies', equiv', getUnifierMdefault,
   GetMatcher(..), getMatcher, matches', getMatcherMdefault,
   GetFresh(..), getFresh, getVariant, getFreshMdefault
  ) where

import Control.Applicative
import Control.Monad.Free
#ifdef TRANSFORMERS
import Control.Monad.Trans.State (evalState, execStateT, evalStateT)
#else
import Control.Monad.State (evalState, execStateT, evalStateT)
#endif
import Data.Foldable (Foldable, foldMap, toList)
import Data.List ((\\))
import Data.Maybe
import Data.Monoid
import Data.Traversable (Traversable)
import qualified Data.Traversable as T

import Data.Term
import Data.Term.Var
import Data.Term.IOVar
import Data.Term.Utils


-- ----------------
-- * Concrete rules
-- ----------------
infix 1 :->
data RuleF a = (:->) {lhs,rhs::a} deriving (Eq, Ord, Show)
instance Functor RuleF where fmap f (l :-> r) = f l :-> f r
instance Foldable RuleF where foldMap f (l :-> r) = f l `mappend` f r
instance Traversable RuleF where traverse f (l :-> r) = (:->) <$> f l <*> f r
instance Traversable t => GetFresh t v (Rule t v) where getFreshM = getFreshMdefault
instance (Eq v, Traversable t, Eq (t())) => GetUnifier t v (Rule t v) where getUnifierM = getUnifierMdefault
instance (Eq v, Traversable t, Eq (t())) => GetMatcher t v (Rule t v) where getMatcherM = getMatcherMdefault

type Rule t v = RuleF (Term t v)

class HasRules t v trs | trs -> t v where rules :: trs -> [Rule t v]
class HasRules t v trs => IsTRS t v trs where tRS :: [Rule t v] -> trs
instance HasRules t v [Rule t v] where rules = id
instance IsTRS    t v [Rule t v] where tRS   = id

swapRule :: RuleF a -> RuleF a
swapRule (l :-> r) = r :-> l

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
    getFreshM :: (MonadFresh var m, MonadEnv termF var m) => thing -> m thing
instance (Traversable termF) => GetFresh termF var (Free termF var) where
    getFreshM t = fresh t
instance (Traversable termF, GetFresh termF var t) => GetFresh termF var [t] where
    getFreshM = getFreshMdefault

getFreshMdefault :: (Traversable t, GetFresh term v a, MonadFresh v m, MonadEnv term v m) => t a -> m (t a)
getFreshMdefault = T.mapM getFreshM

getFresh :: forall t v m thing. (Ord v, MonadFresh v m, GetFresh t v thing) => thing -> m thing
getFresh t = evalStateT (getFreshM t) (mempty :: Substitution t v)

getVariant :: (Enum v, GetFresh termF v t, GetVars v t') => t -> t' -> t
getVariant u t = evalState (getFresh u) ([toEnum 0..] \\ getVars t)

-- -------------
-- * Unification
-- -------------
getUnifier :: (GetUnifier termF var t, Ord var) => t -> t -> Maybe (Substitution termF var)
getUnifier t u = execStateT (getUnifierM t u) mempty

unifies' :: forall termF v t. (Ord v, GetUnifier termF v t) => t -> t -> Bool
unifies' s t = isJust (getUnifier s t)

class Functor termF => GetUnifier termF var t | t -> termF var
    where getUnifierM :: MonadEnv termF var m => t -> t -> m ()

instance (Eq var, Unify f) => GetUnifier f var (Free f var) where
  getUnifierM t u = unifyM t u
instance (GetUnifier termF var t) => GetUnifier termF var [t] where
  getUnifierM = getUnifierMdefault


getUnifierMdefault :: (GetUnifier termF var t, MonadEnv termF var m, Functor f, Foldable f, Eq (f())) =>
                     f t -> f t -> m ()
getUnifierMdefault t u
    | fmap (const ()) t == fmap (const ()) u = zipWithM_ getUnifierM (toList t) (toList u)
    | otherwise = fail "structure mismatch"

-- ------------
-- * Matching
-- ------------
getMatcher :: (GetMatcher termF var t, Ord var) => t -> t -> Maybe (Substitution termF var)
getMatcher t u = execStateT (getMatcherM t u) mempty

matches' :: (Ord v, GetMatcher termF v t) => t -> t -> Bool
matches' s t = isJust (getMatcher s t)

class Functor termF =>  GetMatcher termF var t | t -> termF var
    where getMatcherM :: MonadEnv termF var m => t -> t -> m ()

instance (Eq var, Match f) => GetMatcher f var (Free f var) where
  getMatcherM t u = matchM t u
instance (GetMatcher termF var t) => GetMatcher termF var [t] where
  getMatcherM = getMatcherMdefault

getMatcherMdefault :: (GetMatcher termF var t, MonadEnv termF var m, Functor f, Foldable f, Eq (f())) =>
                     f t -> f t -> m ()
getMatcherMdefault t u
    | fmap (const ()) t == fmap (const ()) u = zipWithM_ getMatcherM (toList t) (toList u)
    | otherwise = fail "structure mismatch"

-- ----------------------------
-- * Equivalence up to renaming
-- ----------------------------

equiv' :: forall termF var t.
         (Ord var, Enum var, Ord (termF (Free termF var)),
         GetUnifier termF var t, GetVars var t, GetFresh termF var t) => t -> t -> Bool
equiv' t u = maybe False isRenaming (getUnifier t' u)
 where
     t' = getFresh t `evalStateT` (mempty :: Substitution termF var) `evalState` freshVars
     freshVars = [toEnum i ..]
     i = maximum (0 : map fromEnum (getVars t)) + 1
