{-# LANGUAGE OverlappingInstances, UndecidableInstances, ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Data.Term (
     Term, subterms, isVar, vars,
     Match(..), Unify(..), matches, unifies, equiv,
     Substitution(..), fromList, restrictTo, liftSubst, lookupSubst, applySubst, zonkSubst,
     MonadEnv(..), mkFind, find',
     fresh
     ) where

import Control.Applicative
import Control.Monad.Free (Free(..), isPure)
import Control.Monad.Free.Zip
import Control.Monad (replicateM)
import Control.Monad.Trans (lift)
import Control.Monad.Trans.State(State, StateT, get, put, execStateT, evalStateT)
import Data.Foldable (Foldable, toList)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (isJust)
import Data.Monoid
import qualified Data.Set as Set
import Data.Traversable as T

import Prelude hiding (mapM)

-- ------
-- Terms
-- ------

type Term termF var = Free termF var

subterms :: Foldable termF => Free termF var -> [Free termF var]
subterms (Impure t) = Impure t : Prelude.concat (subterms <$> toList t)
subterms _ = []

vars :: (Functor termF, Foldable termF) => Free termF var -> [var]
vars = toList

isVar :: Free termF var -> Bool
isVar = isPure

-- -------------
-- Substitutions
-- -------------
-- | Note that the notion of substitution composition is not exactly what
--    Monoid gives here (which is just left biased Map union)
newtype Substitution termF var = Subst {unSubst::Map var (Free termF var)}
  deriving (Monoid)

liftSubst :: (Map v (Free t v) ->  Map v' (Free t' v')) -> Substitution t v -> Substitution t' v'
liftSubst f (Subst e) = Subst (f e)

lookupSubst :: Ord v => v -> Substitution t v -> Maybe (Free t v)
lookupSubst v (Subst m) = Map.lookup v m

applySubst :: (Ord v, Functor t) => Substitution t v -> Free t v -> Free t v
applySubst s = (>>= f) where
    f v = case lookupSubst v s of
            Nothing -> return v
            Just t' -> t'

restrictTo :: Ord var => [var] -> Substitution id var -> Substitution id var
restrictTo vv = liftSubst f where
  f e = Map.intersectionWith const e (Map.fromDistinctAscList (zip vv (repeat undefined)))

fromList :: Ord v => [(v,Free termF v)] -> Substitution termF v
fromList = Subst . Map.fromList

zonk :: (Functor termF, Ord var) => Substitution termF var -> Free termF var -> Free termF var
zonk subst = (>>= f) where
   f v = case lookupSubst v subst of
           Nothing -> return v
           Just t  -> zonk subst t

zonkSubst :: (Functor termF, Ord var) => Substitution termF var -> Substitution termF var
zonkSubst s = liftSubst (Map.map (zonk s)) s

-- -----------
-- Unification
-- -----------
unifies :: forall termF var. (Unify termF, Ord var) => Free termF var -> Free termF var -> Bool
unifies t u = isJust (execStateT (unify t u) (mempty :: Substitution termF var))

class (Traversable termF, Eq (termF ())) => Unify termF
  where unify :: (MonadEnv termF var m, Eq var) => Free termF var -> Free termF var -> m ()

-- Generic instance
instance (Traversable termF, Eq (termF ())) => Unify termF where
  unify t s = do
    t' <- find' t
    s' <- find' s
    unifyOne t' s'
   where
     unifyOne (Pure vt) s@(Pure vs) = if vt /= vs then varBind vt s else return ()
     unifyOne (Pure vt) s           = {- if vt `Set.member` Set.fromList (vars s) then fail "occurs" else-} varBind vt s
     unifyOne t           (Pure vs) = {-if vs `Set.member` Set.fromList (vars t) then fail "occurs" else-} varBind vs t
     unifyOne t         s           = zipFree_ unify t s

-- ---------
-- Matching
-- ---------
matches :: forall termF var. (Match termF, Ord var) => Free termF var-> Free termF var -> Bool
matches t u = isJust (evalStateT (match t u) (mempty :: Substitution termF var))

class (Eq (termF ()), Traversable termF) => Match termF where
    match :: MonadEnv termF var m => Free termF var -> Free termF var -> m ()

instance (Traversable termF, Eq (termF ())) =>  Match termF where
  match t s = do
    t' <- find' t
    s' <- find' s
    matchOne t' s'
    where matchOne (Pure v) (Pure u) | v == u = return ()
          matchOne (Pure v) u = varBind v u
          matchOne t        u = zipFree_ match t u

-- --------------------------
-- Equivalence up to renaming
-- --------------------------

equiv ::  (Ord var, Enum var, Ord (termF (Free termF var)), Unify termF) => Free termF var -> Free termF var -> Bool
equiv t u = case execStateT (evalStateT (fresh u >>= \u' -> (lift $ unify t u')) freshVars) mempty of
              Just x -> isRenaming x
              _   -> False
 where
     freshVars = [toEnum i ..]
     i = maximum (0 : map fromEnum (vars t)) + 1

--    isRenaming :: (Functor termF, Ord var, Ord (termF (Free termF var))) => Substitution termF var -> Bool
     isRenaming (Subst subst) = all isVar (Map.elems subst) && isBijective (Map.mapKeysMonotonic return subst)

--    isBijective :: Ord k => Map.Map k k -> Bool
     isBijective rel = -- cheap hackish bijectivity check.
                    -- Ensure that the relation is injective and its inverse is too.
                    -- The sets of variables must be disjoint too
                    -- Actually there should be no need to check the inverse
                    -- since this is a Haskell Map and hence the domain contains no duplicates
                   Set.size elemsSet == Map.size rel &&
                   (Map.keysSet rel) `Set.intersection` elemsSet == Set.empty
       where
          elemsSet = Set.fromList(Map.elems rel)

-- ------------------------------------
-- Environments: handling substitutions
-- ------------------------------------

class (Ord var, Functor termF, Monad m) => MonadEnv termF var m | m -> termF var where
    varBind :: var -> Free termF var -> m ()
    find    :: var -> m (Free termF var)
    zonkM   :: Free termF var -> m (Free termF var)

mkFind :: MonadEnv termF var m => Substitution termF var -> (var -> m(Free termF var))
mkFind s v = let mb_t = lookupSubst v s in
             case mb_t of
                Just (Pure v') -> mkFind s v'
                Just t         -> varBind v t >> return t
                Nothing        -> return (Pure v)

find' :: MonadEnv termF v m => Free termF v -> m(Free termF v)
find' (Pure t) = find t
find' t        = return t

instance (Monad m, Functor termF, Ord var) => MonadEnv termF var (StateT (Substitution termF var) m) where
  varBind v t = do {e <- get; put (liftSubst (Map.insert v t) e)}
  find t  = get >>= \s -> mkFind s t
  zonkM t = get >>= \s -> return (zonk s t)

-- ------------------------------------------
-- MonadFresh: Variants of terms and clauses
-- ------------------------------------------

class Monad m => MonadFresh var m | m -> var where freshVar :: m var
instance Monad m => MonadFresh v (StateT [v] m)  where freshVar = do { x:xx <- get; put xx; return x}
instance  MonadFresh v (State [v])  where freshVar = do { x:xx <- get; put xx; return x}

fresh ::  (Traversable termF, Ord var, MonadFresh var m) => Free termF var -> m (Free termF var)
fresh t = do
  let vars_t = snub(vars t)
  fresh_v   <- replicateM (length vars_t) freshVar
  let subst  = fromList (vars_t `zip` map return fresh_v)
  return (applySubst subst t)

-- -----------
-- Combinators
-- -----------
snub :: Ord a => [a] -> [a]
snub = Set.toList . Set.fromList
