{-# LANGUAGE OverlappingInstances, UndecidableInstances, ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE CPP #-}

module Data.Term (
     Term, subterms, positions, isVar, vars, someSubterm,
     Position, (!), updateAt, updateAt',
     Match(..), Unify(..), unify, match, matches, unifies, equiv,
     Substitution(..), fromList, restrictTo, liftSubst, lookupSubst, applySubst, zonkTerm, zonkTermM, zonkSubst, isEmpty, isRenaming,
     MonadEnv(..), find',
     MonadFresh(..), fresh, fresh', variant
     ) where

import Control.Applicative
import Control.Monad.Free (Free(..), foldFree, evalFree, isPure)
import Control.Monad.Free.Zip
import Control.Monad (liftM, join, MonadPlus(..), msum)
import Control.Monad.Trans (lift)
#ifdef TRANSFORMERS
import Control.Monad.Trans.State(State, StateT(..), get, put, evalState, evalStateT, execStateT)
import Control.Monad.Trans.List(ListT)
import Control.Monad.Trans.Reader(ReaderT)
import Control.Monad.Trans.RWS(RWST)
import Control.Monad.Trans.Writer(WriterT)
#else
import Control.Monad.State(State, StateT(..), get, put, evalState, evalStateT, execStateT)
import Control.Monad.List(ListT)
import Control.Monad.Reader(ReaderT)
import Control.Monad.RWS(RWST)
import Control.Monad.Writer(WriterT)
#endif
import Data.Foldable (Foldable, toList)
import Data.List ((\\))
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (isJust)
import Data.Monoid
import qualified Data.Set as Set
import Data.Traversable as T

import Data.Term.Utils
import Prelude as P hiding (mapM)

-- ------
-- Terms
-- ------

type Term termF var = Free termF var

subterms :: Foldable termF => Term termF var -> [Term termF var]
subterms (Impure t) = Impure t : P.concat (subterms <$> toList t)
subterms _ = []

vars :: (Functor termF, Foldable termF) => Term termF var -> [var]
vars = toList

isVar :: Term termF var -> Bool
isVar = isPure

-- ----------
-- Positions
-- ----------
type Position = [Int]

positions :: (Functor f, Foldable f) => Term f v -> [Position]
positions = foldFree (const []) f where
    f x = [] : concat (zipWith (\i pp -> map (i:) pp) [1..] (toList x))

(!) :: Foldable f => Term f v -> Position -> Term f v
Impure t ! (i:ii) = (toList t !! (i-1)) ! ii
t        ! []     = t
_        ! _      = error "(!): invalid position"

-- | Updates the subterm at the position given
--   A failure to reach the position given results in a runtime error
updateAt  :: (Traversable f) =>  Position -> Term f v -> (Term f v -> Term f v) -> Term f v
updateAt (0:_)  _          _ = error "updateAt: 0 is not a position!"
updateAt []     t          f = f t
updateAt (i:ii) (Impure t) f = Impure (unsafeZipWithG g [1..] t)
                               where g j st = if i==j then updateAt ii st f else st
updateAt _      _          _ = error "updateAt: invalid position given"


-- | Updates the subterm at the position given,
--   returning a tuple with the new term and the previous contents at that position.
--   Failure is contained inside the monad
updateAt'  :: (Traversable f, Monad m) =>
              Position -> Term f v -> (Term f v -> Term f v) -> m (Term f v, Term f v)
updateAt' pos t f = runStateT (go pos t) t where
 go (0:_)  _          = fail "updateAt: 0 is not a position!"
 go []     t          = put t >> return (f t)
 go (i:ii) (Impure t) = Impure `liftM` unsafeZipWithGM g [1..] t
                               where g j st = if i==j then go ii st else return st
 go _      _          = fail "updateAt: invalid position given"

-- -----
-- * Ids
-- -----
class Functor f => HasId f id | f -> id where getId :: f a -> Maybe id
class MapId f where mapId :: (id -> id') -> f id a -> f id' a

rootSymbol :: HasId f id => Term f v -> Maybe id
rootSymbol (Impure t) = getId t
rootSymbol _          = Nothing

-- -------------
-- Substitutions
-- -------------
-- | Note that the notion of substitution composition is not exactly what
--    Monoid gives here (which is just left biased Map union)
newtype Substitution termF var = Subst {unSubst::Map var (Term termF var)}
  deriving (Monoid)

liftSubst :: (Map v (Term t v) ->  Map v' (Term t' v')) -> Substitution t v -> Substitution t' v'
liftSubst f (Subst e) = Subst (f e)

lookupSubst :: Ord v => v -> Substitution t v -> Maybe (Term t v)
lookupSubst v (Subst m) = Map.lookup v m

applySubst :: (Ord v, Functor t) => Substitution t v -> Term t v -> Term t v
applySubst s = (>>= f) where
    f v = case lookupSubst v s of
            Nothing -> return v
            Just t' -> t'

restrictTo :: Ord var => [var] -> Substitution id var -> Substitution id var
restrictTo vv = liftSubst f where
  f e = Map.intersectionWith const e (Map.fromDistinctAscList (zip vv (repeat undefined)))

isEmpty :: Substitution id v -> Bool
isEmpty (Subst m) = Map.null m

fromList :: Ord v => [(v,Term termF v)] -> Substitution termF v
fromList = Subst . Map.fromList

zonkTerm :: (Functor termF, Ord var) => Substitution termF var -> (var -> var') -> Term termF var -> Term termF var'
zonkTerm subst fv = (>>= f) where
   f v = case lookupSubst v subst of
           Nothing -> return (fv v)
           Just t  -> zonkTerm subst fv t

zonkTermM :: (Traversable termF, Ord var, Monad m) =>
             Substitution termF var -> (var -> m var') -> Term termF var -> m(Term termF var')
zonkTermM subst fv = liftM join . mapM f where
   f v = case lookupSubst v subst of
           Nothing -> Pure `liftM` fv v
           Just t  -> zonkTermM subst fv t

zonkSubst :: (Functor termF, Ord var) => Substitution termF var -> Substitution termF var
zonkSubst s = liftSubst (Map.map (zonkTerm s id)) s

isRenaming :: (Functor termF, Ord var, Ord (termF (Term termF var))) => Substitution termF var -> Bool
isRenaming (Subst subst) = all isVar (Map.elems subst) && isBijective (Map.mapKeysMonotonic return subst)
  where
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

-- | Only 1st level subterms
someSubterm :: (Traversable f, MonadPlus m) => (Term f a -> m(Term f a)) -> Term f a -> m (Term f a)
someSubterm f  = evalFree (return.return) (msum . liftM2 Impure . interleaveM f)
-- -----------
-- Unification
-- -----------
unifies :: forall termF var. (Unify termF, Ord var) => Term termF var -> Term termF var -> Bool
unifies t u = isJust (unify t u)

unify :: (Unify termF, Ord var) => Term termF var -> Term termF var -> Maybe (Substitution termF var)
unify t u = execStateT (unifyM t u) mempty

class (Traversable termF, Eq (termF ())) => Unify termF
  where unifyM :: (MonadEnv termF var m, Eq var) => Term termF var -> Term termF var -> m ()

-- Generic instance
instance (Traversable termF, Eq (termF ())) => Unify termF where
  unifyM t s = do
    t' <- find' t
    s' <- find' s
    unifyOne t' s'
   where
     unifyOne (Pure vt) s@(Pure vs) = if vt /= vs then varBind vt s else return ()
     unifyOne (Pure vt) s           = {- if vt `Set.member` Set.fromList (vars s) then fail "occurs" else-} varBind vt s
     unifyOne t           (Pure vs) = {-if vs `Set.member` Set.fromList (vars t) then fail "occurs" else-} varBind vs t
     unifyOne t         s           = zipFree_ unifyM t s

-- ---------
-- Matching
-- ---------
matches :: forall termF var. (Match termF, Ord var) => Term termF var -> Term termF var -> Bool
matches t u = isJust (match t u)

match :: (Match termF, Ord var) => Term termF var -> Term termF var -> Maybe (Substitution termF var)
match t u = execStateT (matchM t u) mempty

class (Eq (termF ()), Traversable termF) => Match termF where
    matchM :: (Eq var, MonadEnv termF var m) => Term termF var -> Term termF var -> m ()

instance (Traversable termF, Eq (termF ())) =>  Match termF where
  matchM t s = do
    t' <- find' t
    s' <- find' s
    matchOne t' s'
    where matchOne (Pure v) (Pure u) | v == u = return ()
          matchOne (Pure v) u = varBind v u
          matchOne t        u = zipFree_ matchM t u

-- --------------------------
-- Equivalence up to renaming
-- --------------------------

equiv :: forall termF var.
         (Ord var, Enum var, Ord (termF (Term termF var)), Unify termF) => Term termF var -> Term termF var -> Bool
equiv t u = maybe False isRenaming (unify t' u)
 where
     t' = fresh t `evalStateT` (mempty :: Substitution termF var) `evalState` freshVars
     freshVars = [toEnum i ..]
     i = maximum (0 : map fromEnum (vars t)) + 1

-- ------------------------------------
-- Environments: handling substitutions
-- ------------------------------------
-- | Instances need only to define 'varBind' and 'lookupVar'
class (Functor termF, Monad m) => MonadEnv termF var m | m -> termF var where
    varBind   :: var -> Term termF var -> m ()
    lookupVar :: var -> m (Maybe (Term termF var))

    find      :: var -> m(Term termF var)
    find v = do
      mb_t <- lookupVar v
      case mb_t of
        Just (Pure v') -> find v'
        Just t         -> varBind v t >> return t
        Nothing        -> return (Pure v)

    zonkM :: (Traversable termF) => (var -> m var') -> Term termF var -> m(Term termF var')
    zonkM fv = liftM join . mapM f where
        f v = do mb_t <- lookupVar v
                 case mb_t of
                   Nothing -> Pure `liftM` fv v
                   Just t  -> zonkM fv t


find' :: MonadEnv termF v m => Term termF v -> m(Term termF v)
find' (Pure t) = find t
find' t        = return t

instance (Monad m, Functor t, Ord v) => MonadEnv t v (StateT (Substitution t v) m) where
  varBind v t = do {e <- get; put (liftSubst (Map.insert v t) e)}
  lookupVar t  = get >>= \s -> return(lookupSubst t s)

instance (Monad m, Functor t, Ord v) => MonadEnv t v (StateT (Substitution t v, a) m) where
  varBind v t = withFst (varBind v t)
  lookupVar t = withFst (lookupVar t)

#ifndef TRANSFORMERS
instance (Functor t, Ord v) => MonadEnv t v (State (Substitution t v)) where
  varBind v t = do {e <- get; put (liftSubst (Map.insert v t) e)}
  lookupVar t  = get >>= \s -> return(lookupSubst t s)

instance (Functor t, Ord v) => MonadEnv t v (State (Substitution t v, a)) where
  varBind v t = do {(e,a) <- get; put (liftSubst (Map.insert v t) e,a)}
  lookupVar t  = get >>= \(s,_) -> return(lookupSubst t s)

#endif

-- ------------------------------------------
-- MonadFresh: Variants of terms and clauses
-- ------------------------------------------

class Monad m => MonadFresh var m | m -> var where freshVar :: m var
instance (Enum v, Monad m) => MonadFresh v (StateT (Sum Int) m) where freshVar = do { Sum i <- get; put (Sum $ succ i); return (toEnum i)}
instance Monad m => MonadFresh v (StateT [v] m)     where freshVar = do { x:xx <- get; put xx; return x}
instance Monad m => MonadFresh v (StateT (a,[v]) m) where freshVar = withSnd freshVar

#ifndef TRANSFORMERS
instance MonadFresh v (State [v])     where freshVar = do { x:xx <- get; put xx; return x}
instance MonadFresh v (State (a,[v])) where freshVar = do {(s,x:xx) <- get; put (s,xx); return x}
#endif

fresh ::  (Traversable t, MonadEnv t var m, MonadFresh var m) =>
         Term t var -> m (Term t var)
fresh = go where
  go  = liftM join . T.mapM f
  f v = do
          mb_v' <- lookupVar v
          case mb_v' of
            Nothing -> do {v' <- freshVar; varBind v (return v'); return (return v')}
            Just v' -> return v'

fresh' ::  (Traversable t, MonadEnv t (Either var var') m, MonadFresh var' m) =>
          Term t var -> m (Term t var')
fresh' = go where
  go  = liftM join . T.mapM f
  f v = do
          mb_v' <- lookupVar (Left v)
          case mb_v' of
            Nothing -> do {v' <- freshVar; varBind (Left v) (return $ Right v'); return (return v')}
            Just (Pure (Right v')) -> return (Pure v')
            _ -> error "impossible: fresh'"

variant :: forall v t t'. (Ord v, Enum v, Functor t', Foldable t', Traversable t) => Term t v -> Term t' v -> Term t v
variant u t = fresh u `evalStateT` (mempty :: Substitution t v) `evalState` ([toEnum 0..] \\ vars t)

-- ------------------------------
-- Liftings of monadic operations
-- ------------------------------
instance (Monoid w, Functor t, MonadEnv t var m) => MonadEnv t var (WriterT w m) where
  varBind = (lift.) . varBind
  lookupVar = lift . lookupVar

instance MonadEnv t v m => MonadEnv t v (ListT m) where
  varBind   = (lift.) . varBind
  lookupVar = lift    . lookupVar

instance (Functor t, MonadEnv t var m) => MonadEnv t var (StateT s m) where
  varBind = (lift.) . varBind
  lookupVar = lift . lookupVar

instance (Functor t, MonadEnv t var m) => MonadEnv t var (ReaderT r m) where
  varBind = (lift.) . varBind
  lookupVar = lift . lookupVar

instance (Monoid w, Functor t, MonadEnv t var m) => MonadEnv t var (RWST r w s m) where
  varBind = (lift.) . varBind
  lookupVar = lift . lookupVar

instance MonadFresh var m => MonadFresh var (ListT    m) where freshVar = lift freshVar
instance MonadFresh var m => MonadFresh var (StateT s m) where freshVar = lift freshVar
instance (MonadFresh var m,Monoid w) => MonadFresh var (WriterT w m) where freshVar = lift freshVar
