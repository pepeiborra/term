{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GADTs #-}

module Data.Term.Substitutions where

import Control.Applicative
import Control.Applicative.Compose
import Control.DeepSeq
import Control.Monad (MonadPlus, join, when)
import Control.Monad (liftM)
import Control.Monad.Cont (MonadTrans, lift)
import Control.Monad.Env
import Control.Monad.Free (Free(..), wrap)
import Control.Monad.List (ListT)
import Control.Monad.Logic (LogicT, LogicT, MonadLogic, msplit)
import Control.Monad.RWS (RWST)
import Control.Monad.Reader (ReaderT)
import Control.Monad.State (StateT, get, put, evalStateT, execStateT, runStateT)
import Control.Monad.Variant
import Control.Monad.Writer (WriterT)
import Data.Foldable (Foldable, toList)
import Data.Id.Family
import Data.List ((\\))
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (isJust)
import Data.Monoid
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Term.Base
import Data.Term.Family
import Data.Traversable (Traversable, mapM)
import qualified Data.Traversable as T
import Data.Var.Family
import Data.Foldable (foldMap)
import Prelude hiding (mapM)
import Prelude.Extras

import Debug.Hoed.Observe
import Debug.Hoed.Observe.Instances

-- ---------------
-- * Variables
-- ---------------
import Data.Maybe (fromMaybe)

class GetVars t where
  getVars :: Ord (Var t) => t -> Set (Var t)
  fromVar :: Var t -> t

instance (Functor termF, Foldable termF, Ord var) => GetVars (Term termF var) where
   getVars = Set.fromList . toList
   fromVar = Pure

-- type instance Var (f t) = Var t
instance GetVars t => GetVars [t] where getVars = foldMap getVars
instance GetVars t => GetVars (Set t) where getVars = foldMap getVars
-- instance (GetVars t var, Foldable f, Foldable g) => GetVars (g(f t)) var where getVars = (foldMap.foldMap) getVars


class GetFresh thing where
    getFreshM :: (TermF thing ~ TermF m, Var thing ~ Var m, Traversable (TermF thing), MonadEnv m, MonadVariant m) => thing -> m thing

instance (Traversable termF) => GetFresh (Term termF var) where getFreshM = fresh
instance (Ord a, GetFresh a) => GetFresh (Set a)          where getFreshM = liftM Set.fromList . getFreshM . Set.toList
instance GetFresh t => GetFresh [t] where getFreshM = getFreshMdefault

getFreshMdefault :: (Traversable t, GetFresh a, MonadVariant m, MonadEnv m, Var a ~ Var m, term ~ TermF a, term ~ TermF m, Traversable term) => t a -> m (t a)
getFreshMdefault = T.mapM getFreshM

getFresh :: (MonadVariant m, Observable (Var m), Ord (Var m), GetFresh thing, Traversable (TermF thing), Var thing ~ Var m) =>
            thing -> m thing
getFresh t = evalMEnv (getFreshM t)

getVariant :: ( v ~ Var t, v ~ Var t'
              , Ord v, Observable v, Enum v, Rename v, GetFresh t, GetVars t', Traversable (TermF t)) => t -> t' -> t
getVariant u t = runVariant' ([toEnum 0..] \\ Set.toList (getVars t)) (getFresh u)


-- ---------------
-- * Substitutions
-- ---------------

data Substitution_ a where
  Subst :: Observable(Var a) => {unSubst::Map (Var a) a} -> Substitution_ a

type Substitution t v = Substitution_(Term t v)
type SubstitutionFor t = Substitution (TermF t) (Var t)

subst :: Observable(Var a) => Map (Var a) a -> Substitution_ a
subst = Subst

mapSubst f = liftSubst (fmap f)

s1 `appendSubst` s2 =  liftSubst2 Map.union (applySubst s2 `mapSubst` s1) s2

deriving instance (Eq a,   Eq (Var a))   => Eq (Substitution_ a)
deriving instance (Ord a,  Ord (Var a))  => Ord (Substitution_ a)
deriving instance (Show a, Show (Var a)) => Show (Substitution_ a)

instance (NFData a, NFData(Var a)) => NFData (Substitution_ a) where
  rnf = rnf . unSubst

emptySubst :: (Observable(Var a), Ord(Var a)) => Substitution_ a
emptySubst = subst mempty

liftSubst :: (Observable(Var a), Observable(Var b)) =>
             (Map (Var a) a -> Map (Var b) b) ->
             Substitution_ a -> Substitution_ b
liftSubst f (unSubst -> e) = subst (f e)
liftSubst2 f (unSubst -> e) (unSubst -> b) = subst (f e b)

lookupSubst :: (Ord(Var a)) =>
               Var a -> Substitution_ a -> Maybe a
lookupSubst v (unSubst -> m) = Map.lookup v m

applySubst :: (Ord a, Monad t, a ~ Var(t a)
              ) => Substitution_ (t a) -> t a -> (t a)
applySubst s = (>>= f) where
    f v = case lookupSubst v s of
            Nothing -> return v
            Just t' -> t'

domain :: (Ord(Var t)) => Substitution_ t -> Set (Var t)
domain = Map.keysSet . unSubst

codomain :: () => Substitution_ t -> [t]
codomain = Map.elems . unSubst

restrictTo :: (Ord(Var t), Observable(Var t)
              ) => [Var t] -> Substitution_ t -> Substitution_ t
restrictTo vv = liftSubst f where
  f e = Map.intersectionWith const e (Map.fromDistinctAscList (zip vv (repeat undefined)))

isEmpty :: (Ord(Var t)) => Substitution_ t -> Bool
isEmpty (unSubst -> m) = Map.null m

fromListSubst :: (Ord (Var term), Observable(Var term)
                 ) => [(Var term,term)] -> Substitution_ term
fromListSubst = subst . Map.fromList

zonkTerm :: (v ~ Var (t v), Ord v, Monad t
            ) => Substitution_ (t v) -> (v -> v') -> t v -> t v'
zonkTerm subst fv = (>>= f) where
   f v = case lookupSubst v subst of
           Nothing -> return (fv v)
           Just t  -> zonkTerm subst fv t

zonkTermM :: (termF ~ TermF m, var ~ Var m, Traversable termF, Ord var, MonadEnv m) =>
             (var -> m var') -> Term termF var -> m(Term termF var')
zonkTermM fv = liftM join . mapM f where
   f v = do val <- lookupVar v
            case val of
              Nothing -> Pure `liftM` fv v
              Just t  -> zonkTermM fv t

zonkSubst :: (v ~ Var(t v),  Ord v, Monad t, Observable v
             ) => Substitution_ (t v) -> Substitution_ (t v)
zonkSubst s = liftSubst (Map.map (zonkTerm s id)) s

isRenaming :: (Foldable termF, Functor termF, Ord var, Ord (Term termF var)
              ) => Substitution termF var -> Bool
isRenaming (unSubst -> subst) = all isVar (Map.elems subst) && isBijective (Map.mapKeysMonotonic return subst)
  where
--    isBijective :: Ord k => Map.Map k k -> Bool
     isBijective rel = -- cheap hackish bijectivity check.
                    -- Ensure that the relation is injective and its inverse is too.
                    -- The sets of variables must be disjoint too
                    -- Actually there should be no need to check the inverse
                    -- since this is a Haskell Map and hence the domain contains no duplicates
                   Set.size elemsSet == Map.size rel &&
                   Map.keysSet rel `Set.intersection` elemsSet == Set.empty
       where
          elemsSet = Set.fromList(Map.elems rel)

instance Observable1 Substitution_ where
  observer1 (Subst s) = send "Subst" (return Subst << s)

instance Observable a => Observable (Substitution_ a) where
  observer = observer1
  observers = observers1

-- --------------------------------------
-- ** Environments: handling substitutions
-- --------------------------------------

newtype MEnvT t (v :: *) (m :: * -> *) a = MEnv {unMEnv ::StateT (Substitution_ (Term t v)) m a}
                                           deriving (Functor, Monad, MonadPlus, MonadTrans)

type instance Var   (MEnvT t v m) = v
type instance TermF (MEnvT t v m) = t

instance (Monad m, Foldable t, Functor t, Ord v, Observable v) => MonadEnv (MEnvT t v m) where
  varBind v t = do {e <- MEnv get; MEnv $ put (liftSubst (Map.insert v t) e)}
  lookupVar t  = MEnv get >>= \s -> return(lookupSubst t s)

instance (v ~ Var m, Rename v, MonadVariant m) => MonadVariant (MEnvT t v m) where
--  type MonadVariant.Var (MEnvT t v m) = MonadVariant.Var m
  freshVar = lift freshVar

#ifdef LOGICT
--deriving instance MonadLogic m => MonadLogic (MEnvT t v m)
instance MonadLogic m => MonadLogic (MEnvT t v m) where
  msplit m = MEnv $ (liftM.liftM) f (msplit (unMEnv m)) where
   f (a,m') = (a, MEnv m')

instance (Functor (TermF m), MonadEnv m) => MonadEnv (LogicT m) where
  varBind = (lift.) . varBind
  lookupVar = lift . lookupVar
#endif

execMEnv :: (Foldable t, Functor t, Ord v, Observable v, Monad m) => MEnvT t v m a -> m (Substitution t v)
evalMEnv :: (Foldable t, Functor t, Ord v, Observable v, Monad m) => MEnvT t v m a -> m a
runMEnv  :: (Foldable t, Functor t, Ord v, Observable v, Monad m) => MEnvT t v m a -> m (a, Substitution t v)

execMEnv = (`execStateT` subst mempty) . unMEnv

evalMEnv = (`evalStateT` subst mempty) . unMEnv

runMEnv  = (`runStateT` subst mempty) . unMEnv


instance Monad m => Observable1 (MEnvT t v m) where
  observer1 comp p = do
    res <- comp
    send "<MEnvT>" (return return << res) p

instance (Observable a, Monad m) => Observable (MEnvT t v m a) where
  observer = observer1
  observers = observers1
  
-- instance (Monad m, Functor t, Ord v) => MonadEnv (StateT (Substitution t v, a) m) where
--   type TermF (StateT (Substitution t v, a) m) = t
--   type Var   (StateT (Substitution t v, a) m) = v
--   varBind v = withFst . varBind v
--   lookupVar = withFst . lookupVar

-- ------------------------------------
-- * Unification (without occurs check)
-- ------------------------------------
unifies :: forall termF var. (Unify termF, Ord var, Observable var) => Term termF var -> Term termF var -> Bool
unifies t u = isJust (unify t u)

unify :: (Unify termF, Ord var, Observable var) => Term termF var -> Term termF var -> Maybe (Substitution termF var)

unify t u = fmap zonkSubst (execMEnv (unifyM t u))

class (Traversable termF, Match termF) => Unify termF
  where unifyM :: (MonadEnv m, Ord (Var m), TermF m ~ termF) => Term termF (Var m) -> Term termF (Var m) -> m ()

-- Generic instance
instance (Match termF) => Unify termF where
  unifyM :: forall m. (MonadEnv m, Ord(Var m), TermF m ~ termF) =>
            Term termF (Var m) -> Term termF (Var m) -> m ()
  unifyM t s = do
    t' <- find' t
    s' <- find' s
    unifyOne t' s'
   where
     unifyOne :: Term termF (Var m) -> Term termF (Var m) -> m ()
     unifyOne (Pure vt) s@(Pure vs) = when (vt /= vs) $ varBind vt s
     unifyOne (Pure vt) s           = varBind vt s
     unifyOne t           (Pure vs) = varBind vs t
     unifyOne (Impure t)  (Impure s)= do
       constraints <- T.sequence(unifyM <$> Compose(Just t) <*> Compose(Just s))
       when (not $ isJust $ decompose constraints) $ fail "structure mismatch"
       return ()


{- | Occurs function, to roll your own unification with occurs check.
   To do this, declare your custom instance of Unify as follows

> instance (Traversable termF, Eq (termF ())) => Unify termF where
>   unifyM t s = do
>     t' <- find' t
>     s' <- find' s
>     unifyOne t' s'
>    where
>      unifyOne (Pure vt) s@(Pure vs) = when (vt /= vs) $ varBind vt s
>      unifyOne (Pure vt) s           = vt `occursIn` s' >>= \occ -> if occ then fail "occurs" else  varBind vt s
>      unifyOne t           (Pure vs) = vs `occursIn` t' >>= \occ -> if occ then fail "occurs" else  varBind vs t
>      unifyOne t         s           = zipFree_ unifyM t s
-}

occursIn :: (Ord (Var m), Traversable (TermF m), MonadEnv m) => Var m -> Term (TermF m) (Var m) -> m Bool
occursIn v t = do
  t' <- zonkM return t
  return (v `Set.member` Set.fromList (vars t'))

-- ----------
-- * Matching
-- ----------
{-# INLINABLE matches #-}
matches :: forall termF var. (Ord var, Observable var, Match termF) => Term termF var -> Term termF var -> Bool
matches t u = isJust (match t u)

{-# INLINABLE match #-}
match :: (Ord var, Match termF, Observable var
         ) => Term termF var -> Term termF var -> Maybe(Substitution termF var)
match t u = execMEnv (matchM t u)

type Match term = (Applicative (Maybe :+: term), Traversable term, Eq1 term)

type instance TermF (Maybe :+: m) = TermF m
type instance Var   (Maybe :+: m) = Var   m

deriving instance (Foldable f, Foldable g) => Foldable (f :+: g)
deriving instance (Traversable f, Traversable g) => Traversable (f :+: g)

{-# INLINABLE matchM #-}
matchM :: forall m. (Eq (Var m), Match(TermF m), MonadEnv m
                    ) => TermFor m -> TermFor m -> m ()
matchM t s = do
    matchOne t s
    where
          matchOne :: TermFor m -> TermFor m -> m ()
          matchOne Impure{} Pure{} = fail "match: structure mismatch"
          matchOne (Pure v) u = do
              contents <- lookupVar v
              case contents of
                Just v' -> when (v' /= u) $ fail "incompatible"
                Nothing -> varBind v u
          matchOne (Impure t) (Impure u) = do
            constraints <- T.sequence(matchM <$> Compose(Just t) <*> Compose(Just u))
            when (not $ isJust $ decompose constraints) $ fail "structure mismatch"
            return()


-- -----------------------------
-- ** Equivalence up to renaming
-- -----------------------------
{-# INLINABLE equiv #-}
equiv :: forall termF var.
         (Ord var, Observable var, Rename var, Enum var, Ord (Term termF var), Unify termF) => Term termF var -> Term termF var -> Bool
equiv t u = t == u || maybe False isRenaming (match (variant t u) u)

{-# INLINABLE equiv2 #-}
equiv2 :: (Rename var, Ord var, Observable var, Enum var, Unify termF) => Term termF var -> Term termF var -> Bool
equiv2 t u = let t' = variant t u in matches t' u && matches u t'

newtype EqModulo a = EqModulo {eqModulo::a}
instance (Ord v, Observable v, Rename v, Enum v, Unify t, Ord (Term t v)) => Eq (EqModulo (Term t v)) where
    EqModulo t1 == EqModulo t2 = t1 `equiv2` t2

instance (Ord v, Observable v, Rename v, Enum v, Unify t, Ord (Term t v)) => Ord (EqModulo (Term t v)) where
    t1 `compare` t2 = if t1 == t2 then EQ else compare (eqModulo t1) (eqModulo t2)

-- --------------------------------
-- * Variants of terms and rules
-- --------------------------------

fresh ::  (v ~ Var m, Traversable (TermF m), MonadEnv m, MonadVariant m) =>
         Term (TermF m) v -> m (Term (TermF m) v)
fresh = go where
  go  = liftM join . T.mapM f
  f v = do
          mb_v' <- lookupVar v
          case mb_v' of
            Nothing -> do {v' <- renaming v; varBind v (return v'); return (return v')}
            Just v' -> return v'

freshWith :: (Traversable (TermF m), MonadEnv m, MonadVariant m) =>
               (Var m -> Var m -> Var m) -> TermFor m -> m (TermFor m)
freshWith fv = go where
  go  = liftM join . T.mapM f
  f v = do
          mb_v' <- lookupVar v
          case mb_v' of
            Nothing -> do {v' <- fv v `liftM` freshVar; varBind v (return v'); return (return v')}
            Just (Pure v') -> return (Pure v')

freshWith' :: (Rename var, Observable var, Observable var', Ord var', Ord var, var' ~ Var m, Traversable t, MonadVariant m) =>
               (var -> var' -> var') -> Term t var -> m (Term t var')
freshWith' fv t = variantsWith Right $ evalMEnv $
                  (liftM.fmap) (\(Right x) -> x)
                               (freshWith fv' (fmap Left t))
 where
  fv' (Left v) (Right v') = Right (fv v v')


variant :: forall v t t'. (Ord v, Observable v, Rename v, Enum v, Functor t', Foldable t', Traversable t) => Term t v -> Term t' v -> Term t v
variant u t = runVariant' ([toEnum 0..] \\ vars t) (evalMEnv(fresh u))

