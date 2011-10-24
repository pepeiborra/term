{-# LANGUAGE OverlappingInstances, UndecidableInstances, ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE CPP #-}

module Data.Term (
-- * Terms
     Term, Free(..), foldTerm, foldTermM, mapTerm, evalTerm,
-- * Subterms
     subterms, properSubterms, directSubterms, mapSubterms, mapMSubterms, collect,
     someSubterm, someSubterm', someSubtermDeep,
-- * Positions
     Position, positions, (!), (!*), (!?), updateAt, updateAt', updateAtM, occurrences,
-- * Variables
     Rename(..), isVar, vars, isLinear,
-- * Annotating terms
     WithNote(..), WithNote1(..), note, dropNote, noteV, annotateWithPos, annotateWithPosV,
-- * Ids
     HasId(..), MapId(..), rootSymbol, mapRootSymbol, mapTermSymbols, mapTermSymbolsM,
-- * Matching & Unification (without occurs check)
     Match(..), Unify(..), unify, occursIn, match, matches, unifies, equiv, equiv2, EqModulo(..),
-- * Substitutions
     Substitution, SubstitutionF(..), emptySubst, fromListSubst, domain, codomain, restrictTo, liftSubst,
     lookupSubst, applySubst, zonkTerm, zonkTermM, zonkSubst, isEmpty, isRenaming,
-- Environment monad
     MonadEnv(..), find',
-- Fresh monad
     MonadVariant(..), fresh, freshWith, variant
     ) where

import Control.Applicative
import Control.Monad (liftM, join, MonadPlus(..), msum, when)
import Control.Monad.Free (Free(..), foldFree, foldFreeM, mapFree, mapFreeM, evalFree, isPure)
import Control.Monad.Free.Zip
import Control.Monad.Identity (runIdentity)
import Control.Monad.Trans (lift)

import Control.Monad.State(StateT(..), get, put, modify, evalState, evalStateT, execStateT)
import Control.Monad.List(ListT)
import Control.Monad.Reader(ReaderT)
import Control.Monad.RWS(RWST, ask, evalRWST)
import Control.Monad.Writer(WriterT)

import Data.Bitraversable
import Data.Foldable (Foldable(..), toList)
import Data.List ((\\))
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (isJust)
import Data.Monoid
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Traversable as T

import Data.Term.Utils
import Prelude as P hiding (mapM)

-- --------
-- * Terms
-- --------
type Term = Free
foldTerm :: Functor t => (a -> b) -> (t b -> b) -> Term t a -> b
foldTerm = foldFree
foldTermM :: (Traversable t, Monad m) => (a -> m b) -> (t b -> m b) -> Term t a -> m b
foldTermM = foldFreeM

mapTerm :: (Functor t, Functor t') => (forall a. t a -> t' a) -> Term t a -> Term t' a
mapTerm f = mapFree f

evalTerm :: (a -> b) -> (f (Free f a) -> b) -> Free f a -> b
evalTerm = evalFree

subterms, properSubterms, directSubterms :: Foldable termF => Term termF var -> [Term termF var]
subterms t = t : properSubterms t
directSubterms (Impure t) = toList t
directSubterms _          = []
properSubterms (Impure t) =  P.concat (subterms <$> toList t)
properSubterms _          = []

mapSubterms :: Functor t => (Term t v -> Term t v) -> Term t v -> Term t v
mapSubterms f  = evalTerm return (Impure . fmap f)

mapMSubterms :: (Traversable t, Monad m) => (Term t v -> m(Term t v)) -> Term t v -> m(Term t v)
mapMSubterms f = evalTerm (return.return) (liftM Impure . mapM f)


-- | Only 1st level subterms
someSubterm :: (Traversable f, MonadPlus m) => (Term f a -> m(Term f a)) -> Term f a -> m (Term f a)
someSubterm f  = evalFree (return.return) (msum . liftM2 Impure . interleaveM f)

-- | Only 1st level subterms
someSubterm' :: (Traversable f, MonadPlus m) => (Term f a -> m(Term f a)) -> Term f a -> m (Position, Term f a)
someSubterm' f  = evalTerm ( return . ([],) . return )
                           ( msum
                           . zipWith (\p -> liftM ([p],)) [1..]
                           . liftM2 Impure
                           . interleaveM f)

interleaveDeep :: forall m f a. (Monad m, Traversable f) =>
                  (Free f a -> m (Free f a)) -> Free f a -> [m (Position, Free f a)]
interleaveDeep f t = [liftM (\(t',_) -> (cursor,t')) $ evalRWST indexedComp cursor []
                         | cursor <- positions t]
   where
     indexedComp = mapFreeM f' t

     f' :: f (Free f a) -> RWST Position () Position m (f(Free f a))
     f' = unsafeZipWithGM (\pos t -> modify (++[pos]) >> indexedf t)
                          [0..]

     indexedf :: Free f a -> RWST Position () Position m (Free f a)
     indexedf x = do {pos <- get; cursor <- ask;
                      if pos == cursor then lift(f x) else return x}

someSubtermDeep :: (Traversable f, MonadPlus m) => (Term f a -> m(Term f a)) -> Term f a -> m (Position, Term f a)
someSubtermDeep f = msum . interleaveDeep f

collect :: (Foldable f, Functor f) => (Term f v -> Bool) -> Term f v -> [Term f v]
collect pred t = [ u | u <- subterms t, pred u]

vars :: (Functor termF, Foldable termF) => Term termF var -> [var]
vars = toList

isVar :: Term termF var -> Bool
isVar = isPure

isLinear :: (Ord v, Foldable t, Functor t) => Term t v -> Bool
isLinear t = length(snub varst) == length varst where
    varst = vars t

-- -----------
-- * Positions
-- -----------
type Position = [Int]

positions :: (Functor f, Foldable f) => Term f v -> [Position]
positions = foldFree (const []) f where
    f x = [] : concat (zipWith (\i pp -> map (i:) pp) [1..] (toList x))

-- | get subterm at position or fail with error
(!) :: Foldable f => Term f v -> Position -> Term f v
Impure t ! (i:ii) = (toList t !! (i-1)) ! ii
t        ! []     = t
_        ! _      = error "(!): invalid position"

-- | t !? pos returns the deepest subterm at position p and some p' where pos = p.p'
(!?) :: (Monad m, Foldable f) => Term f v -> Position -> m (Term f v, Position)
Impure t !? (i:ii) = do {x <- toList t !!* (i-1); x !? ii}
t        !? []     = return (t,[])
t@Pure{} !? pos    = return (t,pos)

-- | get subterm at position or call @fail@ in @m@
(!*) :: (Monad m, Foldable f) => Term f v -> Position -> m(Term f v)
Impure t !* (i:ii) = do {x <- toList t !!* (i-1); x !* ii}
t        !* []     = return t
_        !* _      = fail "(!*): invalid position"

infixr 4 !!*
(!!*) :: Monad m => [a] -> Int -> m a
x:_  !!* 0 = return x
_:xx !!* i = xx !!* i - 1
[]   !!* _ = fail "!!*: index too large"

-- | Updates the subterm at the position given
--   A failure to reach the position given results in a runtime error
updateAt  :: (Traversable f) =>  Position -> (Term f v -> Term f v) -> Term f v -> Term f v
updateAt (0:_)  _          _ = error "updateAt: 0 is not a position!"
updateAt []     f          t = f t
updateAt (i:ii) f (Impure t) = Impure (unsafeZipWithG g [1..] t)
                               where g j st = if i==j then updateAt ii f st else st
updateAt _      _          _ = error "updateAt: invalid position given"


-- | Updates the subterm at the position given,
--   returning a tuple with the new term and the previous contents at that position.
--   Failure is contained inside the monad
updateAt'  :: (Traversable f, Monad m) =>
              Position -> (Term f v -> Term f v) -> Term f v -> m (Term f v, Term f v)
updateAt' pos f = updateAtM pos (return . f)

-- | Monadic version of @updateAt'@
updateAtM  :: (Traversable f, Monad m) =>
              Position -> (Term f v -> m(Term f v)) -> Term f v -> m (Term f v, Term f v)
updateAtM pos f t = runStateT (go pos t) t where
 go (0:_)  _          = fail "updateAt: 0 is not a position!"
 go []     t          = put t >> lift(f t)
 go (i:ii) (Impure t) = Impure `liftM` unsafeZipWithGM g [1..] t
                               where g j st = if i==j then go ii st else return st
 go _      _          = fail "updateAt: invalid position given"

newtype WithNote note a = Note (note, a) deriving (Show)
newtype WithNote1 note f a = Note1 (note, f a) deriving (Show)

instance Eq a => Eq (WithNote n a) where Note (_,a) == Note (_,b) = a == b
--instance (Functor f, Eq (Free f a)) => Eq (Free (WithNote1 n f) a) where
--    a == b = f a == f b  where f = mapTerm (\(Note1 (_,x)) -> x)

instance Eq (f a) => Eq ((WithNote1 n f) a) where Note1 (_,x) == Note1 (_,y) = x == y

instance Ord a => Ord (WithNote n a) where Note (_,a) `compare` Note (_,b) = compare a b
--instance (Functor f, Ord (Free f a)) => Ord (Free (WithNote1 n f) a) where
--    compare a b = f a `compare` f b  where f = mapTerm (\(Note1 (_,x)) -> x)
instance Ord (f a) => Ord ((WithNote1 n f) a) where Note1 (_,x) `compare` Note1 (_,y) = compare x y

instance Functor f  => Functor (WithNote1 note f)  where fmap f (Note1 (p, fx))   = Note1 (p, fmap f fx)
instance Foldable f => Foldable (WithNote1 note f) where foldMap f (Note1 (_p,fx)) = foldMap f fx
instance Traversable f => Traversable (WithNote1 note f) where traverse f (Note1 (p, fx)) = (Note1 . (,) p) <$> traverse f fx
instance Functor (WithNote n) where fmap f (Note (n,a)) = Note (n, f a)
instance Foldable (WithNote n) where foldMap f (Note (_,a)) = f a
instance Traversable (WithNote n) where traverse f (Note (n,a)) = (\a' -> Note (n,a')) <$> f a

note :: Term (WithNote1 n t) (WithNote n a) -> n
note (Impure (Note1 (n,_))) = n
note (Pure (Note (n,_)))    = n

noteV :: WithNote n a -> n
noteV (Note (n,_)) = n

dropNote :: Functor t => Free (WithNote1 n t) (WithNote n a) -> Free t a
dropNote = foldTerm (\(Note (_,v)) -> return v) (\(Note1 (_,x)) -> Impure x)

annotateWithPos :: Traversable f => Term f v -> Term (WithNote1 Position f) (WithNote Position v)
annotateWithPos = go [] where
     go pos = evalFree (\v -> return $ Note (pos,v))
                       (\t -> Impure (Note1 (pos, unsafeZipWithG (\p' -> go (pos ++ [p'])) [1..] t))) -- TODO Remove the append at tail

annotateWithPosV :: Traversable f => Term f v -> Term f (WithNote Position v)
annotateWithPosV= go [] where
     go pos = evalFree (\v -> return $ Note (pos,v))
                       (\t -> Impure (unsafeZipWithG (\p' -> go (pos ++ [p'])) [1..] t)) -- TODO Remove the append at tail

occurrences :: (Traversable f, Eq (Term f v)) => Term f v -> Term f v -> [Position]
occurrences sub parent = [ note t | t <- subterms(annotateWithPos parent), dropNote t == sub]

-- -----
-- * Ids
-- -----
class (Ord (TermId f)) => HasId f where
    type TermId f :: *
    getId :: f a -> Maybe (TermId f)

instance HasId f => HasId (Free f) where
    type TermId (Free f) = TermId f
    getId = evalFree (const Nothing) getId

class MapId f where mapId  :: (id -> id') -> f id a -> f id' a
                    mapIdM :: (Applicative m) => (id -> m id') -> f id a -> m(f id' a)
                    mapId f = runIdentity  . mapIdM (pure.f)

instance Bitraversable f => MapId f where mapIdM f = bitraverse f pure

rootSymbol :: HasId f => Term f v -> Maybe (TermId f)
rootSymbol = getId

mapRootSymbol :: (Functor (f id), MapId f) => (id -> id) -> Term (f id) v -> Term (f id) v
mapRootSymbol f = evalFree return (Impure . mapId f)

mapTermSymbols :: (Functor (f id), Functor (f id'), MapId f) => (id -> id') -> Term (f id) v -> Term (f id') v
mapTermSymbols f = mapFree (mapId f)

mapTermSymbolsM :: (Traversable (f id), Functor (f id'), MapId f, Applicative t, Monad t) => (id -> t id') -> Term (f id) v -> t(Term (f id') v)
mapTermSymbolsM f = mapFreeM (mapIdM f)

-- ---------------
-- * Substitutions
-- ---------------
type Substitution termF var = SubstitutionF var (Term termF var)

newtype SubstitutionF k a = Subst {unSubst::Map k a}
  deriving (Functor)

instance (Functor t, Ord v) => Monoid (Substitution t v) where
  mempty = Subst mempty
  s1 `mappend` s2 =  (applySubst s2 <$> s1)

deriving instance (Eq v,   Eq (Term t v))   => Eq (Substitution t v)
deriving instance (Ord v,  Ord (Term t v))  => Ord (Substitution t v)
deriving instance (Show v, Show (Term t v)) => Show (Substitution t v)

emptySubst :: Ord v => Substitution t v
emptySubst = Subst mempty

liftSubst :: (Map v (Term t v) ->  Map v' (Term t' v')) -> Substitution t v -> Substitution t' v'
liftSubst f (Subst e) = Subst (f e)

lookupSubst :: Ord v => v -> Substitution t v -> Maybe (Term t v)
lookupSubst v (Subst m) = Map.lookup v m

applySubst :: (Ord v, Functor t) => Substitution t v -> Term t v -> Term t v
applySubst s = (>>= f) where
    f v = case lookupSubst v s of
            Nothing -> return v
            Just t' -> t'

domain :: Substitution t v -> Set v
domain = Map.keysSet . unSubst

codomain :: Substitution t v -> [Term t v]
codomain = Map.elems . unSubst

restrictTo :: Ord var => [var] -> Substitution id var -> Substitution id var
restrictTo vv = liftSubst f where
  f e = Map.intersectionWith const e (Map.fromDistinctAscList (zip vv (repeat undefined)))

isEmpty :: Substitution id v -> Bool
isEmpty (Subst m) = Map.null m

fromListSubst :: Ord v => [(v,Term termF v)] -> Substitution termF v
fromListSubst = Subst . Map.fromList

zonkTerm :: (Functor termF, Ord var) => Substitution termF var -> (var -> var') -> Term termF var -> Term termF var'
zonkTerm subst fv = (>>= f) where
   f v = case lookupSubst v subst of
           Nothing -> return (fv v)
           Just t  -> zonkTerm subst fv t

zonkTermM :: (Traversable termF, Ord var, MonadEnv termF var m) =>
             (var -> m var') -> Term termF var -> m(Term termF var')
zonkTermM fv = liftM join . mapM f where
   f v = do val <- lookupVar v
            case val of
              Nothing -> Pure `liftM` fv v
              Just t  -> zonkTermM fv t

zonkSubst :: (Functor termF, Ord var) => Substitution termF var -> Substitution termF var
zonkSubst s = liftSubst (Map.map (zonkTerm s id)) s

isRenaming :: (Functor termF, Ord var, Ord (Term termF var)) => Substitution termF var -> Bool
isRenaming (Subst subst) = all isVar (Map.elems subst) && isBijective (Map.mapKeysMonotonic return subst)
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

-- --------------------------------------
-- ** Environments: handling substitutions
-- --------------------------------------
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
  varBind v = withFst . varBind v
  lookupVar = withFst . lookupVar

-- ------------------------------------
-- * Unification (without occurs check)
-- ------------------------------------
unifies :: forall termF var. (Unify termF, Ord var) => Term termF var -> Term termF var -> Bool
unifies t u = isJust (unify t u)

unify :: (Unify termF, Ord var) => Term termF var -> Term termF var -> Maybe (Substitution termF var)
unify t u = fmap zonkSubst (execStateT (unifyM t u) mempty)

class (Traversable termF, Eq (termF ())) => Unify termF
  where unifyM :: (MonadEnv termF var m, Ord var) => Term termF var -> Term termF var -> m ()

-- Generic instance
instance (Traversable termF, Eq (termF ())) => Unify termF where
  unifyM t s = do
    t' <- find' t
    s' <- find' s
    unifyOne t' s'
   where
     unifyOne (Pure vt) s@(Pure vs) = when (vt /= vs) $ varBind vt s
     unifyOne (Pure vt) s           = varBind vt s
     unifyOne t           (Pure vs) = varBind vs t
     unifyOne t         s           = zipFree_ unifyM t s


{- | Occurs function, to roll your own unification with occurs check.
   To do this, chip in your custom instance of Unify as follows

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

occursIn :: (Ord v, Traversable t, MonadEnv t v m) => v -> Term t v -> m Bool
occursIn v t = do
  t' <- zonkM return t
  return (v `Set.member` Set.fromList (vars t'))

-- ----------
-- * Matching
-- ----------
matches :: forall termF var. (Match termF, Ord var) => Term termF var -> Term termF var -> Bool
matches t u = isJust (match t u)

match :: (Match termF, Ord var) => Term termF var -> Term termF var -> Maybe (Substitution termF var)
match t u = execStateT (matchM t u) mempty

class (Eq (termF ()), Traversable termF) => Match termF where
    matchM :: (Eq var, MonadEnv termF var m) => Term termF var -> Term termF var -> m ()

instance (Traversable termF, Eq (termF ())) =>  Match termF where
  matchM t s = do
    t' <- find' t
    matchOne t' s
    where matchOne (Pure v) (Pure u) | v == u = return ()
          matchOne (Pure v) u = do
              bound_already <- isJust `liftM` lookupVar v
              if bound_already then fail "incompatible" else varBind v u
          matchOne t        u = zipFree_ matchM t u

-- -----------------------------
-- ** Equivalence up to renaming
-- -----------------------------

equiv :: forall termF var.
         (Ord var, Rename var, Enum var, Ord (Term termF var), Unify termF) => Term termF var -> Term termF var -> Bool
equiv t u = maybe False isRenaming (match (variant t u) u)

equiv2 t u = let t' = variant t u in matches t' u && matches u t'

newtype EqModulo a = EqModulo {eqModulo::a}
instance (Ord v, Rename v, Enum v, Unify t, Ord (Term t v)) => Eq (EqModulo (Term t v)) where
    EqModulo t1 == EqModulo t2 = t1 `equiv2` t2

-- --------------------------------
-- * Variants of terms and rules
-- --------------------------------

-- | Renaming of variables
class Rename v where
    rename :: v      -- ^ Original variable
           -> v      -- ^ Fresh variable
           -> v      -- ^ Result of renaming the original variable to the fresh variable

class (Rename var, Monad m) => MonadVariant var m | m -> var where
    freshVar :: m var
    renaming :: var -> m var
    renaming v = do {v' <- freshVar; return $ rename v v'}

instance (Enum v, Rename v, Monad m) => MonadVariant v (StateT (Sum Int) m) where
    freshVar = do { Sum i <- get; put (Sum $ succ i); return (toEnum i)}

instance (Rename v, Monad m) => MonadVariant v (StateT [v] m) where
    freshVar = do { x:xx <- get; put xx; return x}

instance (Rename v, Monad m) => MonadVariant v (StateT (a,[v]) m) where
    freshVar = withSnd freshVar

instance (Monoid w, Rename v, Monad m) => MonadVariant v (RWST r w [v] m) where
    freshVar = do { x:xx <- get; put xx; return x}

fresh ::  (Traversable t, MonadEnv t var m, MonadVariant var m) =>
         Term t var -> m (Term t var)
fresh = go where
  go  = liftM join . T.mapM f
  f v = do
          mb_v' <- lookupVar v
          case mb_v' of
            Nothing -> do {v' <- renaming v; varBind v (return v'); return (return v')}
            Just v' -> return v'

freshWith :: (Traversable t, MonadEnv t (Either var var') m, MonadVariant var' m) =>
               (var -> var' -> var') -> Term t var -> m (Term t var')
freshWith fv = go where
  go  = liftM join . T.mapM f
  f v = do
          mb_v' <- lookupVar (Left v)
          case mb_v' of
            Nothing -> do {v' <- fv v `liftM` freshVar; varBind (Left v) (return $ Right v'); return (return v')}
            Just (Pure (Right v')) -> return (Pure v')
            _ -> error "impossible: fresh'"

variant :: forall v t t'. (Ord v, Rename v, Enum v, Functor t', Foldable t', Traversable t) => Term t v -> Term t' v -> Term t v
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

instance MonadVariant var m => MonadVariant var (ListT    m) where
    freshVar = lift freshVar
    renaming = lift . renaming

instance MonadVariant var m => MonadVariant var (StateT s m) where
    freshVar = lift freshVar
    renaming = lift . renaming

instance (Monoid w, MonadVariant var m) => MonadVariant var (RWST r w s m) where
    freshVar = lift freshVar
    renaming = lift . renaming

instance (MonadVariant var m,Monoid w) => MonadVariant var (WriterT w m) where
    freshVar = lift freshVar
    renaming = lift . renaming
