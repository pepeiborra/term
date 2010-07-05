{-# LANGUAGE OverlappingInstances, UndecidableInstances, ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE CPP #-}

module Data.Term.Annotated (
     Measured(..),
-- * Terms
     Term,
     mkT, mkV, getT, getV, free, ann,
     foldTerm, foldTermM, mapTerm, evalTerm,
     annotate, dropNotes,
-- * Subterms
     subterms, properSubterms, directSubterms, mapSubterms, mapMSubterms, collect,
     someSubterm, someSubterm', someSubtermDeep,
-- * Positions
     Position, positions, (!), (!*), (!?), updateAt, updateAt', updateAtM, occurrences,
-- * Variables
     Rename(..), isVar, vars, isLinear,
-- * Annotating terms
     WithNote(..), WithNote1(..), note, dropNote, Sans.noteV, annotateWithPos, annotateWithPosV,
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

import           Control.Applicative                 hiding (pure)
import           Control.Monad.Free.Annotated        hiding (ann, fmap, join, mapM)
import qualified Control.Monad.Free.Annotated        as Free
import           Control.Monad.Identity              (runIdentity, liftM, MonadPlus(..), msum, when)
import           Control.Monad.Trans                 (lift)

#ifdef TRANSFORMERS
import           Control.Monad.Trans.State           (State, StateT(..), get, put, modify, evalState, evalStateT, execStateT)
import           Control.Monad.Trans.List(ListT)
import           Control.Monad.Trans.Reader(ReaderT)
import           Control.Monad.Trans.RWS             (RWST, ask, evalRWST)
import           Control.Monad.Trans.Writer(WriterT)
#else
import           Control.Monad.State                 (State, StateT(..), get, put, modify, evalState, evalStateT, execStateT)
import           Control.Monad.List(ListT)
import           Control.Monad.Reader(ReaderT)
import           Control.Monad.RWS                   (RWS,RWST, ask, evalRWST)
import           Control.Monad.Writer(WriterT)
#endif

import           Data.Bifunctor
import           Data.Foldable                       (Foldable(..), toList)
import           Data.List                           ((\\))
import           Data.Map                            (Map)
import qualified Data.Map                            as Map
import           Data.Maybe                          (isJust)
import           Data.Monoid
import           Data.Set                            (Set)
import qualified Data.Set                            as Set
import           Data.Traversable                    as T

import           Data.Term                           (HasId(..), MapId(..), WithNote(..), WithNote1(..), MonadVariant(..), Rename(..))
import qualified Data.Term                           as Sans
import           Data.Term.Utils
import           Prelude                             as P hiding (mapM)

-- --------
-- * Terms
-- --------
type Term = Free

mkT :: (Functor t, Foldable t, Measured a ann) => t(Term ann t a) -> Term ann t a
mkV :: Measured a ann => a -> Term ann t a

mkT = impure
mkV = pure

getV = evalTerm Just (const Nothing)
getT = evalTerm (const Nothing) Just

free :: Term ann t a -> Either a (t(Term ann t a))
free (Impure _ f) = Right f
free (Pure   _ v) = Left  v

ann :: Term ann t a -> ann
ann = Free.ann

dropNotes :: Functor t => Term ann t a -> Sans.Term t a
dropNotes = down

annotate :: (Foldable t, Functor t, Measured a ann) => Sans.Term t a -> Term ann t a
annotate = up

foldTerm :: Functor t => (a -> b) -> (t b -> b) -> Term ann t a -> b
foldTerm = foldFree

foldTermM :: (Traversable t, Monad m) => (a -> m b) -> (t b -> m b) -> Term ann t a -> m b
foldTermM = foldFreeM

mapTerm :: (Functor t, Functor t', Foldable t', Measured a ann) =>
           (forall a. t a -> t' a) -> Term ann t a -> Term ann t' a
mapTerm = mapFree

evalTerm :: (a -> b) -> (f (Term ann f a) -> b) -> Term ann f a -> b
evalTerm = evalFree

subterms, directSubterms, properSubterms :: (Functor termF, Foldable termF) =>
                             Term ann termF var -> [Term ann termF var]
subterms t = t : properSubterms t
directSubterms = evalFree (const []) toList
properSubterms = foldFree' (\ann v -> [Pure ann v]) (const fold)
--properSubterms = evalFree (const []) (P.concatMap subterms . toList)

mapSubterms :: (Foldable t, Functor t, Measured a ann) =>
               (Term ann t a -> Term ann t a) -> Term ann t a -> Term ann t a
mapSubterms f  = evalFree' Pure (\_ -> impure . fmap f)

mapMSubterms :: (Traversable t, Monad m, Measured a ann) =>
                (Term ann t a -> m(Term ann t a)) -> Term ann t a -> m(Term ann t a)
mapMSubterms f = evalFree' ((return.) . Pure) (\_ -> liftM impure . mapM f)


-- | Only 1st level subterms
someSubterm :: (Traversable f, MonadPlus m, Measured a ann) =>
               (Term ann f a -> m(Term ann f a)) -> Term ann f a -> m (Term ann f a)
someSubterm f  = evalFree' ((return.) . Pure) (\ann -> msum . liftM2 (Impure ann) . interleaveM f)

-- | Only 1st level subterms
someSubterm' :: (Traversable f, MonadPlus m, Measured a ann) =>
                (Term ann f a -> m(Term ann f a)) -> Term ann f a -> m (Position, Term ann f a)
someSubterm' f  = evalFree'( ((return . ([],)).) . Pure)
                           (\_ ->
                             msum
                           . zipWith (\p -> liftM ([p],)) [1..]
                           . liftM2 impure
                           . interleaveM f)

interleaveDeep :: forall m f a ann. (Monad m, Traversable f, Measured a ann) =>
                  (Term ann f a -> m (Term ann f a)) -> Term ann f a -> [m (Position, Term ann f a)]
interleaveDeep f t
   = [liftM (\(t',_) -> (cursor,t')) $ evalRWST indexedComp cursor []
          | cursor <- positions t]
   where
     indexedComp = foldFreeM' ((return.).Pure) f' t

     f' :: ann -> f (Term ann f a) -> RWST Position () Position m (Term ann f a)
     f' _ = liftM impure
          . unsafeZipWithGM (\pos t -> modify (++[pos]) >> indexedf t)
                            [0..]

     indexedf :: Term ann f a -> RWST Position () Position m (Term ann f a)
     indexedf x = get >>= \pos -> ask >>= \cursor ->
                  if pos == cursor then lift(f x) else return x

     unsafeZipWithGM f t1 t2  = evalStateT (mapM zipG' t2) (toList t1)
       where zipG' y = do (x:xx) <- get
                          put xx
                          lift (f x y)


someSubtermDeep :: (Traversable f, MonadPlus m, Measured a ann) =>
                   (Term ann f a -> m(Term ann f a)) -> Term ann f a -> m (Position, Term ann f a)
someSubtermDeep f = msum . interleaveDeep f

collect :: (Foldable f, Functor f) =>
           (Term ann f v -> Bool) -> Term ann f v -> [Term ann f v]
collect pred t = [ u | u <- subterms t, pred u]

vars :: (Functor termF, Foldable termF) => Term ann termF var -> [var]
vars = toList

isVar :: Term ann termF var -> Bool
isVar = isPure

isLinear :: (Ord v, Foldable t, Functor t) => Term ann t v -> Bool
isLinear t = length(snub varst) == length varst where
    varst = vars t


-- -----------
-- * Positions
-- -----------
type Position = [Int]

positions :: (Functor f, Foldable f) => Term ann f v -> [Position]
positions = foldFree (const []) f where
    f x = [] : concat (zipWith (\i pp -> map (i:) pp) [1..] (toList x))

-- | get subterm at position or fail with error
(!) :: Foldable f => Term ann f v -> Position -> Term ann f v
t ! []     = t
t ! (i:ii) = evalFree (error "(!): invalid position") (\it -> toList it !! (i-1) ! ii) t


-- | t !? pos returns the deepest subterm at position p and some p' where pos = p.p'
(!?) :: (Monad m, Foldable f) => Term ann f v -> Position -> m (Term ann f v, Position)
t !? []     = return (t,[])
t !? (i:ii) = evalFree (\_ -> return (t,i:ii))
                       (\t -> do {x <- toList t !!* (i-1); x !? ii})
                       t
-- | get subterm at position or call @fail@ in @m@
(!*) :: (Monad m, Foldable f) => Term ann f v -> Position -> m(Term ann f v)
t !* []     = return t
t !* (i:ii) = evalFree (fail "(!*): invalid position")
                       (\t -> do {x <- toList t !!* (i-1); x !* ii})
                       t
infixr 4 !!*
(!!*) :: Monad m => [a] -> Int -> m a
x:_  !!* 0 = return x
_:xx !!* i = xx !!* i - 1
[]   !!* _ = fail "!!*: index too large"

-- | Updates the subterm at the position given
--   A failure to reach the position given results in a runtime error
updateAt  :: (Traversable f, Measured a ann) =>  Position -> (Term ann f a -> Term ann f a) -> Term ann f a -> Term ann f a
updateAt (0:_)  _ = error "updateAt: 0 is not a position!"
updateAt []     f = f
updateAt (i:ii) f = evalFree err (\t -> impure (unsafeZipWithG g [1..] t))
         where g j st = if i==j then updateAt ii f st else st
               err = error "updateAt: invalid position given"


-- | Updates the subterm at the position given,
--   returning a tuple with the new term and the previous contents at that position.
--   Failure is contained inside the monad
updateAt'  :: (Traversable f, Measured a ann, Monad m) =>
              Position -> (Term ann f a -> Term ann f a) -> Term ann f a -> m (Term ann f a, Term ann f a)
updateAt' pos f = updateAtM pos (return . f)

-- | Monadic version of @updateAt'@
updateAtM  :: (Traversable f, Measured a ann, Monad m) =>
              Position -> (Term ann f a -> m(Term ann f a)) -> Term ann f a -> m (Term ann f a, Term ann f a)
updateAtM pos f t = runStateT (go pos t) t where
 go (0:_)  _ = fail "updateAt: 0 is not a position!"
 go []     t = put t >> lift(f t)
 go (i:ii) t = foldFreeM (\_ -> fai) (liftM impure . unsafeZipWithGM g [1..]) t
  where fai    = fail "updateAt: invalid position given"
        g j st = if i==j then go ii st else return st


note :: Term ann (WithNote1 n t) (WithNote n a) -> n
note = evalFree (\(Note (n,_)) -> n) (\(Note1 (n,_)) -> n)

dropNote :: (Functor t, Foldable t) =>
            Term ann (WithNote1 n t) (WithNote n a) -> Free ann t a
dropNote = foldFree' (\ann (Note (_,v)) -> Pure ann v) (\ann (Note1 (_,x)) -> Impure ann x)

annotateWithPos :: (Traversable f, Monoid ann) =>
                   Term ann f v -> Term ann (WithNote1 Position f) (WithNote Position v)
annotateWithPos = go [] where
     go pos = evalFree' (\ann -> Pure   ann . Note . (pos,))
                        (\ann -> Impure ann . Note1 . (pos,) . unsafeZipWithG (\p' -> go (pos ++ [p'])) [1..] ) -- TODO Remove the append at tail

annotateWithPosV :: (Traversable f, Monoid ann) =>
                    Term ann f v -> Term ann f (WithNote Position v)
annotateWithPosV= go [] where
     go pos = evalFree' (\ann -> Pure   ann . Note . (pos,))
                        (\ann -> Impure ann . unsafeZipWithG (\p' -> go (pos ++ [p'])) [1..]) -- TODO Remove the append at tail

occurrences :: (Traversable f, Eq (Term ann f v), Monoid ann) =>
               Term ann f v -> Term ann f v -> [Position]
occurrences sub parent = [ note t | t <- subterms(annotateWithPos parent)
                                  , dropNote t == sub]

instance Measured a m => Measured (WithNote note a) m where
  measure (Note (_,a)) = measure a

instance Measured (f a) m => Measured (WithNote1 note f a) m where
  measure (Note1 (_,fa)) = measure fa

{-
newtype PosNote = PosNote (State [Position] Position)
instance Monoid PosNote where
  mempty = PosNote $ return []
  mappend (PosNote m1) (PosNote m2) = PosNote (m1>>m2)

instance Measured var PosNote where
  measure _ = PosNote $ do
      p:pp <- get
      put pp
      return p
-}
-- -----
-- * Ids
-- -----
instance HasId f => HasId (Free h f) where
    type TermId (Free h f) = TermId f
    getId = evalFree (const Nothing) getId

rootSymbol :: HasId f => Term ann f v -> Maybe (TermId f)
rootSymbol = getId

mapRootSymbol :: (Functor (f id), Foldable (f id), MapId f, Measured v ann) => (id -> id) -> Term ann (f id) v -> Term ann (f id) v
mapRootSymbol f = evalFree pure (impure . mapId f)

mapTermSymbols :: (Functor (f id), Foldable (f id'), Functor (f id'), MapId f, Measured v ann) =>
                  (id -> id') -> Term ann (f id) v -> Term ann (f id') v
mapTermSymbols f = mapFree (mapId f)

mapTermSymbolsM :: (Traversable (f id), Functor (f id'), Foldable (f id'), MapId f, Measured v ann, Monad t) =>
                   (id -> t id') -> Term ann (f id) v -> t(Term ann (f id') v)
mapTermSymbolsM f = mapFreeM (mapIdM f)

-- ---------------
-- * Substitutions
-- ---------------
type Substitution ann termF var = SubstitutionF var (Term ann termF var)

newtype SubstitutionF k a = Subst {unSubst::Map k a}
  deriving (Functor)

instance (Functor t, Foldable t, Measured v ann, Ord v) => Monoid (Substitution ann t v) where
  mempty = Subst mempty
  s1 `mappend` s2 =  (applySubst s2 <$> s1)

deriving instance (Eq v,   Eq (Term ann t v))   => Eq (Substitution ann t v)
deriving instance (Ord v,  Ord (Term ann t v))  => Ord (Substitution ann t v)
deriving instance (Show v, Show (Term ann t v)) => Show (Substitution ann t v)

emptySubst :: Ord v => Substitution ann t v
emptySubst = Subst mempty

liftSubst :: (Map v (Term ann t v) ->  Map v' (Term ann t' v')) -> Substitution ann t v -> Substitution ann t' v'
liftSubst f (Subst e) = Subst (f e)

lookupSubst :: Ord v => v -> Substitution ann t v -> Maybe (Term ann t v)
lookupSubst v (Subst m) = Map.lookup v m

applySubst :: (Ord v, Functor t, Foldable t, Measured v ann) => Substitution ann t v -> Term ann t v -> Term ann t v
applySubst s = (Free.bind f) where
    f v = case lookupSubst v s of
            Nothing -> pure v
            Just t' -> t'

domain :: Substitution ann t v -> Set v
domain = Map.keysSet . unSubst

codomain :: Substitution ann t v -> [Term ann t v]
codomain = Map.elems . unSubst

restrictTo :: Ord var => [var] -> Substitution ann id var -> Substitution ann id var
restrictTo vv = liftSubst f where
  f e = Map.intersectionWith const e (Map.fromDistinctAscList (zip vv (repeat undefined)))

isEmpty :: Substitution ann id v -> Bool
isEmpty (Subst m) = Map.null m

fromListSubst :: Ord v => [(v,Term ann termF v)] -> Substitution ann termF v
fromListSubst = Subst . Map.fromList

zonkTerm :: (Functor termF, Foldable termF, Ord var, Measured var' ann) =>
            Substitution ann termF var -> (var -> var') -> Term ann termF var -> Term ann termF var'
zonkTerm subst fv = (bind f) where
   f v = case lookupSubst v subst of
           Nothing -> pure (fv v)
           Just t  -> zonkTerm subst fv t

zonkTermM :: (Traversable termF, Measured var' ann, Ord var, MonadEnv ann termF var m) =>
             (var -> m var') -> Term ann termF var -> m(Term ann termF var')
zonkTermM fv = liftM Free.join . Free.mapM f where
   f v = do val <- lookupVar v
            case val of
              Nothing -> pure `liftM` fv v
              Just t  -> zonkTermM fv t

zonkSubst :: (Functor termF, Foldable termF, Measured var ann, Ord var) =>
             Substitution ann termF var -> Substitution ann termF var
zonkSubst s = liftSubst (Map.map (zonkTerm s id)) s

isRenaming :: (Functor termF, Measured var ann, Ord var, Ord (Term ann termF var)) =>
              Substitution ann termF var -> Bool
isRenaming (Subst subst) = all isVar (Map.elems subst) &&
                           isBijective (Map.mapKeysMonotonic pure subst)
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
class (Functor termF, Monad m) => MonadEnv ann termF var m | m -> ann termF var where
    varBind   :: var -> Term ann termF var -> m ()
    lookupVar :: var -> m (Maybe (Term ann termF var))

    find      :: (Monoid ann, Measured var ann) => var -> m(Term ann termF var)
    find v = do
      mb_t <- lookupVar v
      case mb_t of
        Just t  -> evalFree find (\_ -> varBind v t >> return t) t
        Nothing -> return (pure v)

    zonkM :: (Traversable termF, Measured var ann, Measured var' ann) => (var -> m var') -> Term ann termF var -> m(Term ann termF var')
    zonkM fv = liftM Free.join . Free.mapM f where
        f v = do mb_t <- lookupVar v
                 case mb_t of
                   Nothing -> pure `liftM` fv v
                   Just t  -> zonkM fv t


{-# INLINE find' #-}
find' :: (Monoid ann, Measured v ann) => MonadEnv ann termF v m => Term ann termF v -> m(Term ann termF v)
find' t = evalFree find (\_ -> return t) t

instance (Monad m, Functor t, Ord v) => MonadEnv ann t v (StateT (Substitution ann t v) m) where
  varBind v t = do {e <- get; put (liftSubst (Map.insert v t) e)}
  lookupVar t  = get >>= \s -> return(lookupSubst t s)

instance (Monad m, Functor t, Ord v) => MonadEnv ann t v (StateT (Substitution ann t v, a) m) where
  varBind v = withFst . varBind v
  lookupVar = withFst . lookupVar

#ifndef TRANSFORMERS
instance (Functor t, Ord v) => MonadEnv ann t v (State (Substitution ann t v)) where
  varBind v t = do {e <- get; put (liftSubst (Map.insert v t) e)}
  lookupVar t  = get >>= \s -> return(lookupSubst t s)

instance (Functor t, Ord v) => MonadEnv ann t v (State (Substitution ann t v, a)) where
  varBind v t = do {(e,a) <- get; put (liftSubst (Map.insert v t) e,a)}
  lookupVar t  = get >>= \(s,_) -> return(lookupSubst t s)

#endif

-- ------------------------------------
-- * Unification (without occurs check)
-- ------------------------------------
unifies :: (Unify termF, Ord var, Measured var ann) =>
           Term ann termF var -> Term ann termF var -> Bool
unifies t u = isJust (unify t u)

unify :: (Unify termF, Ord var, Measured var ann) =>
         Term ann termF var -> Term ann termF var -> Maybe (Substitution ann termF var)
unify t u = fmap zonkSubst (execStateT (unifyM t u) mempty)

class (Traversable termF, Eq (termF ())) => Unify termF
  where unifyM :: (Monoid ann, Measured var ann, MonadEnv ann termF var m, Ord var) => Term ann termF var -> Term ann termF var -> m ()

-- Generic instance
instance (Traversable termF, Eq (termF ())) => Unify termF where
  unifyM = unifyMDefault

unifyMDefault :: ( Traversable termF, Eq (termF ())
                 , Monoid ann, Measured var ann
                 , MonadEnv ann termF var m, Ord var
                 ) => Term ann termF var -> Term ann termF var -> m ()
unifyMDefault t s = do
    t' <- find' t
    s' <- find' s
    unifyOne t' s'
   where
     unifyOne (Pure _ vt) s@(Pure _ vs) = when (vt /= vs) $ varBind vt s
     unifyOne (Pure _ vt) s             = varBind vt s
     unifyOne t             (Pure _ vs) = varBind vs t
     unifyOne t           s             = zipFree_ unifyM t s


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

occursIn :: (Ord v, Measured v ann, Traversable t, MonadEnv ann t v m) => v -> Term ann t v -> m Bool
occursIn v t = do
  t' <- zonkM return t
  return (v `Set.member` Set.fromList (vars t'))

-- ----------
-- * Matching
-- ----------
matches :: (Match termF, Ord var, Measured var ann) =>
           Term ann termF var -> Term ann termF var -> Bool
matches t u = isJust (match t u)

match :: (Match termF, Ord var, Measured var ann) =>
         Term ann termF var -> Term ann termF var -> Maybe (Substitution ann termF var)
match t u = execStateT (matchM t u) mempty

class (Eq (termF ()), Traversable termF) => Match termF where
    matchM :: (Eq var, Measured var ann, MonadEnv ann termF var m) => Term ann termF var -> Term ann termF var -> m ()

instance (Traversable termF, Eq (termF ())) =>  Match termF where
  matchM t s = do
    t' <- find' t
    matchOne t' s
    where matchOne (Pure _ v) (Pure _ u) | v == u = return ()
          matchOne (Pure _ v) u = do
              bound_already <- isJust `liftM` lookupVar v
              if bound_already then fail "incompatible" else varBind v u
          matchOne t        u = zipFree_ matchM t u

-- -----------------------------
-- ** Equivalence up to renaming
-- -----------------------------

equiv :: (Ord var, Rename var, Enum var, Measured var ann, Ord (Term ann termF var), Unify termF) =>
         Term ann termF var -> Term ann termF var -> Bool
equiv t u = maybe False isRenaming (match (variant t u) u)

equiv2 t u = let t' = variant t u in matches t' u && matches u t'

newtype EqModulo a = EqModulo {eqModulo::a}
instance (Ord v, Rename v, Enum v, Measured v ann, Unify t, Ord (Term ann t v)) =>
    Eq (EqModulo (Term ann t v))
 where
    EqModulo t1 == EqModulo t2 = t1 `equiv2` t2

-- --------------------------------
-- * Variants of terms and rules
-- --------------------------------

fresh ::  (Traversable t, Measured var ann, MonadEnv ann t var m, MonadVariant var m) =>
         Term ann t var -> m (Term ann t var)
fresh = go where
  go  = liftM Free.join . Free.mapM f
  f v = do
          mb_v' <- lookupVar v
          case mb_v' of
            Nothing -> do {v' <- renaming v; varBind v (pure v'); return (pure v')}
            Just v' -> return v'

instance (Measured a m, Measured b m) => Measured (Either a b) m where
  measure = either measure measure

freshWith :: (Traversable t, Measured var ann, Measured var' ann, MonadEnv ann t (Either var var') m, MonadVariant var' m) =>
             (var -> var' -> var') -> Term ann t var -> m (Term ann t var')
freshWith fv = liftM Free.join . Free.mapM f where
  f v = do
          mb_v' <- lookupVar (Left v)
          case mb_v' of
            Nothing -> do {v' <- fv v `liftM` freshVar; varBind (Left v) (pure $ Right v'); return (pure v')}
            Just (Pure _ (Right v')) -> return (pure v')
            _ -> error "impossible: fresh'"

variant :: forall v t t' ann.
           (Ord v, Rename v, Enum v, Functor t', Foldable t', Traversable t, Measured v ann) =>
           Term ann t v -> Term ann t' v -> Term ann t v
variant u t = fresh u `evalStateT` (mempty :: Substitution ann t v) `evalState` ([toEnum 0..] \\ vars t)

-- ------------------------------
-- Liftings of monadic operations
-- ------------------------------
instance (Monoid w, Functor t, MonadEnv ann t var m) => MonadEnv ann t var (WriterT w m) where
  varBind = (lift.) . varBind
  lookupVar = lift . lookupVar

instance MonadEnv ann t v m => MonadEnv ann t v (ListT m) where
  varBind   = (lift.) . varBind
  lookupVar = lift    . lookupVar

instance (Functor t, MonadEnv ann t var m) => MonadEnv ann t var (StateT s m) where
  varBind = (lift.) . varBind
  lookupVar = lift . lookupVar

instance (Functor t, MonadEnv ann t var m) => MonadEnv ann t var (ReaderT r m) where
  varBind = (lift.) . varBind
  lookupVar = lift . lookupVar

instance (Monoid w, Functor t, MonadEnv ann t var m) => MonadEnv ann t var (RWST r w s m) where
  varBind = (lift.) . varBind
  lookupVar = lift . lookupVar
