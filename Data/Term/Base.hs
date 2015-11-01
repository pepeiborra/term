{-# LANGUAGE OverlappingInstances, UndecidableInstances, ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, StandaloneDeriving #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE Rank2Types, PolyKinds #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE CPP #-}
module Data.Term.Base where


import Control.Applicative
import Control.Category
import Control.Monad (liftM, MonadPlus(..))
import Control.Monad.Free (Free(..), foldFree, foldFreeM, mapFree, mapFreeM, evalFree, isPure)
import Control.Monad.Identity (runIdentity)
import Control.Monad.Trans (MonadTrans(..))

#ifdef LOGICT
import Control.Monad.Logic (MonadLogic(msplit), LogicT)
#endif

import Data.Bifunctor
import Data.Bitraversable
import Data.Bifoldable
import Data.Foldable (Foldable(..), toList, msum)
import Data.Monoid
import Data.Traversable as T

import Data.Id.Family
import Data.Term.Family
import Data.Term.Utils
import Prelude as P hiding (mapM,(.),id)
import Control.Monad.State (runStateT)
import Control.Monad.State (put)


-- --------
-- * Terms
-- --------
type Term = Free
type TermFor (t :: k)  = Term (TermF t) (Var t)
type UnwrappedTermFor t = (TermF t) (TermFor t)
type instance TermF (Term t v) = t
type instance TermF (Term t) = t
type instance Var   (Term t v) = v

-- | Catamorphism over a term
foldTerm :: Functor t => (a -> b) -> (t b -> b) -> Term t a -> b
foldTerm = foldFree
foldTermM :: (Traversable t, Monad m) => (a -> m b) -> (t b -> m b) -> Term t a -> m b
foldTermM = foldFreeM

-- | Functor from a term structure to another
mapTerm :: (Functor t, Functor t') => (forall a. t a -> t' a) -> Term t a -> Term t' a
mapTerm f = mapFree f

-- | Destructor
evalTerm :: (a -> b) -> (f (Free f a) -> b) -> Free f a -> b
evalTerm = evalFree


subterms, properSubterms, directSubterms :: Foldable termF => Term termF var -> [Term termF var]
-- | Get all subterms of a term, including the term itself
subterms t = t : properSubterms t
-- | Get all the subterms of a term, excluding the term itself
properSubterms (Impure t) =  P.concat (subterms <$> toList t)
properSubterms _          = []
-- | Get the direct children of a term
directSubterms (Impure t) = toList t
directSubterms _          = []

-- | Map a endomorphism over the subterms of a term
mapSubterms :: Functor t => (Term t v -> Term t v) -> Term t v -> Term t v
mapSubterms f  = evalTerm return (Impure . fmap f)

mapMSubterms :: (Traversable t, Monad m) => (Term t v -> m(Term t v)) -> Term t v -> m(Term t v)
mapMSubterms f = evalTerm (return.return) (liftM Impure . mapM f)


-- | Non-deterministically applies a non-deterministic endomorphism over the children of a term
someSubterm :: (Traversable f, MonadPlus m) => (Term f a -> m(Term f a)) -> Term f a -> m (Term f a)
someSubterm f  = evalFree (return.return) (msum . liftM2 Impure . interleaveM f)

-- | Same as 'someSubterm', but the return type includes the position
someSubterm' :: (Traversable f, MonadPlus m) => (Term f a -> m(Term f a)) -> Term f a -> m (Position, Term f a)
someSubterm' f  = evalTerm ( return . ([],) . return )
                           ( msum
                           . zipWith (\p -> liftM ([p],)) [1..]
                           . liftM2 Impure
                           . interleaveM f)

-- | Same as 'someSubterm'', but over all the subterms not just the children
someSubtermDeep :: (Traversable t, MonadPlus m) =>
                  (Term t a -> m(Term t a)) -> Term t a -> m (Position, Term t a)
someSubtermDeep f t = (foldTerm (\_ -> mzero)
                             (\(Note1(pos,Note1(me,subs))) ->
                                liftM ((pos,) . (\me -> updateAt pos (const me) t)) me
                                 `mplus` msum subs)
                      . annotateWithPos
                      . annotate f
                      ) t

-- | Collect all the subterms that satisfy a predicate
collect :: (Foldable f, Functor f) => (Term f v -> Bool) -> Term f v -> [Term f v]
collect pred t = [ u | u <- subterms t, pred u]

-- | Returns all the variables of a term
vars :: (Functor termF, Foldable termF) => Term termF var -> [var]
vars = toList

-- | True if the term is a variable
isVar :: Term termF var -> Bool
isVar = isPure

-- | True if the term is linear, i.e. it contains no duplicate variables
isLinear :: (Ord v, Foldable t, Functor t) => Term t v -> Bool
isLinear t = length(snub varst) == length varst where
    varst = vars t

-- -----------
-- * Positions
-- -----------
type Position = [Int]

-- | Returns a list with all the positions in a term
positions :: (Functor f, Foldable f) => Term f v -> [Position]
positions = foldFree (const [[]]) f where
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

-- | Tuple a value with a note
newtype WithNote note a    = Note  (note, a) deriving (Show)
-- | Tuple a functor with a note
newtype WithNote1 note f a = Note1 (note, f a) deriving (Show)

type instance Id  (WithNote  n a) = Id a
type instance Id (WithNote1 n f) = Id f

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
instance Bifunctor WithNote where bimap f g (Note (n,a)) = Note (f n, g a)
instance Bifoldable WithNote where bifoldMap f g (Note (n,a)) = f n `mappend` g a
instance Bitraversable WithNote where bitraverse f g (Note (n,a)) = (Note.) . (,) <$> f n <*> g a

-- | Given an annotated term structure, extract the top level note
note :: Term (WithNote1 n t) (WithNote n a) -> n
note (Impure (Note1 (n,_))) = n
note (Pure (Note (n,_)))    = n

-- | Note extract function
noteV :: WithNote n a -> n
noteV (Note (n,_)) = n

-- | Forgetful functor for annotated terms with annotated variables
dropNote :: Functor t => Free (WithNote1 n t) (WithNote n a) -> Free t a
dropNote = foldTerm (\(Note (_,v)) -> return v) (\(Note1 (_,x)) -> Impure x)

-- | Forgetful functor for anotated terms
dropNote1 :: Functor t => Free (WithNote1 n t) a -> Free t a
dropNote1 = foldTerm return (\(Note1 (_,x)) -> Impure x)

-- | Annotates a term tree with the positions
annotateWithPos :: Traversable f => Free f a -> Free (WithNote1 Position f) (WithNote Position a)
annotateWithPos = foldFree (\v -> return $ Note ([],v))
                           (Impure . Note1 . ([],) . unsafeZipWithG(\i pp -> mapNote (i:) pp) [1..])
  where
    -- TODO replace with Bifunctor instance for WithNote1
    mapNote f (Impure(Note1(n,t))) = Impure(Note1(f n, t))
    mapNote f (Pure (Note (pp,v))) = Pure (Note(f pp, v))

annotateWithPosV :: Traversable f => Term f v -> Term f (WithNote Position v)
annotateWithPosV= go [] where
     go pos = evalFree (\v -> return $ Note (pos,v))
                       (\t -> Impure (unsafeZipWithG (\p' -> go (pos ++ [p'])) [1..] t)) -- TODO Remove the append at tail

occurrences :: (Traversable f, Eq (Term f v)) => Term f v -> Term f v -> [Position]
occurrences sub parent = [ note t | t <- subterms(annotateWithPos parent), dropNote t == sub]

annotate :: (Traversable f) => (Term f v -> note) -> Term f v -> Term (WithNote1 note f) v
annotate f = foldTerm return (\t -> (Impure . Note1 . (,t) . f . Impure . fmap dropNote1) t)

annotateM :: (Traversable f, Monad m) => (Term f v -> m note) -> Term f v -> m(Term (WithNote1 note f) v)
annotateM f = foldTermM (return.return)
                        (\t -> (liftM(Impure . Note1 . (,t)) . f . Impure . fmap dropNote1) t)


-- -----
-- * Ids
-- -----
type instance Id (Free f)   = Id f
type instance Id (Free f v) = Id f

class HasId1 f where
  getId1 :: f a -> Maybe (Id f)
  fromId1 :: Id f -> f a

class HasId a where
    getId :: a -> Maybe (Id a)
    fromId :: Id a -> a

instance HasId1 f => HasId (Free f v) where
    getId = evalFree (const Nothing) getId1
    fromId = Impure . fromId1

class MapId f where mapId  :: (id -> id') -> f id a -> f id' a
                    mapIdM :: (Applicative m) => (id -> m id') -> f id a -> m(f id' a)
                    mapId f = runIdentity  . mapIdM (pure.f)

instance Bitraversable f => MapId f where mapIdM f = bitraverse f pure

-- | Extracts the root symbol if any
rootSymbol :: HasId1 f => Term f v -> Maybe (Id f)
rootSymbol = getId

-- | Maps an endomorphism over the root symbol
mapRootSymbol :: (Functor (f id), MapId f) => (id -> id) -> Term (f id) v -> Term (f id) v
mapRootSymbol f = evalFree return (Impure . mapId f)

-- | Functor that maps a morphism over all the symbols
mapTermSymbols :: (Functor (f id), Functor (f id'), MapId f) => (id -> id') -> Term (f id) v -> Term (f id') v
mapTermSymbols f = mapFree (mapId f)

-- | Kleisli functor that maps a computation over all the symbols
mapTermSymbolsM :: (Traversable (f id), Functor (f id'), MapId f, Applicative t, Monad t) => (id -> t id') -> Term (f id) v -> t(Term (f id') v)
mapTermSymbolsM f = mapFreeM (mapIdM f)
