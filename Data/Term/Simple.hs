{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Data.Term.Simple (TermF(..), Term1, constant, term, termId) where

import Control.Monad.Free
import Data.Bifunctor
import Data.Foldable
import Data.Traversable
import Data.Term

data TermF id f = Term {id::id, args::[f]} deriving (Eq,Ord,Show)
type Term1 id = Free (TermF id)

term :: id -> [Term1 id a] -> Term1 id a
term f = Impure . Term f

constant :: id -> Term1 id a
constant f = term f []

termId :: MonadPlus m => Term1 id a -> m id
termId = foldFree (const mzero) f where
    f (Term f tt) = return f `mplus` Data.Foldable.msum tt

-- Specific instance for TermF, only for efficiency
instance Eq id => Unify (TermF id) where
  {-# SPECIALIZE instance Unify (TermF String) #-}
  unifyM = unifyF where
   unifyF t s = do
    t' <- find' t
    s' <- find' s
    case (t', s') of
      (Pure vt, Pure vs) -> when(vt /= vs) $ varBind vt s'
      (Pure vt, _)  -> varBind vt s'
      (_, Pure vs)  -> varBind vs t'
      (Impure t, Impure s) -> zipTermM_ unifyF t s
   zipTermM_ f (Term f1 tt1) (Term f2 tt2) | f1 == f2 = zipWithM_ f tt1 tt2
                                           | otherwise = fail "structure mismatch"

instance HasId (TermF id) id where getId (Term id _) = Just id
instance MapId TermF where mapId f (Term id tt) = Term (f id) tt

-- Functor boilerplate
-- --------------------
instance Functor (TermF id) where
    fmap     f (Term a tt) = Term a (fmap f tt)
instance Foldable (TermF id) where
    foldMap  f (Term _ tt) = foldMap f tt
instance Traversable (TermF id) where
    traverse f (Term a tt) = Term a `fmap` traverse f tt

instance Bifunctor TermF where
    bimap f g (Term id tt) = Term (f id) (fmap g tt)