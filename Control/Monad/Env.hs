{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
module Control.Monad.Env where

import Control.Monad.List (ListT)
import Control.Monad.Logic (LogicT, LogicT, MonadLogic, msplit)
import Control.Monad.RWS (RWST)
import Control.Monad.Reader (ReaderT)
import Control.Monad.State (StateT)
import Control.Monad.Writer (WriterT)

import Control.Monad.Free
import Control.Monad.Logic
import Control.Monad.Variant

import Data.Monoid
import Data.Term.Base
import Data.Term.Family
import Data.Traversable (Traversable)
import qualified Data.Traversable as T

-- | Instances need only to define 'varBind' and 'lookupVar'
class Monad m => MonadEnv m where
    varBind   :: Var m -> Term (TermF m) (Var m) -> m ()
    lookupVar :: Var m -> m (Maybe (Term (TermF m) (Var m)))

    find      :: Var m -> m(Term (TermF m) (Var m))
    find v = do
      mb_t <- lookupVar v
      case mb_t of
        Just (Pure v') -> find v'
        Just t         -> varBind v t >> return t
        Nothing        -> return (Pure v)

    zonkM :: (Traversable (TermF m)) => (Var m -> m var') -> TermFor m -> m(Term (TermF m) var')
    zonkM fv = liftM join . T.mapM f where
        f v = do mb_t <- lookupVar v
                 case mb_t of
                   Nothing -> Pure `liftM` fv v
                   Just t  -> zonkM fv t

find' :: MonadEnv m => Term (TermF m) (Var m) -> m(Term (TermF m) (Var m))
find' (Pure t) = find t
find' t        = return t

-- ------------------------------
-- Liftings of monadic operations
-- ------------------------------

--type instance Var  (MVariantT v m) = Var m
type instance TermF (MVariantT v m) = TermF m
instance (Functor (TermF m), v ~ Var m, MonadEnv m) => MonadEnv (MVariantT v m) where
  varBind   = (lift.) . varBind
  lookupVar = lift . lookupVar

type instance TermF (WrappedMVariant v v' m) = TermF m
instance (MonadEnv m, v' ~ Var m) => MonadEnv (WrappedMVariant v v' m) where
  varBind = (lift.) . varBind
  lookupVar = lift . lookupVar

type instance TermF (WriterT w m) = TermF m
type instance Var  (WriterT w m) = Var m
instance (Monoid w, Functor (TermF m), MonadEnv m) => MonadEnv (WriterT w m) where
  varBind   = (lift.) . varBind
  lookupVar = lift . lookupVar

type instance TermF (ListT m) = TermF m
type instance Var  (ListT m) = Var m
instance MonadEnv m => MonadEnv (ListT m) where
  varBind   = (lift.) . varBind
  lookupVar = lift    . lookupVar

type instance TermF (StateT s m) = TermF m
type instance Var  (StateT s m) = Var m
instance (Functor (TermF m), MonadEnv m) => MonadEnv (StateT s m) where
  varBind   = (lift.) . varBind
  lookupVar = lift . lookupVar

type instance TermF (ReaderT r m) = TermF m
type instance Var  (ReaderT r m) = Var m
instance (Functor (TermF m), MonadEnv m) => MonadEnv (ReaderT r m) where
  varBind   = (lift.) . varBind
  lookupVar = lift . lookupVar

type instance TermF (RWST r w s m) = TermF m
type instance Var  (RWST r w s m) = Var m
instance (Monoid w, Functor (TermF m), MonadEnv m) => MonadEnv (RWST r w s m) where
  varBind = (lift.) . varBind
  lookupVar = lift . lookupVar
