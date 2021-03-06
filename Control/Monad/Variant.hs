{-# LANGUAGE CPP #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Control.Monad.Variant (
    Rename(..),
    MonadVariant(..),
    MVariantT(..), runVariantT, runVariantT', runVariant, runVariant',
    WrappedMVariant, variantsWith
    )where

import Control.Applicative
import Control.Monad.Identity
import Control.Monad.List
#ifdef LOGICT
import Control.Monad.Logic
#endif
import Control.Monad.State.Strict
import Control.Monad.RWS
import Control.Monad.Writer

import Data.Term.Family

import Debug.Hoed.Observe

-- type Var m

-- | Renaming of variables
class Rename v where
    rename :: v      -- ^ Original variable
           -> v      -- ^ Fresh variable
           -> v      -- ^ Result of renaming the original variable to the fresh variable

instance (Rename v, Rename v') => Rename (Either v v') where
  rename (Left v) (Left v') = Left (rename v v')
  rename (Right v) (Right v') = Right (rename v v')
  rename _ _ = error "rename: incompatible variables"

class (Rename (Var m), Monad m) => MonadVariant m where
    -- | Returns a fresh variable
    freshVar :: m (Var m)
    -- | Renames with a fresh variable
    renaming :: Var m-> m (Var m)
    renaming v = do {v' <- freshVar; return $ rename v v'}

-- * A Monad
newtype MVariantT v m a = MVariant {unMVariant :: StateT [v] m a} deriving (Applicative, Alternative, Functor, Monad, MonadTrans, MonadPlus)
type MVariant v a = MVariantT v Identity a

type instance Var (MVariantT v m) = v
instance (Rename v, Monad m) => MonadVariant (MVariantT v m) where
    freshVar = do { x:xx <- MVariant get; MVariant(put xx); return x}


#ifdef LOGICT
--deriving instance (MonadLogic m) => MonadLogic (MVariantT v m)
instance MonadLogic m => MonadLogic (MVariantT v m) where
  msplit m = MVariant $ (liftM.liftM) f (msplit (unMVariant m)) where
   f (a,m') = (a, MVariant m')

type instance Var   (LogicT m) = Var m
type instance TermF (LogicT m) = TermF m
instance MonadVariant m => MonadVariant (LogicT m) where freshVar = lift freshVar
#endif

-- | Runs a computation over the given set of fresh variables
runVariantT' :: Monad m => [v] -> MVariantT v m a -> m a
runVariantT' vars = (`evalStateT` vars) . unMVariant

-- | Runs a computation over the set of all variables enumerated from 0 onwards
runVariantT :: (Monad m, Enum v) => MVariantT v m a -> m a
runVariantT = runVariantT' (map toEnum [0..])

-- | Runs a computation over the given set of fresh variables
runVariant' :: [v] -> MVariant v a -> a
runVariant' vars = runIdentity . runVariantT' vars

-- | Runs a computation over the set of all variables enumerated from 0 onwards
runVariant :: Enum v => MVariant v a -> a
runVariant = runVariant' [toEnum 0..]

instance (Monad m) => Observable1 (MVariantT v m) where
  observer1 = observeComp "<MvariantT>"

instance (Observable a, Monad m) => Observable(MVariantT v m a) where
  observer = observer1
  observers = observers1

observeComp name comp p = do
    res <- comp
    send name (return return << res) p

-- * A rebranding function
-- | Applies the Yoneda transformation over MonadVariant
newtype WrappedMVariant v v' m a = WrappedMVariant {unwrapMVariant :: (v -> v') -> m a}

instance Monad m => Functor(WrappedMVariant v v' m) where
  fmap = liftM

instance Monad m => Applicative(WrappedMVariant v v' m) where
  pure = return
  (<*>) = ap

instance Monad m => Monad(WrappedMVariant v v' m) where
  return x = WrappedMVariant (\_ -> return x)
  m >>= k = WrappedMVariant (\f -> unwrapMVariant m f >>= ((`unwrapMVariant` f) . k))

instance MonadTrans (WrappedMVariant v v') where
  lift m = WrappedMVariant (\_ -> m)

type instance Var   (WrappedMVariant v v' m) = v'

instance (MonadVariant m, Rename v', v ~ Var m) => MonadVariant (WrappedMVariant v v' m) where
  freshVar = WrappedMVariant ( `liftM` freshVar)

-- variantsWith :: (MonadVariant m, Var m ~ v') => (v -> v') -> m a -> MVariantT v m a
-- | Applies a morphism on the source of fresh variables of a MonadVariant computation
variantsWith = flip unwrapMVariant -- f m = unwrapMVariant (WrappedMVariant m) f


-- * Some instances

-- instance (Rename v, Monad m) => MonadVariant (StateT [v] m) where
--     type Var (StateT [v] m) = v


-- instance (Rename v, Monad m) => MonadVariant (StateT (a,[v]) m) where
--     type Var (StateT (a,[v]) m) = v
--     freshVar = withSnd freshVar



-- instance (Monoid w, Rename v, Monad m) => MonadVariant (RWST r w [v] m) where
--     type Var (RWST r w [v] m) = v
--     freshVar = do { x:xx <- get; put xx; return x}

-- * Propagation

type instance (Var (ListT m)) = Var m
instance MonadVariant m => MonadVariant (ListT m) where
  freshVar = lift freshVar
  renaming = lift . renaming

type instance Var (StateT s m) = Var m
instance MonadVariant m => MonadVariant (StateT s m) where
  freshVar = lift freshVar
  renaming = lift . renaming

type instance Var (RWST r w s m) = Var m
instance (Monoid w, MonadVariant m) => MonadVariant (RWST r w s m) where
  freshVar = lift freshVar
  renaming = lift . renaming

type instance Var (WriterT w m) = Var m
instance (MonadVariant m,Monoid w) => MonadVariant (WriterT w m) where
  freshVar = lift freshVar
  renaming = lift . renaming

