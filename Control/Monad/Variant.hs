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
    WrappedMVariant, variantsWith,
    VarM
    )where

import Control.Applicative
import Control.Monad.Identity
import Control.Monad.List
#ifdef LOGICT
import Control.Monad.Logic
#endif
import Control.Monad.State
import Control.Monad.RWS
import Control.Monad.Writer
import Data.Monoid

import Data.Term.Family
import Data.Var.Family
-- type VarM m

-- | Renaming of variables
class Rename v where
    rename :: v      -- ^ Original variable
           -> v      -- ^ Fresh variable
           -> v      -- ^ Result of renaming the original variable to the fresh variable

instance (Rename v, Rename v') => Rename (Either v v') where
  rename (Left v) (Left v') = Left (rename v v')
  rename (Right v) (Right v') = Right (rename v v')
  rename _ _ = error "rename: incompatible variables"

class (Rename (VarM m), Monad m) => MonadVariant m where
    freshVar :: m (VarM m)
    renaming :: VarM m-> m (VarM m)
    renaming v = do {v' <- freshVar; return $ rename v v'}

-- * A Monad
newtype MVariantT v m a = MVariant {unMVariant :: StateT [v] m a} deriving (Applicative, Functor, Monad, MonadTrans, MonadPlus)
type MVariant v a = MVariantT v Identity a

type instance VarM (MVariantT v m) = v
instance (Enum v, Rename v, Monad m) => MonadVariant (MVariantT v m) where
    freshVar = do { x:xx <- MVariant get; MVariant(put xx); return x}


#ifdef LOGICT
deriving instance (MonadLogic m) => MonadLogic (MVariantT v m)
type instance VarM   (LogicT m) = VarM m
type instance TermFM (LogicT m) = TermFM m
instance MonadVariant m => MonadVariant (LogicT m) where freshVar = lift freshVar
#endif

runVariantT' :: Monad m => [v] -> MVariantT v m a -> m a
runVariantT' vars = (`evalStateT` vars) . unMVariant

runVariantT :: (Monad m, Enum v) => MVariantT v m a -> m a
runVariantT = runVariantT' (map toEnum [0..])

runVariant' :: [v] -> MVariant v a -> a
runVariant' vars = runIdentity . runVariantT' vars

runVariant :: Enum v => MVariant v a -> a
runVariant = runVariant' [toEnum 0..]

-- * A rebranding function

newtype WrappedMVariant v v' m a = WrappedMVariant {unwrapMVariant :: (v -> v') -> m a}

instance Monad m => Monad(WrappedMVariant v v' m) where
  return x = WrappedMVariant (\_ -> return x)
  m >>= k = WrappedMVariant (\f -> unwrapMVariant m f >>= ((`unwrapMVariant` f) . k))

instance MonadTrans (WrappedMVariant v v') where
  lift m = WrappedMVariant (\_ -> m)

type instance VarM   (WrappedMVariant v v' m) = v'

instance (MonadVariant m, Rename v', v ~ VarM m) => MonadVariant (WrappedMVariant v v' m) where
  freshVar = WrappedMVariant ( `liftM` freshVar)

-- variantsWith :: (MonadVariant m, VarM m ~ v') => (v -> v') -> m a -> MVariantT v m a
variantsWith = flip unwrapMVariant -- f m = unwrapMVariant (WrappedMVariant m) f


-- * Some instances

-- instance (Rename v, Monad m) => MonadVariant (StateT [v] m) where
--     type VarM (StateT [v] m) = v


-- instance (Rename v, Monad m) => MonadVariant (StateT (a,[v]) m) where
--     type VarM (StateT (a,[v]) m) = v
--     freshVar = withSnd freshVar



-- instance (Monoid w, Rename v, Monad m) => MonadVariant (RWST r w [v] m) where
--     type VarM (RWST r w [v] m) = v
--     freshVar = do { x:xx <- get; put xx; return x}

-- * Propagation

type instance (VarM (ListT m)) = VarM m
instance MonadVariant m => MonadVariant (ListT m) where
  freshVar = lift freshVar
  renaming = lift . renaming

type instance VarM (StateT s m) = VarM m
instance MonadVariant m => MonadVariant (StateT s m) where
  freshVar = lift freshVar
  renaming = lift . renaming

type instance VarM (RWST r w s m) = VarM m
instance (Monoid w, MonadVariant m) => MonadVariant (RWST r w s m) where
  freshVar = lift freshVar
  renaming = lift . renaming

type instance VarM (WriterT w m) = VarM m
instance (MonadVariant m,Monoid w) => MonadVariant (WriterT w m) where
  freshVar = lift freshVar
  renaming = lift . renaming

