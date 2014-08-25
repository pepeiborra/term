{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE OverlappingInstances, UndecidableInstances, FlexibleContexts #-}
module Data.Term.IOVar where

import Control.Applicative
import Control.Arrow
import qualified Control.Exception as CE
import Control.Monad.Env
import Control.Monad.Trans
import Control.Monad.Free
import Control.Monad.Variant
import qualified Control.Monad.Variant as MonadVariant
import Data.Foldable(Foldable)
import Data.IOStableRef
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Var.Family as Family
import Data.Term.Family
import Data.Term.Substitutions
import Data.Traversable as T
import qualified Prelude as P
import Prelude

import Debug.Hoed.Observe

newtype IOVar termF = IOVar (IOStableRef( Maybe (Free termF (IOVar termF)))) deriving (Eq,Ord, Show)


unifiesIO :: (Unify t, Eq (IOVar t)) => Free t (IOVar t) -> Free t (IOVar t) -> TIO t Bool
unifiesIO t u = (unifyM t u >> return True) `catch` \(_ :: CE.SomeException) -> return False

matchesIO :: (Unify t, Eq (IOVar t)) => Free t (IOVar t) -> Free t (IOVar t) -> TIO t Bool
matchesIO t u = (matchM t u >> return True) `catch` \(_ :: CE.SomeException) -> return False

instantiate :: (term ~ TermF m, Var m ~ Either var (IOVar term), Traversable term, MonadVariant m, MonadEnv m) =>
               Free term var -> m (Free term (IOVar term))
instantiate t = (liftM.fmap) (\(Right x) -> x)
                             (freshWith (flip const)
                                        (fmap Left t))

getInst :: (Traversable t, Ord var, Observable var, Eq (Free t (IOVar t))) =>
           Substitution t (Either var (IOVar t)) -> TIO t (Substitution t var)
getInst (unSubst -> s) = do
    map0' <- P.mapM (secondM (zonkM (\v -> let Just v' = lookup (Pure v) inversemap in return v'))) map0
    return $ fromListSubst map0'
 where
    map0       = map (fromLeft *** fmap fromRight) (Map.toList s)
    inversemap = [(b,a) | (a,b) <- map0]
    fromRight  = either (error "getInst") id
    fromLeft   = either id (error "getInst")
    secondM f (a,b) = f b >>= \b' -> return (a,b')

instance Rename (IOVar t) where rename _ = id

newtype TIO (t :: * -> *) a = TIO {tio::IO a} deriving (Applicative, Functor, Monad, MonadIO)

catch m h = TIO (CE.catch (tio m) (tio.h))

type instance Var   (TIO t) = IOVar t
type instance TermF (TIO t) = t
instance Traversable t => MonadEnv (TIO t) where
  varBind (IOVar v) t = liftIO $ writeIOStableRef v (Just t)
  lookupVar (IOVar v) = liftIO $ readIOStableRef  v

type instance Family.Var (TIO t) = IOVar t
instance MonadVariant (TIO t) where
  freshVar = IOVar `liftM` liftIO(newIOStableRef Nothing)
  renaming _ = freshVar

type instance Var (IOVar t) = IOVar t
instance GetVars (IOVar t) where
  getVars = Set.singleton
  fromVar = id

instance Observable (IOVar a) where observer = observeOpaque "IOVar"
