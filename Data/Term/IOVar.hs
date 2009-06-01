{-# LANGUAGE OverlappingInstances, UndecidableInstances, FlexibleContexts #-}
module Data.Term.IOVar where

import Control.Monad.Free
import Data.IORef
import Data.Term
import Data.Traversable as T

newtype IOVar termF = IOVar (IORef( Maybe (Free termF (IOVar termF)))) deriving (Eq)

unifiesIO :: (Unify t, Eq (IOVar t)) => Free t (IOVar t) -> Free t (IOVar t) -> IO Bool
unifiesIO t u = (unify t u >> return True) `catch` \_ -> return False

matchesIO :: (Match t, Eq (IOVar t)) => Free t (IOVar t) -> Free t (IOVar t) -> IO Bool
matchesIO t u = (match t u >> return True) `catch` \_ -> return False

instance Traversable termF => MonadEnv termF (IOVar termF) IO where
  varBind (IOVar v) t = writeIORef v (Just t)
  lookupVar (IOVar v) = readIORef  v

instance MonadFresh (IOVar termF) IO where
  freshVar = IOVar `liftM` newIORef Nothing