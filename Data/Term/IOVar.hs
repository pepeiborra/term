{-# LANGUAGE OverlappingInstances, UndecidableInstances, FlexibleContexts #-}
module Data.Term.IOVar where

import Control.Arrow
import Control.Monad.Free
import Data.IOStableRef
import qualified Data.Map as Map
import Data.Term
import Data.Traversable as T
import Prelude as P

newtype IOVar termF = IOVar (IOStableRef( Maybe (Free termF (IOVar termF)))) deriving (Eq,Ord, Show)


unifiesIO :: (Unify t, Eq (IOVar t)) => Free t (IOVar t) -> Free t (IOVar t) -> IO Bool
unifiesIO t u = (unifyM t u >> return True) `catch` \_ -> return False

matchesIO :: (Match t, Eq (IOVar t)) => Free t (IOVar t) -> Free t (IOVar t) -> IO Bool
matchesIO t u = (matchM t u >> return True) `catch` \_ -> return False

instantiate :: (Traversable term,
                MonadFresh (IOVar term) m, MonadEnv term (Either var (IOVar term)) m) =>
               Free term var -> m (Free term (IOVar term))
instantiate = fresh'

getInst :: (Traversable t, Ord var,  Eq (Free t (IOVar t))) =>
           Substitution t (Either var (IOVar t)) -> IO (Substitution t var)
getInst (Subst s) = do
    map0' <- P.mapM (secondM (zonkM (\v -> let Just v' = lookup (Pure v) inversemap in return v'))) map0
    return $ fromList map0'
 where
    map0       = map (fromLeft *** fmap fromRight) (Map.toList s)
    inversemap = [(b,a) | (a,b) <- map0]
    fromRight  = either (error "getInst") id
    fromLeft   = either id (error "getInst")
    secondM f (a,b) = f b >>= \b' -> return (a,b')

instance Traversable termF => MonadEnv termF (IOVar termF) IO where
  varBind (IOVar v) t = writeIOStableRef v (Just t)
  lookupVar (IOVar v) = readIOStableRef  v

instance MonadFresh (IOVar termF) IO where
  freshVar = IOVar `liftM` newIOStableRef Nothing