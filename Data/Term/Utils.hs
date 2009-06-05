{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
module Data.Term.Utils where

import Control.Monad hiding (mapM)
import Data.Foldable
import Data.Traversable as T
import Control.Monad.Trans (MonadTrans,lift)
import Control.Monad.Identity(Identity(..))
import Control.Monad.State(StateT(..), MonadState, get, put, modify, evalStateT)
#ifdef LOGICT
import Control.Monad.Logic (MonadLogic, ifte)
#endif

import Prelude hiding (mapM)

size :: Foldable f => f a -> Int
size = length . toList

interleaveM :: (Monad m, Traversable t) => (a -> m a) -> t a -> [m (t a)]
interleaveM f x = (liftM T.sequence) (interleave f return x)

interleave :: (Traversable f) => (a -> b) -> (a -> b) -> f a -> [f b]
interleave f def x = [unsafeZipWithG (indexed f i) [0..] x | i <- [0..size x - 1]]
  where indexed f i j x = if i==j then f x else def x

unsafeZipWithGM :: (Traversable t1, Traversable t2, Monad m) => (a -> b -> m c) -> t1 a -> t2 b -> m(t2 c)
unsafeZipWithGM f t1 t2  = evalStateT (mapM zipG' t2) (toList t1)
       where zipG' y = do (x:xx) <- get
                          put xx
                          lift (f x y)

unsafeZipWithG :: (Traversable t1, Traversable t2) => (a -> b -> c) -> t1 a -> t2 b -> t2 c
unsafeZipWithG f x y = runIdentity $ unsafeZipWithGM (\x y -> return (f x y)) x y

liftM2 :: (Monad m1, Monad m2) => (a -> b) -> m1(m2 a) -> m1(m2 b)
liftM2 = liftM.liftM

third :: (c -> c') -> (a,b,c) -> (a,b,c')
third f (a,b,c) = (a,b,f c)

firstM :: Monad m => (a -> m a') -> (a,b) -> m (a',b)
firstM f (x,y) = do { x' <- f x; return (x',y)}

secondM :: Monad m => (b -> m b') -> (a,b) -> m (a,b')
secondM f (x,y) = do { y' <- f y; return (x,y')}

forEach :: [a] -> (a -> b) -> [b]
forEach = flip map

-- ------------------------
-- Fixed points and similar
-- ------------------------
-- | transitive closure
closureMP :: MonadPlus m => (a -> m a) -> (a -> m a)
closureMP f x = return x `mplus` (f x >>= closureMP f)

#ifdef LOGICT
-- | least fixed point of a backtracking computation
fixMP :: MonadLogic m => (a -> m a) -> (a -> m a)
fixMP f x = ifte (f x) (fixMP f) (return x)
#endif

-- | least fixed point of a monadic function, using Eq comparison
fixM_Eq :: (Monad m, Eq a) => (a -> m a) -> a -> m a
fixM_Eq f = go (0::Int)  where
  go i prev_result = do
    x <- f prev_result
    if x == prev_result then return x
                        else go (i+1) x

----------------------
-- With...
{-# INLINE with #-}
{-# INLINE withSnd #-}
{-# INLINE withFst #-}
with :: (Monad m, MonadTrans t1, MonadState s (t1 m), MonadState s2 (t2 m)) =>
        (s -> s2) ->
        (s2 -> s -> s) ->
        (t2 m a -> s2 -> m (a,s2)) -> t2 m a -> t1 m a
with gets puts run m = do
      s <- gets `liftM` get
      (res,s') <- lift $ run m s
      modify (puts s')
      return res

withFst :: (MonadState (s, b) (t1 m), MonadTrans t1, Monad m) => StateT s m a -> t1 m a
withFst = with fst (\x' (x,y) -> (x',y)) runStateT
withSnd :: (MonadState (b, s) (t1 m), MonadTrans t1, Monad m) => StateT s m a -> t1 m a
withSnd = with snd (\y' (x,y) -> (x,y')) runStateT
