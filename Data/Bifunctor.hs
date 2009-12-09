{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Bifunctor where

import Control.Monad.Identity

class Bifunctor b where bimap :: (u->v) -> (s->t) -> b u s -> b v t
{-
instance Bifunctor Either where
    bimap l _ (Left  x) = Left  (l x)
    bimap _ r (Right x) = Right (r x)
-}
class BifunctorM b where bimapM :: Monad m => (u -> m v) -> (s -> m t) -> b u s -> m(b v t)
instance BifunctorM Either where
    bimapM l _ (Left  x) = Left  `liftM` l x
    bimapM _ r (Right x) = Right `liftM` r x

bimapDefault l r = runIdentity  . bimapM (return.l) (return.r)

instance BifunctorM b => Bifunctor b where bimap = bimapDefault

data BiFix b x = BiIn (b x (BiFix b x))

bifold :: Bifunctor b => (b x t -> t) -> BiFix b x -> t
bifold phi (BiIn s) = phi (bimap id (bifold phi) s)

instance Bifunctor b => Functor (BiFix b) where
  fmap f (BiIn s) = BiIn (bimap f (fmap f) s)

instance Bifunctor b => Functor (b a) where fmap = bimap id