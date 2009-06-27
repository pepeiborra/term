module Data.Bifunctor where

class Bifunctor b where bimap :: (u->v) -> (s->t) -> b u s ->b v t
instance Bifunctor Either where
    bimap l _ (Left  x) = Left  (l x)
    bimap _ r (Right x) = Right (r x)

data BiFix b x = BiIn (b x (BiFix b x))

bifold :: Bifunctor b => (b x t -> t) -> BiFix b x -> t
bifold phi (BiIn s) = phi (bimap id (bifold phi) s)

instance Bifunctor b => Functor (BiFix b) where
  fmap f (BiIn s) = BiIn (bimap f (fmap f) s)

instance Bifunctor b => Functor (b a) where fmap = bimap id