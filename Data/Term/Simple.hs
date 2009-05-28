module Data.Term.Simple where

import Control.Monad.Free
import Data.Foldable
import Data.Traversable
import Data.Term

data TermF id f = Term {id::id, args::[f]} deriving (Eq,Ord,Show)
data Var        = VName String | VAuto Int deriving (Eq, Ord, Show)

type Term1 id = Free (TermF id)

ident :: id -> Term1 id a
ident f = term f []

term :: id -> [Term1 id a] -> Term1 id a
term f = Impure . Term f


var :: Functor f =>  String -> Free f Var
var  = return . VName

var' :: Functor f => Int -> Free f Var
var' = return . VAuto

termId :: MonadPlus m => Term1 id a -> m id
termId = foldFree (const mzero) f where
    f (Term f tt) = return f `mplus` Data.Foldable.msum tt

-- Specific instance for TermF, only for efficiency
instance Eq id => Unify (TermF id) where
  {-# SPECIALIZE instance Unify (TermF String) #-}
  unify = unifyF where
   unifyF t s = do
    t' <- find' t
    s' <- find' s
    case (t', s') of
      (Pure vt, Pure vs) -> if vt /= vs then varBind vt s' else return ()
      (Pure vt, _)  -> {-if vt `Set.member` Set.fromList (vars s') then fail "occurs" else-} varBind vt s'
      (_, Pure vs)  -> {-if vs `Set.member` Set.fromList (vars t') then fail "occurs" else-} varBind vs t'
      (Impure t, Impure s) -> zipTermM_ unifyF t s
   zipTermM_ f (Term f1 tt1) (Term f2 tt2) | f1 == f2 = zipWithM_ f tt1 tt2
                                           | otherwise = fail "structure mismatch"

-- Functor boilerplate
-- --------------------
instance Functor (TermF id) where
    fmap     f (Term a tt) = Term a (fmap f tt)
instance Foldable (TermF id) where
    foldMap  f (Term _ tt) = foldMap f tt
instance Traversable (TermF id) where
    traverse f (Term a tt) = Term a `fmap` traverse f tt
