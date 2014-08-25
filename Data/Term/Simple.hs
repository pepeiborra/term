{-# LANGUAGE FlexibleInstances, OverlappingInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveGeneric #-}

module Data.Term.Simple (TermF(..), Term1, constant, term, termId) where

import Control.Applicative
import Control.Applicative.Compose
import Control.DeepSeq
import Control.DeepSeq.Extras
import Control.Monad.Free
import Data.Bifunctor
import Data.Char (isAlpha)
import Data.Foldable (Foldable(..), msum)
import Data.Term.Substitutions
import Data.Traversable
import Prelude.Extras
import Text.PrettyPrint.HughesPJClass

import qualified Data.Id.Family as Family
import Data.Term hiding (TermF)
import Data.Monoid (Monoid(..))

import Debug.Hoed.Observe

data TermF id f = Term {id::id, args::[f]} deriving (Eq,Ord,Show,Generic)
type Term1 id = Free (TermF id)

instance Eq id => Eq1 (TermF id) where (==#) = (==)
instance Ord id => Ord1 (TermF id) where compare1 = compare
instance Show id => Show1 (TermF id) where showsPrec1 = showsPrec

type instance Family.Id (TermF id) = id

term :: id -> [Term1 id a] -> Term1 id a
term f = Impure . Term f

constant :: id -> Term1 id a
constant f = term f []

termId :: MonadPlus m => Term1 id a -> m id
termId = foldFree (const mzero) f where
    f (Term f tt) = return f `mplus` Data.Foldable.msum tt

instance (Eq id) => Applicative (Maybe :+: TermF id) where
  pure _ = Compose Nothing
  Compose(Just(Term a ff)) <*> Compose(Just(Term b xx))
    | a == b = Compose $ Just $ Term a (zipWith ($) ff xx)
  _ <*> _ = Compose Nothing

-- Specific instance for TermF, only for efficiency
instance Ord id => Unify (TermF id) where
  {-# SPECIALIZE instance Unify (TermF String) #-}
  unifyM = unifyF where
   unifyF t s = do
    t' <- find' t
    s' <- find' s
    case (t', s') of
      (Pure vt, Pure vs) -> when(vt /= vs) $ varBind vt s'
      (Pure vt, _)  -> varBind vt s'
      (_, Pure vs)  -> varBind vs t'
      (Impure t, Impure s) -> zipTermM_ unifyF t s
   zipTermM_ f (Term f1 tt1) (Term f2 tt2) | f1 == f2 = zipWithM_ f tt1 tt2
                                           | otherwise = fail "structure mismatch"

instance Ord id =>  HasId1 (TermF id) where
    getId1 (Term id _) = Just id
    fromId1 id = Term id []

instance MapId TermF where
    mapIdM f (Term id tt) = (`Term` tt) <$> f id

instance (Pretty a, Pretty id) => Pretty (TermF id a) where
    pPrint (Term n []) = pPrint n
    pPrint (Term n [x,y]) | not (any isAlpha $ show $ pPrint n) = pPrint x <+> pPrint n <+> pPrint y
    pPrint (Term n tt) = pPrint n <> parens (hcat$ punctuate comma$ map pPrint tt)

instance Pretty a => Pretty (TermF String a) where
    pPrint (Term n []) = text n
    pPrint (Term n [x,y]) | not (any isAlpha n) = pPrint x <+> text n <+> pPrint y
    pPrint (Term n tt) = text n <> parens (hcat$ punctuate comma $ map pPrint tt)

-- Functor boilerplate
-- --------------------
instance Functor (TermF id) where
    fmap     f (Term a tt) = Term a (fmap f tt)
instance Foldable (TermF id) where
    foldMap  f (Term _ tt) = foldMap f tt
instance Traversable (TermF id) where
    traverse f (Term a tt) = Term a `fmap` traverse f tt

instance Bifunctor TermF where
    bimap f g (Term id tt) = Term (f id) (fmap g tt)

instance Observable id => Observable1 (TermF id)

instance NFData id => NFData1 (TermF id) where
  rnf1 (Term id tt) = rnf id `seq` rnf tt
