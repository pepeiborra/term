{-# LANGUAGE FlexibleContexts, ConstraintKinds #-}
{-# LANGUAGE DeriveGeneric, DeriveDataTypeable #-}

module Data.Term.Automata
   (TermMatcher, singleton, insert, createMatcher, match
   ) where

import Data.Foldable as F
import qualified Data.Map as Map
import Data.Map.Strict (Map)
import Data.Monoid (Monoid(..))
import Data.Term
import Data.Term.Rules
import Data.Typeable
import GHC.Generics

-- -------------------------------------------
-- Fast normal form checking via Tree automata
-- -------------------------------------------

data TermMatcher a = Any
                   | OneOf (Map a (TermMatcher a))
                   deriving (Eq, Ord, Show, Generic, Typeable)

instance Ord a => Monoid (TermMatcher a) where
  mempty = OneOf Map.empty
  mappend Any _ = Any
  mappend _ Any = Any
  mappend (OneOf m1) (OneOf m2) = OneOf (Map.unionWith mappend m1 m2)

type FastMatch t = (Functor t, HasId1 t, Foldable t, Ord (Id t))

singleton :: FastMatch t => Term t v -> TermMatcher(Id t)
singleton = foldTerm fv ft where
  ft t
    | Just i <- getId1 t =
      OneOf (Map.singleton i (fold t))
    | otherwise = OneOf Map.empty
  fv _ = Any

insert :: FastMatch t => Term t v -> TermMatcher (Id t) -> TermMatcher(Id t)
insert t m = singleton t `mappend` m

-- | Returns true if the term does not match any in the set of terms modelled by the matcher
isNF :: FastMatch t => Term t v -> TermMatcher (Id t) -> Bool
isNF = (not.) . foldTerm fv ft where
  fv _ Any = True
  fv _ _   = False

  ft t Any = True
  ft t (OneOf m) =
    case getId1 t >>= \i -> Map.lookup i m of
      Nothing -> False
      Just m' -> F.or $ (fmap ($ m') t)

-- | Given a left-linear TRS, returns a model of the normal forms of the TRS
createMatcher :: FastMatch t => [Rule t v] -> TermMatcher (Id t)
createMatcher = Prelude.foldr insert mempty . map lhs
