{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}

module Data.Term.Rewriting (
      isNF, isNFo,
 -- * One step
      rewrite1, rewrite1', rewrite1p, rewriteStep,
      rewrite1O, rewrite1O', rewrite1pO, rewriteStepO,
 -- * Big step
      rewrites, rewritesO, reduce
 ) where

import Control.Applicative
#ifdef LOGICT
import Control.Monad.Logic
#endif
import Control.Monad.State
import Data.List
import Data.Foldable as F
import Data.Traversable (Traversable)

import Control.Monad.Variant
import Data.Term hiding (Rule)
import Data.Term.Rules
import Data.Term.Utils

import Debug.Hoed.Observe

----------------------------------------
-- * Rewriting
----------------------------------------
{-# INLINABLE isNF #-}
isNF :: (Match t, Rename v, Ord v, Observable v, Observable(Term t v), Enum v) => [Rule t v] -> Term t v -> Bool
isNF = isNFo nilObserver
{-# INLINABLE isNFo #-}
isNFo :: (Match t, Rename v, Ord v, Observable v, Observable(Term t v), Enum v) => Observer -> [Rule t v] -> Term t v -> Bool
isNFo o rr = null . drop 1 . rewritesO o rr
--isNF rr = not . F.any (\t -> F.any ((`matches` t) . lhs) rr) . subterms


rewrite1 :: (Ord v, Observable v, Enum v, Rename v, Match t, Traversable t, Observable(Term t v), MonadPlus m) => [Rule t v] -> Term t v -> m(Term t v)
rewrite1 = rewrite1O nilObserver

rewrite1O :: (Ord v, Observable v, Enum v, Rename v, Match t, Traversable t, Observable(Term t v), MonadPlus m) => Observer -> [Rule t v] -> Term t v -> m(Term t v)
rewrite1O o rr t = runVariantT' freshvars (snd `liftM` rewriteStepO o rr t)
  where freshvars = [toEnum 0 ..] \\ vars t

rewrite1' :: (Ord v, Observable v, Enum v, Rename v, Match t, Traversable t, Observable(Term t v), MonadPlus m) => [Rule t v] -> Term t v -> m(Position, Term t v)
rewrite1' = rewrite1O' nilObserver

rewrite1O' :: (Ord v, Observable v, Enum v, Rename v, Match t, Traversable t, Observable(Term t v), MonadPlus m) => Observer -> [Rule t v] -> Term t v -> m(Position, Term t v)
rewrite1O' o rr t = runVariantT' freshvars $ rewriteStepO o rr t
  where freshvars = [toEnum 0 ..] \\ vars t

rewrite1p :: (Ord v, Observable v, Enum v, Rename v, Match t, Traversable t, Observable(Term t v), MonadPlus m) => [Rule t v] -> Term t v -> Position -> m(Term t v)
rewrite1p = rewrite1pO nilObserver

rewrite1pO :: (Ord v, Observable v, Enum v, Rename v, Match t, Traversable t, Observable(Term t v), MonadPlus m) => Observer -> [Rule t v] -> Term t v -> Position -> m(Term t v)
rewrite1pO o rr t p = liftM fst $ updateAtM p (rewriteTopO o rr) t

-- | Reflexive, Transitive closure
rewrites :: (Ord v, Observable v, Enum v, Rename v, Match t, Traversable t, Observable(Term t v), MonadPlus m) => [Rule t v] -> Term t v -> m (Term t v)
rewrites = rewritesO nilObserver
-- | Reflexive, Transitive closure
rewritesO :: (Ord v, Observable v, Enum v, Rename v, Match t, Traversable t, Observable(Term t v), MonadPlus m) => Observer -> [Rule t v] -> Term t v -> m (Term t v)
rewritesO o rr t = runVariantT' freshvars $ closureMP (liftM snd . rewriteStepO o rr) t
  where freshvars = [toEnum 0 ..] \\ vars t

rewriteStep :: (Ord v, Observable v, Match t, Traversable t, Observable(Term t v), Rename v, v ~ Var m, MonadVariant m, MonadPlus m
               ) => [Rule t v] -> Term t v -> m (Position, Term t v)
rewriteStep rr = rewriteStepO nilObserver rr

rewriteStepO :: (Ord v, Observable v, Match t, Traversable t, Observable(Term t v), Rename v, v ~ Var m, MonadVariant m, MonadPlus m
               ) => Observer -> [Rule t v] -> Term t v -> m (Position, Term t v)
rewriteStepO o rr t = do
   rr' <- mapM getFresh rr
   someSubtermDeep (rewriteTopO o rr') t

rewriteTopO :: (MonadPlus m, Ord v, Observable v, Observable(Term t v), Match t
               ) => Observer -> [RuleF (Term t v)] -> Term t v -> m (Term t v)
rewriteTopO (O o _) rr t = F.msum $ forEach rr $ \r -> do
                              let lhs:->rhs = r
                              case o "match" match lhs t of
                                Just subst -> return (applySubst subst rhs)
                                Nothing -> mzero

#ifdef LOGICT
-- | Normal forms, starting from leftmost outermost
-- Assumes no extra variables in the rhs are present
reduce :: (Ord v, Observable v, Enum v, Rename v, Match t, Traversable t, Observable(Term t v), MonadLogic m
          ) => [Rule t v] -> Term t v -> m (Term t v)
reduce rr t = runVariantT' freshvars $ fixMP (liftM snd . rewriteStep rr) t
  where freshvars = [toEnum 0 ..] \\ vars t
#else
-- | Normal forms, starting from leftmost outermost
-- Assumes no extra variables in the rhs are present
reduce :: (Ord v, Observable v, Enum v, Rename v, Eq (Term t v), Traversable t, Observable(Term t v), Match t, MonadPlus m
          ) => [Rule t v] -> Term t v -> m (Term t v)
reduce rr t = runVariantT' freshvars $ fixM_Eq (liftM snd . rewriteStep rr) t
  where freshvars = [toEnum 0 ..] \\ vars t
#endif
