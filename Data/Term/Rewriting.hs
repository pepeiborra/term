{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}

module Data.Term.Rewriting (
 -- * One step
      rewrite1, rewrite1', rewrite1p,
 -- * Big step
      rewrites, reduce
 ) where

import Control.Applicative
#ifdef LOGICT
import Control.Monad.Logic
#endif
import Control.Monad.State
import Data.List
import Data.Foldable as F

import Control.Monad.Variant
import Data.Term
import Data.Term.Rules
import Data.Term.Utils

----------------------------------------
-- * Rewriting
----------------------------------------

rewrite1 :: (Ord v, Enum v, Rename v, Match t, MonadPlus m) => [Rule t v] -> Term t v -> m(Term t v)
rewrite1 rr t = runVariantT' freshvars (snd `liftM` rewriteStep rr t)
  where freshvars = [toEnum 0 ..] \\ vars t

rewrite1' :: (Ord v, Enum v, Rename v, Match t, MonadPlus m) => [Rule t v] -> Term t v -> m(Position, Term t v)
rewrite1' rr t = runVariantT' freshvars $ rewriteStep rr t
  where freshvars = [toEnum 0 ..] \\ vars t

rewrite1p :: (Ord v, Enum v, Rename v, Match t, MonadPlus m) => [Rule t v] -> Term t v -> Position -> m(Term t v)
rewrite1p rr t p = liftM fst $ updateAtM p (rewriteTop rr) t

-- | Reflexive, Transitive closure
rewrites :: (Ord v, Enum v, Rename v, v ~ VarM m, Match t, MonadPlus m) => [Rule t v] -> Term t v -> m (Term t v)
rewrites rr t = runVariantT' freshvars $ closureMP (liftM snd . rewriteStep rr) t
  where freshvars = [toEnum 0 ..] \\ vars t

rewriteStep :: (Ord v, Match t, Rename v, v ~ VarM m, MonadVariant m, MonadPlus m) => [Rule t v] -> Term t v -> m (Position, Term t v)
rewriteStep rr t = do
   rr' <- mapM getFresh rr
   someSubtermDeep (rewriteTop rr') t

rewriteTop rr t = F.msum $ forEach rr $ \r -> do
                          lhs:->rhs <- return r
                          case match lhs t of
                               Just subst -> return (applySubst subst rhs)
                               Nothing -> mzero

#ifdef LOGICT
-- | Normal forms, starting from leftmost outermost
-- Assumes no extra variables in the rhs are present
reduce :: (Ord v, Enum v, Rename v, Match t, MonadLogic m) => [Rule t v] -> Term t v -> m (Term t v)
reduce rr t = runVariantT' freshvars $ fixMP (liftM snd . rewriteStep rr) t
  where freshvars = [toEnum 0 ..] \\ vars t
#else
-- | Normal forms, starting from leftmost outermost
-- Assumes no extra variables in the rhs are present
reduce :: (Ord v, Enum v, Rename v, Eq (Term t v), Match t, MonadPlus m) => [Rule t v] -> Term t v -> m (Term t v)
reduce rr t = runVariantT' freshvars $ fixM_Eq (liftM snd . rewriteStep rr) t
  where freshvars = [toEnum 0 ..] \\ vars t
#endif
