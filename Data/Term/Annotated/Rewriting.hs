{-# LANGUAGE CPP #-}
module Data.Term.Annotated.Rewriting (
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

import Data.Term.Annotated
import Data.Term.Annotated.Rules
import Data.Term.Utils

----------------------------------------
-- * Rewriting
----------------------------------------

rewrite1 :: (Ord v, Enum v, Rename v, Measured v ann, Match t, MonadPlus m) => [Rule ann t v] -> Term ann t v -> m(Term ann t v)
rewrite1 rr t = (snd `liftM` rewriteStep rr t) `evalStateT` freshvars
  where freshvars = [toEnum 0 ..] \\ vars t

rewrite1' :: (Ord v, Enum v, Rename v, Measured v ann, Match t, MonadPlus m) => [Rule ann t v] -> Term ann t v -> m(Position, Term ann t v)
rewrite1' rr t = rewriteStep rr t `evalStateT` freshvars
  where freshvars = [toEnum 0 ..] \\ vars t

rewrite1p :: (Ord v, Enum v, Rename v, Measured v ann, Match t, MonadPlus m) => [Rule ann t v] -> Term ann t v -> Position -> m(Term ann t v)
rewrite1p rr t p = liftM fst $ updateAtM p (rewriteTop rr) t

-- | Reflexive, Transitive closure
rewrites :: (Ord v, Enum v, Rename v, Measured v ann, Match t, MonadPlus m) => [Rule ann t v] -> Term ann t v -> m (Term ann t v)
rewrites rr t = closureMP (liftM snd . rewriteStep rr) t `evalStateT` freshvars
  where freshvars = [toEnum 0 ..] \\ vars t

rewriteStep :: (Ord v, Match t, Rename v, Measured v ann, MonadVariant v m, MonadPlus m) => [Rule ann t v] -> Term ann t v -> m (Position, Term ann t v)
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
reduce :: (Ord v, Enum v, Rename v, Measured v ann, Match t, MonadLogic m) => [Rule ann t v] -> Term ann t v -> m (Term ann t v)
reduce rr t = fixMP (liftM snd . rewriteStep rr) t `evalStateT` freshvars
  where freshvars = [toEnum 0 ..] \\ vars t
#else
-- | Normal forms, starting from leftmost outermost
-- Assumes no extra variables in the rhs are present
reduce :: (Ord v, Enum v, Rename v, Measured v ann, Eq (Term ann t v), Match t, MonadPlus m) => [Rule ann t v] -> Term ann t v -> m (Term ann t v)
reduce rr t = fixM_Eq (liftM snd . rewriteStep rr) t `evalStateT` freshvars
  where freshvars = [toEnum 0 ..] \\ vars t
#endif
