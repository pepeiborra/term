{-# LANGUAGE CPP #-}
module Data.Term.Rewriting where

#ifdef LOGICT
import Control.Monad.Logic
#endif
import Control.Monad.State
import Data.List
import Data.Foldable as F

import Data.Term
import Data.Term.Rules
import Data.Term.Utils

----------------------------------------
-- * Rewriting
----------------------------------------

rewrite1 :: (Ord v, Enum v, Match t, MonadPlus m) => [Rule t v] -> Term t v -> m(Term t v)
rewrite1 rr t = rewriteStep rr t `evalStateT` freshvars
  where freshvars = [toEnum 0 ..] \\ vars t

-- | Reflexive, Transitive closure
rewrites :: (Ord v, Enum v, Match t, MonadPlus m) => [Rule t v] -> Term t v -> m (Term t v)
rewrites rr t = closureMP (rewriteStep rr) t `evalStateT` freshvars
  where freshvars = [toEnum 0 ..] \\ vars t

rewriteStep :: (Ord v, Match t, MonadFresh v m, MonadPlus m) => [Rule t v] -> Term t v -> m (Term t v)
rewriteStep rr t = do
   rr' <- mapM getFresh rr
   let rewriteTop t = F.msum $ forEach rr' $ \r -> do
                          lhs:->rhs <- return r
                          case match lhs t of
                               Just subst -> return (applySubst subst rhs)
                               Nothing -> mzero
       go t = rewriteTop t `mplus` someSubterm go t
   go t

#ifdef LOGICT
-- | Normal forms, starting from leftmost outermost
-- Assumes no extra variables in the rhs are present
reduce :: (Ord v, Enum v, Match t, MonadLogic m) => [Rule t v] -> Term t v -> m (Term t v)
reduce rr t = fixMP (rewriteStep rr) t `evalStateT` freshvars
  where freshvars = [toEnum 0 ..] \\ vars t
#else
-- | Normal forms, starting from leftmost outermost
-- Assumes no extra variables in the rhs are present
reduce :: (Ord v, Enum v, Eq (Term t v), Match t, MonadPlus m) => [Rule t v] -> Term t v -> m (Term t v)
reduce rr t = fixM_Eq (rewriteStep rr) t `evalStateT` freshvars
  where freshvars = [toEnum 0 ..] \\ vars t
#endif
