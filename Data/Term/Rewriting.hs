{-# LANGUAGE CPP #-}
module Data.Term.Rewriting where

import Control.Applicative
import Control.Monad.Free
#ifdef LOGICT
import Control.Monad.Logic
#endif
import Control.Monad.State
import Data.List
import Data.Monoid
import Data.Foldable as F
import Data.Traversable (traverse, Traversable)
import qualified Data.Traversable as T

import Data.Term
import Data.Term.Rules
import Data.Term.Utils

-- ----------------
-- * Concrete rules
-- ----------------

data RuleF a = a :-> a deriving (Eq, Ord, Show)
instance Functor RuleF where fmap f (l :-> r) = f l :-> f r
instance Foldable RuleF where foldMap f (l :-> r) = f l `mappend` f r
instance Traversable RuleF where traverse f (l :-> r) = (:->) <$> f l <*> f r
instance Traversable t => GetFresh t v (Rule t v) where getFreshM = getFreshMdefault
instance (Eq v, Traversable t, Eq (t())) => GetUnifier t v (Rule t v) where getUnifierM = getUnifierMdefault
instance (Eq v, Traversable t, Eq (t())) => GetMatcher t v (Rule t v) where getMatcherM = getMatcherMdefault

type Rule t v = RuleF (Free t v)

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
reduce :: (Ord v, Enum v, Eq (Free t v), Match t, MonadPlus m) => [Rule t v] -> Term t v -> m (Term t v)
reduce rr t = fixM_Eq (rewriteStep rr) t `evalStateT` freshvars
  where freshvars = [toEnum 0 ..] \\ vars t
#endif
