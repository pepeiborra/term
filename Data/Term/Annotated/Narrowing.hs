{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE FlexibleContexts #-}
module Data.Term.Annotated.Narrowing (
  contexts, fill, (|>),
  isRNF,
  narrow1, narrow1P, narrows, narrow,
  narrow1', narrow1P', narrows', narrow',
  narrowBasic, narrowsBasic, narrow1Basic,
#ifdef LOGICT
  innNarrowing, innBnarrowing,
#endif
  narrowBounded, narrowBasicBounded,
  narrowStepBasic
) where

import Control.Arrow
import qualified Control.Monad.Free.Annotated as Free
#ifdef LOGICT
import Control.Monad.Logic
#endif
import Control.Monad.State
import Data.Foldable (Foldable)
import Data.Monoid
import Data.Traversable (Traversable)

import Data.Term.Annotated
import Data.Term.Annotated.Rules
import Data.Term.Utils

import Text.PrettyPrint.HughesPJClass

-- | Rigid Normal Form
isRNF :: (Ord v, Enum v, Rename v, Measured v ann, Unify t) => [Rule ann t v] -> Term ann t v -> Bool
isRNF rr = null . narrow1 rr

-- -----------
-- * Contexts
-- -----------
type Context ann t v = Term ann t (Either Hole v)
data Hole            = Hole deriving (Eq, Ord, Show)
instance Pretty Hole where pPrint _ = text "?h"
instance Monoid ann => Measured Hole ann where measure = mempty

instance (Measured v ann, Functor t, Foldable t) => Monoid (Context ann t v) where
 mempty = mkV (Left Hole)
 mappend ct1 ct2 = Free.bind f ct1 where
     f (Left Hole) = ct2
     f v           = mkV v

-- | Fill a hole in a context
fill,(|>) :: (Measured v ann, Foldable t, Functor t) => Context ann t v -> Term ann t v -> Term ann t v
fill ct t = Free.bind f ct
    where f (Left Hole) = t
          f (Right v)   = mkV v

(|>) = fill

-- | Returns one layer of contexts.
--   That is, a list of direct subterms and the corresponding contexts
--   | forall subterm ctx . (subterm, ctx) <- contexts t ==> ctx |> subterm = t
contexts :: (Traversable t, Measured v ann) => Term ann t v -> [(Term ann t v, Context ann t v, Position)]
contexts t = [ (Free.fmap fromRight t_i, u, [i])
             | i <- [1..length (directSubterms t)]
             , (u, t_i) <- updateAt' [i] (const mempty)(Free.fmap Right t) ]
  where fromRight (Right x) = x
        fromRight _ = error "contexts: the impossible happened"

-- ------------
-- * Narrowing
-- ------------

{-# INLINE narrowStepBasic #-}
narrowStepBasic :: (Unify t, Ord v, Measured v ann, MonadPlus m, MonadVariant v m, MonadEnv ann t v m) =>
                   [Rule ann t v] -> Term ann t v -> m (Term ann t v, Position)
narrowStepBasic rr t = go (t, mempty, [])
    where go (t, ct,pos) = do { t' <- narrowTop t; return (ct |> t', pos)}
                          `mplus`
                           msum [go (t', ct `mappend` ct', pos ++ i) | (t', ct', i) <- contexts t]
          narrowTop t = msum$ flip map rr $ \r -> do
                          guard (not $ isVar t)
                          lhs :-> rhs <- getFresh r
                          unifyM lhs t
                          return rhs

-- | one step
narrow1 :: (Ord v, Enum v, Rename v, Measured v ann, Unify t, MonadPlus m) => [Rule ann t v] -> Term ann t v -> m (Term ann t v, Substitution ann t v)
narrow1 rr t = second (restrictTo (vars t)) `liftM` narrow1' rr t

-- | one step, returns the position used
narrow1P :: (Ord v, Enum v, Rename v, Measured v ann, Unify t, MonadPlus m) => [Rule ann t v] -> Term ann t v -> m ((Term ann t v, Position), Substitution ann t v)
narrow1P rr t= second (restrictTo (vars t)) `liftM` narrow1P' rr t

-- | narrowing to rigid normal form
#ifdef LOGICT
narrow :: (Ord v, Enum v, Rename v, Measured v ann, Unify t, MonadLogic m, Eq (Term ann t v)) => [Rule ann t v] -> Term ann t v -> m (Term ann t v, Substitution ann t v)
#else
narrow :: (Ord v, Enum v, Rename v, Measured v ann, Unify t, MonadPlus m, Eq (Term ann t v)) => [Rule ann t v] -> Term ann t v -> m (Term ann t v, Substitution ann t v)
#endif
narrow  rr t = second (restrictTo (vars t)) `liftM` narrow' rr t

-- | narrowing transitive closure
narrows :: (Ord v, Enum v, Rename v, Measured v ann, Unify t, MonadPlus m) => [Rule ann t v] -> Term ann t v -> m (Term ann t v, Substitution ann t v)
narrows rr t = second (restrictTo (vars t)) `liftM` narrows' rr t


-- ** Dirty versions
--  These do not trim the substitution before returning

run   :: (Enum v, Eq v, Monoid s, Functor t, Foldable t, Monad m) => (Term ann t v -> StateT (s, [v]) m a) -> Term ann t v -> m (a, s)
run f t = second fst `liftM` (f t `runStateT` (mempty, freshVars)) where
    freshVars = [toEnum (1 + maximum ( 0 : map fromEnum (vars t))) ..]

-- | one step
narrow1' :: (Ord v, Enum v, Rename v, Measured v ann, Unify t, MonadPlus m) => [Rule ann t v] -> Term ann t v -> m (Term ann t v, Substitution ann t v)
narrow1' rr = liftM (second zonkSubst) . run (narrowStepBasic rr >=> zonkM return . fst)

-- | one step, returns the position used
narrow1P' :: (Ord v, Enum v, Rename v, Measured v ann, Unify t, MonadPlus m) => [Rule ann t v] -> Term ann t v -> m ((Term ann t v, Position), Substitution ann t v)
narrow1P' rr = liftM (second zonkSubst) . run (narrowStepBasic rr >=> firstM (zonkM return))

-- | narrowing to rigid normal form
#ifdef LOGICT
narrow' :: (Ord v, Enum v, Rename v, Measured v ann, Unify t, MonadLogic m, Eq (Term ann t v)) => [Rule ann t v] -> Term ann t v -> m (Term ann t v, Substitution ann t v)
narrow' rr = liftM (second zonkSubst) . run (fixMP(narrowStepBasic rr >=> zonkM return . fst))
#else
narrow' :: (Ord v, Enum v, Rename v, Measured v ann, Unify t, MonadPlus m, Eq (Term ann t v)) => [Rule ann t v] -> Term ann t v -> m (Term ann t v, Substitution ann t v)
narrow' rr = liftM (second zonkSubst) . run (fixM_Eq(narrowStepBasic rr >=> zonkM return . fst))
#endif

-- | one or more steps (transitive closure)
narrows' :: (Ord v, Enum v, Rename v, Measured v ann, Unify t, MonadPlus m) => [Rule ann t v] -> Term ann t v -> m (Term ann t v, Substitution ann t v)
narrows' rr = liftM (second zonkSubst) . run(closureMP(narrowStepBasic rr >=> zonkM return . fst))

------------------------------
-- * Narrowing under Strategies
-- ---------------------------

#ifdef LOGICT
-- | Innermost narrowing
innNarrowing :: (Unify t, Ord v, Enum v, Rename v, Measured v ann, MonadLogic m) => [Rule ann t v] -> Term ann t v -> m (Term ann t v, Substitution ann t v)
innNarrowing rr t = do
  (t', s) <- run (fixMP (innStepBasic rr >=> zonkM return)) t
  return (t', zonkSubst s)

-- | Innermost Basic Narrowing
innBnarrowing :: (Unify t, Ord v, Enum v, Rename v, Measured v ann, MonadLogic m) => [Rule ann t v] -> Term ann t v -> m (Term ann t v, Substitution ann t v)
innBnarrowing rr t = second (restrictTo (vars t)) `liftM` run go t where go = fixMP (innStepBasic rr)

-- TODO: Prove that this implementation really fulfills the innermost restriction
innStepBasic :: (Ord v, Measured v ann, Unify t, MonadEnv ann t v m, MonadVariant v m, MonadLogic m) => [Rule ann t v] -> Term ann t v -> m(Term ann t v)
innStepBasic rr t = do
     rr' <- mapM getFresh rr
     let go (t, ct) = ifte (msum [go (t, ct`mappend`ct1) | (t, ct1,_) <- contexts t]) -- Try
                           return                        -- then return it
                           ((ct |>) `liftM` narrowTop t) -- else narrow at the top
         narrowTop t = msum $ flip map rr' $ \(lhs:->rhs) -> do
                          guard (not $ isVar t)
                          unifyM lhs t
                          return rhs
     go (t, mempty)
#endif

narrowBounded :: (Ord v, Enum v, Rename v, Measured v ann, Unify t, MonadPlus m) => (Term ann t v -> Bool) -> [Rule ann t v] -> Term ann t v -> m (Term ann t v, Substitution ann t v)
narrowBounded pred rr t = second (restrictTo (vars t)) `liftM` run go t where
 go t = do
    t' <- narrowStepBasic rr t >>= zonkM return . fst
    if pred t' then go t' else return t'

-- ** Basic Narrowing
narrow1Basic :: (Ord v, Enum v, Rename v, Measured v ann, Unify t, MonadPlus m) => [Rule ann t v] -> Term ann t v -> m (Term ann t v, Substitution ann t v)
narrow1Basic = narrow1

narrowsBasic :: (Ord v, Enum v, Rename v, Measured v ann, Unify t, MonadPlus m) => [Rule ann t v] -> Term ann t v -> m (Term ann t v, Substitution ann t v)
narrowsBasic rr t = second (restrictTo (vars t)) `liftM`
                    run (closureMP (liftM fst . narrowStepBasic rr) >=> zonkM return) t
#ifdef LOGICT
narrowBasic :: (Ord v, Enum v, Rename v, Measured v ann, Unify t, MonadLogic m) => [Rule ann t v] -> Term ann t v -> m (Term ann t v, Substitution ann t v)
narrowBasic rr t = second (restrictTo (vars t)) `liftM`
                   run (fixMP (liftM fst . narrowStepBasic rr) >=> zonkM return) t
#else
narrowBasic :: (Ord v, Enum v, Rename v, Measured v ann, Unify t, Eq (Term ann t v), MonadPlus m) => [Rule ann t v] -> Term ann t v -> m (Term ann t v, Substitution ann t v)
narrowBasic rr t = second (restrictTo (vars t)) `liftM`
                   run (fixM_Eq (liftM fst . narrowStepBasic rr) >=> zonkM return) t
#endif
narrowBasicBounded :: (Ord v, Enum v, Rename v, Measured v ann, Unify t, MonadPlus m) => (Term ann t v -> Bool) -> [Rule ann t v] -> Term ann t v -> m (Term ann t v, Substitution ann t v)
narrowBasicBounded pred rr t = second (restrictTo (vars t)) `liftM` run (go >=> zonkM return) t
  where
    go t = do
      t' <- fst `liftM` narrowStepBasic rr t
      if pred t' then go t' else return t'

