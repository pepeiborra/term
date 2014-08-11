{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

module Data.Term.Narrowing (
  contexts, fill, (|>),
  isRNF,
  narrow1, narrow1P, narrows, narrow,
  narrow1', narrow1P', narrows', narrow',
  narrowBasic, narrowsBasic, narrow1Basic,
  qNarrow1P, qNarrow1P',
#ifdef LOGICT
  innNarrowing, innBnarrowing,
#endif
  narrowBounded, narrowBasicBounded,
  narrowStepBasic
) where

import Control.Arrow
#ifdef LOGICT
import Control.Monad.Logic
#endif
import Control.Monad.State
import Control.Monad.Variant
import Data.Foldable (Foldable)
import Data.Monoid
import Data.Traversable (Traversable)

import Data.Term
import Data.Term.Rewriting
import Data.Term.Substitutions
import Data.Term.Rules
import Data.Term.Utils

import Text.PrettyPrint.HughesPJClass

-- | Rigid Normal Form
isRNF :: (Ord v, Enum v, Rename v, Unify t) => [Rule t v] -> Term t v -> Bool
isRNF rr = null . narrow1 rr

-- -----------
-- * Contexts
-- -----------
type Context t v = Term t (Either Hole v)
data Hole        = Hole deriving (Eq, Ord, Show)

instance Pretty Hole where pPrint _ = text "?h"

instance Functor t => Monoid (Context t v) where
 mempty = return (Left Hole)
 mappend ct1 ct2 = ct1 >>= f where
     f (Left Hole) = ct2
     f v           = return v

-- | Fill a hole in a context
fill,(|>) :: Functor t => Context t v -> Term t v -> Term t v
fill ct t = ct >>= f
    where f (Left Hole) = t
          f (Right v)   = return v

(|>) = fill

-- | Returns one layer of contexts.
--   That is, a list of direct subterms and the corresponding contexts
--   | forall subterm ctx . (subterm, ctx) <- contexts t ==> ctx |> subterm = t
contexts :: Traversable t => Term t v -> [(Term t v, Context t v, Position)]
contexts t = [ (fmap fromRight t_i, u, [i])
             | i <- [1..length (directSubterms t)]
             , (u, t_i) <- updateAt' [i] (const mempty)(fmap Right t) ]
  where fromRight (Right x) = x
        fromRight _ = error "contexts: the impossible happened"

-- ------------
-- * Narrowing
-- ------------

{-# INLINE narrowStepBasic #-}
narrowStepBasic :: (Unify t, Ord v, MonadPlus m, MonadVariant m, MonadEnv m, Var m ~ v, t ~ TermF m) =>
                   [Rule t v] -> Term t v -> m (Term t v, Position)
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
narrow1 :: (Ord v, Enum v, Rename v, Unify t, MonadPlus m) => [Rule t v] -> Term t v -> m (Term t v, Substitution t v)
narrow1 rr t = second (restrictTo (vars t)) `liftM` narrow1' rr t

-- | one step, returns the position used
narrow1P :: (Ord v, Enum v, Rename v, Unify t, MonadPlus m) => [Rule t v] -> Term t v -> m ((Term t v, Position), Substitution t v)
narrow1P rr t= second (restrictTo (vars t)) `liftM` narrow1P' rr t

-- | narrowing to rigid normal form
#ifdef LOGICT
narrow :: (Ord v, Enum v, Rename v, Unify t, MonadLogic m, Eq (Term t v)
          ) => [Rule t v] -> Term t v -> m (Term t v, Substitution t v)
#else
narrow :: (Ord v, Enum v, Rename v, Unify t, MonadPlus m, Eq (Term t v)) => [Rule t v] -> Term t v -> m (Term t v, Substitution t v)
#endif
narrow  rr t = second (restrictTo (vars t)) `liftM` narrow' rr t

-- | narrowing transitive closure
narrows :: (Ord v, Enum v, Rename v, Unify t, MonadPlus m) => [Rule t v] -> Term t v -> m (Term t v, Substitution t v)
narrows rr t = second (restrictTo (vars t)) `liftM` narrows' rr t


-- ** Dirty versions
--  These do not trim the substitution before returning

-- Monad stacking both monadvariant and monadenv.
-- TODO Manually roll for speed.
newtype NarrowingM t v m a = NarrowingM {unNarrowingM :: MVariantT v (MEnvT t v m) a}
                           deriving (Functor, Monad, MonadPlus, MonadVariant)
type instance Var (NarrowingM t v m) = v
type instance TermF (NarrowingM t v m) = t

deriving instance (Functor t, Foldable t, Ord v, Monad m) => MonadEnv (NarrowingM t v m)

#ifdef LOGICT
-- deriving instance MonadLogic m => MonadLogic (NarrowingM t v m)
instance MonadLogic m => MonadLogic (NarrowingM t v m) where
  msplit m = NarrowingM $ (liftM.liftM) f (msplit (unNarrowingM m)) where
   f (a,m') = (a, NarrowingM m')
#endif

run   :: (Enum v, Ord v, Functor t, Foldable t, Monad m
         ) => (Term t v -> NarrowingM t v m a) -> Term t v -> m (a, Substitution t v)
run f t = runMEnv $ runVariantT' freshVars $ unNarrowingM $ f t where
    freshVars = [toEnum (1 + maximum ( 0 : map fromEnum (vars t))) ..]

-- | one step
narrow1' :: (Ord v, Enum v, Rename v, Unify t, MonadPlus m) => [Rule t v] -> Term t v -> m (Term t v, Substitution t v)
narrow1' rr = liftM (second zonkSubst) . run (narrowStepBasic rr >=> zonkM return . fst)

-- | one step, returns the position used
narrow1P' :: (Ord v, Enum v, Rename v, Unify t, MonadPlus m) => [Rule t v] -> Term t v -> m ((Term t v, Position), Substitution t v)
narrow1P' rr = liftM (second zonkSubst) . run (narrowStepBasic rr >=> firstM (zonkM return))

-- | narrowing to rigid normal form
#ifdef LOGICT
narrow' :: (Ord v, Enum v, Rename v, Unify t, MonadLogic m, Eq (Term t v)) => [Rule t v] -> Term t v -> m (Term t v, Substitution t v)
narrow' rr = liftM (second zonkSubst) . run (fixMP(narrowStepBasic rr >=> zonkM return . fst))
#else
narrow' :: (Ord v, Enum v, Rename v, Unify t, MonadPlus m,  Eq (Term t v)) => [Rule t v] -> Term t v -> m (Term t v, Substitution t v)
narrow' rr = liftM (second zonkSubst) . run (fixM_Eq(narrowStepBasic rr >=> zonkM return . fst))
#endif

-- | one or more steps (transitive closure)
narrows' :: (Ord v, Enum v, Rename v, Unify t, MonadPlus m) => [Rule t v] -> Term t v -> m (Term t v, Substitution t v)
narrows' rr = liftM (second zonkSubst) . run(closureMP(narrowStepBasic rr >=> zonkM return . fst))

------------------------------
-- * Narrowing under Strategies
-- ---------------------------
-- | Note that this function does not assume that the rules and the term have been renamed apart
qNarrow1P :: ( Ord v, Enum v, Rename v, Unify t, MonadPlus m
             ) => [Term t v] -> [Rule t v] -> Term t v -> m ((Term t v, Position), Substitution t v)
qNarrow1P q rr t = second(restrictTo (vars t)) `liftM` qNarrow1P' q rr t
-- | Note that this function does not assume that the rules and the term have been renamed apart
qNarrow1P' :: ( Ord v, Enum v, Rename v, Unify t, MonadPlus m
              ) => [Term t v] -> [Rule t v] -> Term t v -> m ((Term t v, Position), Substitution t v)
qNarrow1P' q rr = liftM(second zonkSubst) . run (qNarrowStepBasic q rr >=> firstM(zonkM return))

{-# INLINE qNarrowStepBasic #-}
-- Note that this function does not assume that the rules and the term have been renamed apart
qNarrowStepBasic :: (Unify t, Enum v, Ord v, MonadPlus m, MonadVariant m, MonadEnv m, Var m ~ v, t ~ TermF m) =>
                   [Term t v] -> [Rule t v] -> Term t v -> m (Term t v, Position)
qNarrowStepBasic q rr t = go (t, mempty, [])
    where go (t, ct,pos) = do { t' <- narrowTop t;
                                return (ct |> t', pos)}
                          `mplus`
                           msum [go (t', ct `mappend` ct', pos ++ i)
                                | (t', ct', i) <- contexts t]
          narrowTop t = msum$ flip map rr $ \(lhs :-> rhs) -> do
                          guard (not $ isVar t)
                          unifyM lhs t
                          lhs' <- zonkTermM return lhs
                          forM_ (directSubterms lhs') (guard . isQNF)
                          return rhs
          isQNF = isNF [ qt :-> qt | qt <- q]

#ifdef LOGICT
-- | Innermost narrowing
innNarrowing :: (Unify t, Ord v, Enum v, Rename v, Var m ~ v, MonadLogic m) => [Rule t v] -> Term t v -> m (Term t v, Substitution t v)
innNarrowing rr t = do
  (t', s) <- run (fixMP (innStepBasic rr >=> zonkM return)) t
  return (t', zonkSubst s)

-- | Innermost Basic Narrowing
innBnarrowing :: (Unify t, Ord v, Enum v, Rename v, MonadLogic m) => [Rule t v] -> Term t v -> m (Term t v, Substitution t v)
innBnarrowing rr t = second (restrictTo (vars t)) `liftM` run go t where go = fixMP (innStepBasic rr)

-- TODO: Prove that this implementation really fulfills the innermost restriction
innStepBasic :: (Ord v, Unify t, TermF m ~ t, Var m ~ v, MonadEnv m, MonadVariant m, MonadLogic m) => [Rule t v] -> Term t v -> m(Term t v)
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

narrowBounded :: (Ord v, Enum v, Rename v, Unify t, MonadPlus m) => (Term t v -> Bool) -> [Rule t v] -> Term t v -> m (Term t v, Substitution t v)
narrowBounded pred rr t = second (restrictTo (vars t)) `liftM` run go t where
 go t = do
    t' <- narrowStepBasic rr t >>= zonkM return . fst
    if pred t' then go t' else return t'

-- ** Basic Narrowing
narrow1Basic :: (Ord v, Enum v, Rename v, Unify t, MonadPlus m) => [Rule t v] -> Term t v -> m (Term t v, Substitution t v)
narrow1Basic = narrow1

narrowsBasic :: (Ord v, Enum v, Rename v, Unify t, MonadPlus m) => [Rule t v] -> Term t v -> m (Term t v, Substitution t v)
narrowsBasic rr t = second (restrictTo (vars t)) `liftM`
                    run (closureMP (liftM fst . narrowStepBasic rr) >=> zonkM return) t
#ifdef LOGICT
narrowBasic :: (Ord v, Enum v, Rename v, Unify t, MonadLogic m) => [Rule t v] -> Term t v -> m (Term t v, Substitution t v)
narrowBasic rr t = second (restrictTo (vars t)) `liftM`
                   run (fixMP (liftM fst . narrowStepBasic rr) >=> zonkM return) t
#else
narrowBasic :: (Ord v, Enum v, Rename v, Unify t, Eq (Term t v), MonadPlus m) => [Rule t v] -> Term t v -> m (Term t v, Substitution t v)
narrowBasic rr t = second (restrictTo (vars t)) `liftM`
                   run (fixM_Eq (liftM fst . narrowStepBasic rr) >=> zonkM return) t
#endif
narrowBasicBounded :: (Ord v, Enum v, Rename v, Unify t, MonadPlus m) => (Term t v -> Bool) -> [Rule t v] -> Term t v -> m (Term t v, Substitution t v)
narrowBasicBounded pred rr t = second (restrictTo (vars t)) `liftM` run (go >=> zonkM return) t
  where
    go t = do
      t' <- fst `liftM` narrowStepBasic rr t
      if pred t' then go t' else return t'

