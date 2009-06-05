{-# LANGUAGE CPP #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE FlexibleContexts #-}
module Data.Term.Narrowing (
  contexts, fill, (|>),
  isRNF,
  narrow1, narrow1P, narrows, narrow,
  narrow1', narrow1P', narrows', narrow',
  narrowBasic, narrowsBasic, narrow1Basic,
#ifdef LOGICT
  inn_narrowing, inn_Bnarrowing,
#endif
  narrowBounded, narrowBasicBounded
) where

import Control.Arrow
import Control.Monad.Free
#ifdef LOGICT
import Control.Monad.Logic
#endif
#ifdef TRANSFORMERS
import Control.Monad.Trans.State
#else
import Control.Monad.State
#endif
import Data.Foldable (Foldable)
import Data.List
import Data.Monoid
import Data.Traversable (Traversable)
import qualified Data.Traversable as T

import Data.Term
import Data.Term.Rules
import Data.Term.Rewriting
import Data.Term.Utils


-- | Rigid Normal Form
isRNF :: (Ord v, Enum v, Unify t) => [Rule t v] -> Term t v -> Bool
isRNF rr = null . narrow1 rr

-- -----------
-- * Contexts
-- -----------
type Context t v = Term t (Either Hole v)
data Hole        = Hole deriving (Eq, Ord, Show)

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

-- | Returns a list of subterms and the corresponding contexts
--   | forall subterm ctx . (subterm, ctx) <- contexts t ==> ctx |> subterm = t
contexts :: Traversable t => Term t v -> [(Term t v, Context t v, Position)]
contexts t = [ (fmap fromRight t_i, u, [i])
             | i <- [1..size t]
             , (u, t_i) <- updateAt' [i] (fmap Right t) (const mempty) ]
  where fromRight (Right x) = x
        fromRight _ = error "contexts: the impossible happened"

-- ------------
-- * Narrowing
-- ------------

{-# INLINE narrowStepBasic #-}
narrowStepBasic :: (Unify t, Ord v, MonadPlus m, MonadFresh v m, MonadEnv t v m) =>
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
narrow1 :: (Ord v, Enum v, Unify t, MonadPlus m) => [Rule t v] -> Term t v -> m (Term t v, Substitution t v)
narrow1 rr t = second (restrictTo (vars t)) `liftM` narrow1' rr t

-- | one step, returns the position used
narrow1P :: (Ord v, Enum v, Unify t, MonadPlus m) => [Rule t v] -> Term t v -> m ((Term t v, Position), Substitution t v)
narrow1P rr t= second (restrictTo (vars t)) `liftM` narrow1P' rr t

-- | narrowing to rigid normal form
#ifdef LOGICT
narrow :: (Ord v, Enum v, Unify t, MonadLogic m, Eq (Free t v)) => [Rule t v] -> Term t v -> m (Term t v, Substitution t v)
#else
narrow :: (Ord v, Enum v, Unify t, MonadPlus m, Eq (Free t v)) => [Rule t v] -> Term t v -> m (Term t v, Substitution t v)
#endif
narrow  rr t = second (restrictTo (vars t)) `liftM` narrow' rr t

-- | narrowing transitive closure
narrows :: (Ord v, Enum v, Unify t, MonadPlus m) => [Rule t v] -> Term t v -> m (Term t v, Substitution t v)
narrows rr t = second (restrictTo (vars t)) `liftM` narrows' rr t


-- ** Dirty versions
--  These do not trim the substitution before returning

run   :: (Enum v, Eq v, Monoid s, Functor t, Foldable t, Monad m) => (Term t v -> StateT (s, [v]) m a) -> Term t v -> m (a, s)
run f t = second fst `liftM` (f t `runStateT` (mempty, freshVars)) where
    freshVars = [toEnum (maximum (map fromEnum (vars t))) ..]

-- | one step
narrow1' :: (Ord v, Enum v, Unify t, MonadPlus m) => [Rule t v] -> Term t v -> m (Term t v, Substitution t v)
narrow1' rr = liftM (second zonkSubst) . run (narrowStepBasic rr >=> zonkM return . fst)

-- | one step, returns the position used
narrow1P' :: (Ord v, Enum v, Unify t, MonadPlus m) => [Rule t v] -> Term t v -> m ((Term t v, Position), Substitution t v)
narrow1P' rr = liftM (second zonkSubst) . run (narrowStepBasic rr >=> firstM (zonkM return))

-- | narrowing to rigid normal form
#ifdef LOGICT
narrow' :: (Ord v, Enum v, Unify t, MonadLogic m, Eq (Free t v)) => [Rule t v] -> Term t v -> m (Term t v, Substitution t v)
narrow' rr = liftM (second zonkSubst) . run (fixMP(narrowStepBasic rr >=> zonkM return . fst))
#else
narrow' :: (Ord v, Enum v, Unify t, MonadPlus m, Eq (Free t v)) => [Rule t v] -> Term t v -> m (Term t v, Substitution t v)
narrow' rr = liftM (second zonkSubst) . run (fixM_Eq(narrowStepBasic rr >=> zonkM return . fst))
#endif

-- | one or more steps (transitive closure)
narrows' :: (Ord v, Enum v, Unify t, MonadPlus m) => [Rule t v] -> Term t v -> m (Term t v, Substitution t v)
narrows' rr = liftM (second zonkSubst) . run(closureMP(narrowStepBasic rr >=> zonkM return . fst))

------------------------------
-- * Narrowing under Strategies
-- ---------------------------

#ifdef LOGICT
-- | Innermost narrowing
inn_narrowing :: (Unify t, Ord v, Enum v, MonadLogic m) => [Rule t v] -> Term t v -> m (Term t v, Substitution t v)
inn_narrowing rr t = do
  (t', s) <- run (fixMP (innStepBasic rr >=> zonkM return)) t
  return (t', zonkSubst s)

-- | Innermost Basic Narrowing
inn_Bnarrowing :: (Unify t, Ord v, Enum v, MonadLogic m) => [Rule t v] -> Term t v -> m (Term t v, Substitution t v)
inn_Bnarrowing rr t = second (restrictTo (vars t)) `liftM` run go t where go = fixMP (innStepBasic rr)

-- TODO: Prove that this implementation really fulfills the innermost restriction
innStepBasic :: (Ord v, Unify t, MonadEnv t v m, MonadFresh v m, MonadLogic m) => [Rule t v] -> Term t v -> m(Term t v)
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

narrowBounded :: (Ord v, Enum v, Unify t, MonadPlus m) => (Term t v -> Bool) -> [Rule t v] -> Term t v -> m (Term t v, Substitution t v)
narrowBounded pred rr t = second (restrictTo (vars t)) `liftM` run go t where
 go t = do
    t' <- narrowStepBasic rr t >>= zonkM return . fst
    if pred t' then go t' else return t'

-- ** Basic Narrowing
narrow1Basic :: (Ord v, Enum v, Unify t, MonadPlus m) => [Rule t v] -> Term t v -> m (Term t v, Substitution t v)
narrow1Basic = narrow1

narrowsBasic :: (Ord v, Enum v, Unify t, MonadPlus m) => [Rule t v] -> Term t v -> m (Term t v, Substitution t v)
narrowsBasic rr t = second (restrictTo (vars t)) `liftM`
                    run (closureMP (liftM fst . narrowStepBasic rr) >=> zonkM return) t
#ifdef LOGICT
narrowBasic :: (Ord v, Enum v, Unify t, MonadLogic m) => [Rule t v] -> Term t v -> m (Term t v, Substitution t v)
narrowBasic rr t = second (restrictTo (vars t)) `liftM`
                   run (fixMP (liftM fst . narrowStepBasic rr) >=> zonkM return) t
#else
narrowBasic :: (Ord v, Enum v, Unify t, Eq (Free t v), MonadPlus m) => [Rule t v] -> Term t v -> m (Term t v, Substitution t v)
narrowBasic rr t = second (restrictTo (vars t)) `liftM`
                   run (fixM_Eq (liftM fst . narrowStepBasic rr) >=> zonkM return) t
#endif
narrowBasicBounded :: (Ord v, Enum v, Unify t, MonadPlus m) => (Term t v -> Bool) -> [Rule t v] -> Term t v -> m (Term t v, Substitution t v)
narrowBasicBounded pred rr t = second (restrictTo (vars t)) `liftM` run (go >=> zonkM return) t
  where
    go t = do
      t' <- fst `liftM` narrowStepBasic rr t
      if pred t' then go t' else return t'

