{-# LANGUAGE FlexibleContexts, ConstraintKinds #-}
{-# LANGUAGE DeriveGeneric, DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, OverlappingInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}

module Data.Term.Automata
   (TermMatcher, Tree, FastMatch, singleton, insert, createMatcher, createMatcherO
   , match, isNF, isNFO, Data.Term.Automata.map
   ) where

import Control.Applicative
import Control.Applicative.Compose
import Control.Monad.Free
import Control.Monad.Free.Extras()
import Control.Monad.State
import Control.DeepSeq
import Control.DeepSeq.Extras
import Data.Foldable (Foldable)
import Data.Function
import qualified Data.Foldable as F
import qualified Data.Map as Map
import Data.Map.Strict (Map)
import Data.Maybe (fromMaybe, isJust, isNothing)
import Data.Monoid (Monoid(..))
import Data.Term
import Data.Term.Simple
import Data.Term.Var
import Data.Term.Rules
import qualified Data.Term.Rewriting as R
import Data.Term.Substitutions
import Data.Traversable as T
import Data.Typeable
import GHC.Generics (Generic)
import Prelude.Extras
import Unsafe.Coerce

import Debug.Hoed.Observe
import Debug.Hoed.Observe.Instances
import Data.Term.Utils (interleave)

-- -------------------------------------------
-- Fast normal form checking via Tree automata
-- -------------------------------------------

{- This representation is wrong and needs to be fixed for:
   1. Non linear terms, by replacing Any with named variables
   2. Non total, overlapping terms. Example:
       f(a,x), f(x,b)
      where x is a variable, will not match the term f(c,c).
      However the term matcher obtained will be f(Any,Any) which will give a false match.
 -}
data Tree a = Node a (Forest a)
            deriving (Eq, Show, Ord, Functor, Foldable, Traversable, Generic, Generic1, Typeable)
type Forest a = [Tree a]
type SubtermMatcher t v = Forest (TermMatcher t v)
type FastMatch t v = (Ord1 t, Traversable t, NFData1 t, NFData v, Ord v, Observable v, Observable1 t, Observable1 (Term t))

data TermMatcher t v =
    Branch  (Map (Lift1 t ()) (SubtermMatcher t v))
  | Var v
  deriving (Generic, Generic1, Typeable)

pattern Done     = []

instance Eq1 t => Eq1 (TermMatcher t) where
  (==#) :: forall v. Eq v => TermMatcher t v -> TermMatcher t v -> Bool
  Branch m1 ==# Branch m2 = m1 == m2
  Var v1 ==# Var v2 = v1 == v2
  _ ==# _ = False
instance (Eq1 t, Eq v) => Eq (TermMatcher t v) where (==) = (==#)

instance Ord1 t => Ord1 (TermMatcher t) where
  compare1 :: forall v . Ord v => TermMatcher t v -> TermMatcher t v -> Ordering
  compare1 (Branch m1) (Branch m2) = compare m1 m2
  compare1 (Var v1) (Var v2) = compare v1 v2
  compare1 Branch{} Var{}    = LT
  compare1 Var{}    Branch{} = GT
instance (Ord1 t, Ord v) => Ord (TermMatcher t v) where compare = compare1

instance Show1 t => Show1 (TermMatcher t) where
  showsPrec1 :: forall v. Show v => Int -> TermMatcher t v -> ShowS
  showsPrec1 p (Var v)    = showsPrec p v
  showsPrec1 p (Branch m) = showParen (p>=5) (("Branch " ++) . showsPrec 5 m)

instance (Show1 t, Show v) => Show (TermMatcher t v) where showsPrec = showsPrec1

mappendTM :: (Observable a, Observable1 t, Observable1 (Free t), Ord1 t, Eq a
             ) => Observer -> TermMatcher t a -> TermMatcher t a -> [TermMatcher t a]
mappendSTM :: (Observable a, Observable1 (Free t), Observable1 t, Ord1 t, Eq a
              ) => Observer -> Forest (TermMatcher t a) -> Forest (TermMatcher t a) -> Forest(TermMatcher t a)
mergeSTM :: (Observable a, Observable1 (Free t), Observable1 t, Ord1 t, Eq a
              ) => Observer -> Forest (TermMatcher t a) -> Forest (TermMatcher t a)
mappendSTM (O _ oo) x y = oo "mergeSTM" mergeSTM (x ++ y)

mergeSTM _ [] = []
mergeSTM (O o oo) (a:aa) =
   foldr (oo "mergeAlg" mergeAlg) [a] aa

mergeAlg :: (Observable v, Observable1 t, Observable1 (Free t), Ord1 t, Eq v
            ) => Observer -> Tree (TermMatcher t v) -> Forest (TermMatcher t v) -> Forest (TermMatcher t v)
mergeAlg (O o oo) x all = F.minimumBy (compare `on` length) $
                          Prelude.map concat (interleave (\y -> oo "mergeAlg'" mergeAlg' x y) (:[]) all)
mergeAlg' ::(Observable v, Observable1 t, Observable1 (Free t), Ord1 t, Eq v
            ) => Observer -> Tree (TermMatcher t v) -> Tree (TermMatcher t v) -> Forest (TermMatcher t v)
mergeAlg' (O _ oo) (Node t1 s1) (Node t2 s2)
      | t1 == t2  = [Node t1 (oo "STM" mappendSTM s1 s2)]
      | s1 == s2  = [Node m s1 | m <- oo "TM" mappendTM t1 t2]
      | otherwise = [Node t1 s1, Node t2 s2]

mappendTM (O _ oo) (Branch b1) (Branch b2)          = [Branch (Map.unionWith (oo "STM" mappendSTM) b1 b2)]
mappendTM (O o oo) (Var v1)    (Var v2) | v1 == v2  = [Var v1]
mappendTM (O o oo)  a          b                    = [a, b]

instance (Ord1 t, Eq v, Observable v, Observable1 t) => Monoid (TermMatcher t v) where
  mempty = Branch mempty
  mappend = mappendO nilObserver

mappendO o a b =
  case mappendTM o a b of
    [x] -> x
    _ -> error "Monoid (TermMatcher t v): cannot resolve ambiguity at top level"

map :: (Functor f, Ord1 g
       ) => (forall a. f a -> g a) -> TermMatcher f v -> TermMatcher g v
map _ (Var v) = Var v
map f (Branch m) = Branch $ Map.map (mapSM f) $ Map.mapKeys (\(Lift1 x) -> Lift1 (f x)) $ m

mapSM :: (Functor f, Ord1 g
         ) => (forall a. f a -> g a) -> SubtermMatcher f v -> SubtermMatcher g v
mapSM f = fmap g where
  g (Node tm stm) = Node (Data.Term.Automata.map f tm) (mapSM f stm)

singleton :: forall t v. FastMatch t v => Term t v -> TermMatcher t v
singleton = foldTerm Var ft where
  ft t = Branch (Map.singleton (Lift1 $ fmap (const ()) t) stm) where
    stm :: SubtermMatcher t v
    stm = F.foldr (\a b -> [Node a b]) mempty t

insertO :: FastMatch t v => Observer -> Term t v -> TermMatcher t v -> TermMatcher t v
insertO o t m = mappendO o (singleton t) m

insert :: FastMatch t v => Term t v -> TermMatcher t v -> TermMatcher t v
insert t m = mappend (singleton t) m

matches :: FastMatch t v => TermMatcher t v -> Term t v -> Bool
matches = matchesO nilObserver
matchesO :: FastMatch t v => Observer -> TermMatcher t v -> Term t v -> Bool
matchesO o tm t = isJust $ evalMEnv (matchesM o tm t)

matchesM:: forall m f v.
           ( FastMatch f v
           , MonadPlus m
           ) => Observer -> TermMatcher f v -> Term f v -> MEnvT f v m ()
matchesM (O o oo) tm t = snd(foldTerm fv ft t) tm
 where
--   ft :: f(Term f v, TermMatcher f v -> m()) -> (Term f v, TermMatcher f v -> m())
   ft  t            = (Impure(fmap fst t), ft' t)
   ft' t (Branch m) =
    case Map.lookup (Lift1 $ fmap (const()) t) m of
      Nothing -> fail "symbol"
      Just m' -> oo "submatches" submatches m' (Lift1 $ fmap snd t)
   ft' t (Var v) = doVar (Impure $ fmap fst t) v

--   fv :: v -> (Term f v, TermMatcher f v -> m())
   fv  v          = (Pure v, fv' v)
   fv' v (Var v') = doVar (Pure v) v'
   fv' _ _        = fail "var"

   doVar t v = do
     contents <- lookupVar v
     case contents of
       Nothing -> varBind v t
       Just t' | t == t' -> return ()
       _ -> fail "incompatible"


submatches o sms ftt = submatchesL o sms (F.toList ftt)
submatchesL _ Done [] = return ()
submatchesL _ _    [] = fail "arity/shape"
submatchesL _ Done _  = fail "arity/shape"
submatchesL o sms (t:tt) = do
  let trySM (Node this next) = do
      t this
      submatchesL o next tt
  msum $ fmap trySM sms

-- submatches :: forall t v m.
--               (MonadPlus m, Observable1 m, FastMatch t v
--               ) => Observer -> SubtermMatcher t v -> t(TermMatcher t v -> m()) -> m ()
submatches1 (O o oo) sm tt = do
  res <- runStateT (T.mapM (oo "matchSubterm" matchSubterm) tt) sm
  case res of
    (_, Done) -> return ()
    _ -> fail "arity/shape (too small)"

  where
--  matchSubterm :: Observer -> (TermMatcher t v -> m ()) -> StateT (SubtermMatcher t v) m ()
    matchSubterm (O o oo) t = do
      st <- get
      when (null st) $ fail "arity/shape (too big)"
      o "msum" msum $ flip Prelude.map (o "st" st) (oo "tryMatchSubterm" tryMatchSubterm)
     where
      tryMatchSubterm (O o _) (Node this next) = do
           lift $ MEnv $ modify (o "menv")
           lift $ o "t" t this
           put next



-- | Returns true if the term does not match any in the set of terms modelled by the matcher
isNF :: forall t v. FastMatch t v => TermMatcher t v -> Term t v -> Bool
isNFO :: forall t v. FastMatch t v => Observer -> TermMatcher t v -> Term t v -> Bool
isNF = isNFO nilObserver
isNFO o tm t = not (matchesO o tm t)

-- | Given a TRS, returns a model of the normal forms of the TRS
createMatcher :: FastMatch t v => [Term t v] -> TermMatcher t v
createMatcher = Prelude.foldr insert mempty
createMatcherO :: (FastMatch t v, Observable1 (Free t)
                  ) => Observer -> [Term t v] -> TermMatcher t v
createMatcherO (O _ oo) = Prelude.foldr (oo "insert" insertO) mempty

a = term "a" []
b = term "b" []
x = var "x"
x1 = var "x1" `asTypeOf` x
x2 = var "x2" `asTypeOf` x
--y = var "y"
f tt = term "f" tt
zero = term "0" []
s x  = term "s" [x]
p x  = term "p" [x]
minus a b = term "minus" [a,b]
trs1 = [ a  ]
trs2 = [ f [a, a]
       , f [b, b]
       ]
trs3 = [ f [x, x] ]
trs4 = [ minus x x
       , minus zero x
       , minus x zero
       , minus (s x1) (s x2)
--       , minus (s x) (s y)
       ]
--Branch fromList [(Term {id = "minus", args = [(),()]},[Node (VName "x") [Node (VName "x") [],Node Branch (fromList [(Term {id = "0", args = []},[])]) []]])]

check :: (t ~ Data.Term.Simple.TermF String, v ~ Data.Term.Var.Var
         ) => [Term t v] -> Term t v -> Bool
check tt t = isNF (createMatcher tt) t == R.isNF [ t :-> a | t <- tt] t

test1   = check trs1 (a)
test1'  = check trs1 (b)
test1'' = check trs1 (term "b" [x])
test2   = check trs2 (f [a,b])
test2'  = check trs2 (f [b,b])
test2'' = check trs2 (f [a,a])
test3   = check trs3 (f [a,b])
test3'  = check trs3 (f [a,a])
test3'' = check trs3 (f [b,b])
test4   = check trs4 (minus zero zero)
test4'  = check trs4 (minus (s zero) zero)
test4'' = check trs4 (minus zero (s zero))
test4'''  = check trs4 (minus x1 x2)
test4'''' = check trs4 (s(minus (s x1) (s x2)))

instance (NFData1 f) => NFData1 (TermMatcher f) where
  rnf1 (Var v)    = rnf v
  rnf1 (Branch m) = rnf m
instance (NFData1 t, NFData v) => NFData (TermMatcher t v) where rnf = rnf1

instance NFData1 Tree where rnf1 (Node a b) = rnf a `seq` rnf b
instance NFData a => NFData (Tree a) where rnf = rnf1

instance (Observable1 f) => Observable1 (TermMatcher f)
instance (Observable1 f, Observable a) => Observable(TermMatcher f a) where
  observers = observers1
  observer = observer1
instance Observable1 Tree
instance Observable a => Observable (Tree a) where
  observers = observers1
  observer = observer1
