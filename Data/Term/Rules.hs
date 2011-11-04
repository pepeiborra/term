{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, UndecidableInstances, TypeSynonymInstances #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE CPP #-}

{-| This module works with an abstract notion of rule.

    A rule is a set of terms (generally a pair) which must
    be treated as a whole. Concrete examples include
    term rewriting rules and prolog clauses.

    To do this the module provides
    generalizations of the unify, match, equiv, fresh and vars
    operations which work with sets of terms.
-}
module Data.Term.Rules
  (RuleF(..), Rule, left, right, HasRules(..), swapRule, IsTRS(..),
   Signature(..), mapSignature, allSymbols, arities, HasSignature(..),
   getArity, getArities, getConstructorSymbols, getDefinedSymbols, getAllSymbols,
   isConstructorTerm, isRootDefined, collectIds,
   GetVars(..),
   GetUnifier(..), getUnifier, unifies', equiv', equiv2', getUnifierMdefault,
   GetMatcher(..), getMatcher, matches', getMatcherMdefault,
   GetFresh(..), getFresh, getVariant, getFreshMdefault
  ) where

import Control.Applicative
import Control.Monad.Free
import Control.Monad.State (evalState, execStateT, evalStateT)
import Data.Foldable (Foldable, foldMap, toList)
import Data.List ((\\))
import Data.Maybe
import Data.Monoid
import Data.Traversable (Traversable)
import qualified Data.Traversable as T
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Control.Monad.Variant

import Data.Term
import qualified Data.Term.Var as Var
import Data.Term.IOVar
import Data.Term.Variables

import qualified Data.Id.Family as Family
import qualified Data.Rule.Family as Family

-- ----------------
-- * Concrete rules
-- ----------------
infix 1 :->
data RuleF a = (:->) {lhs,rhs::a} deriving (Eq, Ord, Show)
instance Functor RuleF where fmap f (l :-> r) = f l :-> f r
instance Foldable RuleF where foldMap f (l :-> r) = f l `mappend` f r
instance Traversable RuleF where traverse f (l :-> r) = (:->) <$> f l <*> f r
instance Traversable t => GetFresh (RuleF (Term t v)) where getFreshM = getFreshMdefault
instance GetVars t => GetVars (RuleF t) where getVars = foldMap getVars
instance (Eq v, Traversable t, Eq (t())) => GetUnifier (Rule t v) where getUnifierM = getUnifierMdefault
instance (Eq v, Traversable t, Eq (t())) => GetMatcher (Rule t v) where getMatcherM = getMatcherMdefault
type instance Var (RuleF a) = Var a
type instance TermF (RuleF a) = TermF a
type instance Id (RuleF a) = Id a

type Rule t v = RuleF (Term t v)

{-# RULES "rules/tRS" forall x. tRS (rules x) = x #-}
{-# RULES "tRS/rules" forall x. rules (tRS x) = x #-}


class HasRules trs where
  rules :: trs -> [Family.Rule trs]
class HasRules trs => IsTRS trs where tRS :: [Family.Rule trs] -> trs

type instance Family.Rule (Rule t v) = Rule t v

instance HasRules (Rule t v) where rules = (:[])
instance HasRules a => HasRules [a] where rules = foldMap rules
instance HasRules a => HasRules (Set   a) where rules = foldMap rules . toList
instance HasRules a => HasRules (Map k a) where rules = foldMap rules . Map.elems

instance IsTRS [Rule t v] where tRS   = id

swapRule :: RuleF a -> RuleF a
swapRule (l :-> r) = r :-> l

left,right :: (a -> a) -> RuleF a -> RuleF a

left f (l :-> r)  = f l :-> r
right f (l :-> r) = l   :-> f r

-- ---------------------
-- * Signatures
-- ---------------------
data Signature id = Sig {constructorSymbols, definedSymbols :: Map id Int}
   deriving (Eq, Ord, Show)

type instance Family.Id (Signature id) = id

instance Ord id => Monoid (Signature id) where
    mempty  = Sig mempty mempty
    mappend (Sig c1 s1) (Sig c2 s2) = Sig (mappend c1 c2) (mappend s1 s2)

instance Ord id => HasSignature (Signature id) where
    getSignature = id

class Ord (Family.Id l) => HasSignature l where
  getSignature :: l -> Signature (Family.Id l)

instance (HasId t, Foldable t) => HasSignature (Term t v) where
  getSignature t = Sig{ definedSymbols = Map.empty
                        , constructorSymbols = all }
     where
      all =  Map.fromList [(f,length (directSubterms t))
                                  | t <- subterms t
                                  , Just f <- [rootSymbol t]]

instance (Foldable t, HasId t) => HasSignature [Term t v] where
  getSignature terms = Sig{ definedSymbols     = Map.empty
                          , constructorSymbols = all
                          }
    where all =  Map.fromList [(f,length (directSubterms t))
                                  | t <- concatMap subterms terms
                                  , Just f <- [rootSymbol t]]


instance (Foldable t,  HasId t) => HasSignature (Rule t v) where
  getSignature (l :-> r)
    | Just d <- rootSymbol l
    = Sig{ definedSymbols = Map.singleton d (length $ directSubterms l)
         , constructorSymbols = all}
    | otherwise
    = Sig { definedSymbols = Map.empty
          , constructorSymbols = Map.fromList [(f,length (directSubterms t))
                                               | t <- concatMap subterms [l,r]
                                               , Just f <- [rootSymbol t]]}
    where
      all = Map.fromList [(f,length (directSubterms t))
                          | t <- concatMap subterms (r : directSubterms l)
                          , Just f <- [rootSymbol t]]

instance (Foldable t,  HasId t) => HasSignature [Rule t v] where
  getSignature rules = Sig{ definedSymbols     = filterByKey (`Set.member` dd) all
                          , constructorSymbols = filterByKey (`Set.notMember` dd) all
                          }
    where
          filterByKey f = Map.filterWithKey (\k _ -> f k)
          dd  = Set.fromList [ root | l :-> _ <- rules, let Just root = rootSymbol l]
          all = Map.fromList [(f,length (directSubterms t))
                                  | l :-> r <- rules
                                  , t <- concatMap subterms [l,r]
                                  , Just f <- [rootSymbol t]]

instance (HasSignature [a]) => HasSignature (Set a) where getSignature = getSignature . toList
instance (Ord a, Ord (Id a), HasSignature (Set a)) => HasSignature [Set a] where getSignature = getSignature . mconcat
instance HasSignature [a] => HasSignature (Map k a) where getSignature = getSignature . Map.elems

mapSignature :: (Ord id, Ord id') => (id -> id') -> Signature id -> Signature id'
mapSignature f (Sig cc dd) = Sig (Map.mapKeys f cc) (Map.mapKeys f dd)

allSymbols :: Ord id => Signature id -> Set id
allSymbols s = Map.keysSet(definedSymbols s) `mappend` Map.keysSet (constructorSymbols s)

arities Sig{..} = constructorSymbols `mappend` definedSymbols

getDefinedSymbols, getConstructorSymbols, getAllSymbols :: ( HasSignature l) => l -> Set (Family.Id l)
getArities :: ( HasSignature sig) => sig -> Map (Family.Id sig) Int
getArity :: ( HasSignature sig) => sig -> Family.Id sig -> Int

getDefinedSymbols     = Map.keysSet . definedSymbols . getSignature
getConstructorSymbols = Map.keysSet . constructorSymbols . getSignature
getAllSymbols         = allSymbols . getSignature

getArities sig = constructorSymbols `mappend` definedSymbols
  where Sig{..} = getSignature sig
getArity l f = fromMaybe (error ("getArity: symbol not in signature"))
                         (Map.lookup f constructorSymbols `mplus` Map.lookup f definedSymbols)
  where  Sig{..} = getSignature l

isConstructorTerm :: (Functor t, Foldable t, HasId t, HasSignature sig, Family.Id1 t ~ Family.Id sig) => sig -> Term t v -> Bool
isConstructorTerm sig t = (`Set.member` getConstructorSymbols sig) `all` collectIds t

isRootDefined :: ( HasId t, HasSignature sig, Family.Id1 t ~ Family.Id sig) => sig -> Term t v -> Bool
isRootDefined sig t
   | Just id <- rootSymbol t = id `Set.member` getDefinedSymbols sig
   | otherwise = False

collectIds :: (Functor t, Foldable t, HasId t) => Term t v -> [Family.Id1 t]
collectIds = catMaybes . foldTerm (const [Nothing]) (\t -> getId t : concat (toList t))

-- -------------
-- * Unification
-- -------------
getUnifier :: (GetUnifier t, Ord (Var t), Functor(TermF t)) => t -> t -> Maybe (SubstitutionFor t)
getUnifier t u = fmap zonkSubst $ execMEnv  (getUnifierM t u)

unifies' :: (Ord (Var t), GetUnifier t, Functor(TermF t)) => t -> t -> Bool
unifies' s t = isJust (getUnifier s t)

class GetUnifier t where
  getUnifierM :: (MonadEnv m, Var t ~ VarM m, TermF t ~ TermFM m, Ord (Var t)) => t -> t -> m ()

instance (Eq var, Unify f) => GetUnifier (Term f var) where
  getUnifierM = unifyM
instance (GetUnifier t) => GetUnifier [t] where
  getUnifierM = getUnifierMdefault


getUnifierMdefault :: (Ord (Var t), GetUnifier t, MonadEnv m, Functor f, Foldable f, Eq (f()),
                      TermFM m ~ TermF t, VarM m ~ Var t) =>
                     f t -> f t -> m ()
getUnifierMdefault t u
    | fmap (const ()) t == fmap (const ()) u = zipWithM_ getUnifierM (toList t) (toList u)
    | otherwise = fail "structure mismatch"

-- ------------
-- * Matching
-- ------------
getMatcher :: (GetMatcher t, Ord (Var t), Functor (TermF t)) => t -> t -> Maybe (SubstitutionFor t)
getMatcher t u = execMEnv (getMatcherM t u)

matches' :: (Ord (Var t), GetMatcher t, Functor (TermF t)) => t -> t -> Bool
matches' s t = isJust (getMatcher s t)

class GetMatcher t
    where getMatcherM :: (MonadEnv m, Var t ~ VarM m, TermF t ~ TermFM m) => t -> t -> m ()

instance (Eq var, Match f) => GetMatcher (Term f var) where
  getMatcherM = matchM
instance (GetMatcher t) => GetMatcher [t] where
  getMatcherM = getMatcherMdefault

getMatcherMdefault :: (GetMatcher t, MonadEnv m, Functor f, Foldable f, Eq (f()),
                       TermF t ~ TermFM m, Var t ~ VarM m) =>
                     f t -> f t -> m ()
getMatcherMdefault t u
    | fmap (const ()) t == fmap (const ()) u = zipWithM_ getMatcherM (toList t) (toList u)
    | otherwise = fail "structure mismatch"

-- ----------------------------
-- * Equivalence up to renaming
-- ----------------------------
--instance (Ord v, Enum v, Ord (Term t v), GetUnifier t v thing, GetVars v thing, GetFresh t v thing) =>
instance (v ~ Var thing, Enum v, Rename v, Ord v,
          Traversable (TermF thing),
          GetMatcher thing, GetVars thing, GetFresh thing) =>
         Eq (EqModulo thing) where
           EqModulo t1 == EqModulo t2 = t1 `equiv2'` t2

equiv' :: (var ~ Var t, Ord var, Enum var, Rename var,
          Traversable (TermF t), Ord (UnwrappedTermFor t),
          GetUnifier t, GetVars t, GetFresh t) => t -> t -> Bool
equiv' t u = maybe False isRenaming (getUnifier (getVariant t u) u)
equiv2' t u = let t' = getVariant t u in matches' t' u && matches' u t'
