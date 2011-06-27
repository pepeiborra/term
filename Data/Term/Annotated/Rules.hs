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
module Data.Term.Annotated.Rules
  (RuleF(..), Rule, left, right, HasRules(..), swapRule, IsTRS(..),
   Signature(..), R.mapSignature, R.allSymbols, HasSignature(..),
   R.getArity, R.getArities, R.getConstructorSymbols, R.getDefinedSymbols, R.getAllSymbols,
   isConstructorTerm, isRootDefined, collectIds,
   GetVars(..),
   GetUnifier(..), getUnifier, unifies', equiv', getUnifierMdefault,
   GetMatcher(..), getMatcher, matches', getMatcherMdefault,
   GetFresh(..), getFresh, getVariant, getFreshMdefault
  ) where

import           Control.Applicative
import           Control.Monad                (zipWithM_)
import           Control.Monad.Free.Annotated
import           Control.Monad.State          (evalState, execStateT, evalStateT)
import           Data.Foldable                (Foldable, foldMap, toList)
import           Data.List                    ((\\))
import           Data.Maybe
import           Data.Monoid
import           Data.Traversable             (Traversable)
import qualified Data.Traversable             as T
import qualified Data.Map                     as Map
import qualified Data.Set                     as Set

import           Data.Term.Annotated
import           Data.Term.Rules              (RuleF(..), Signature(..), HasSignature(..), GetVars(..)
                                              ,getConstructorSymbols, getDefinedSymbols)
import qualified Data.Term.Rules              as R

-- ----------------
-- * Concrete rules
-- ----------------
instance (Measured v ann, Traversable t) => GetFresh ann t v (Rule ann t v) where getFreshM = getFreshMdefault
instance (Measured v ann, Eq v, Traversable t, Eq (t())) => GetUnifier ann t v (Rule ann t v) where getUnifierM = getUnifierMdefault
instance (Measured v ann, Eq v, Traversable t, Eq (t())) => GetMatcher ann t v (Rule ann t v) where getMatcherM = getMatcherMdefault

type Rule ann t v = RuleF (Term ann t v)

{-# RULES "rules/tRS" forall x. tRS (rules x) = x #-}
{-# RULES "tRS/rules" forall x. rules (tRS x) = x #-}

class HasRules ann t v trs | trs -> ann t v where rules :: trs -> [Rule ann t v]
class HasRules ann t v trs => IsTRS ann t v trs | trs -> ann t v where tRS :: [Rule ann t v] -> trs

instance HasRules ann t v (Rule ann t v)            where rules = (:[])
instance HasRules ann t v a => HasRules ann t v [a] where rules = foldMap rules
instance IsTRS    ann t v [Rule ann t v]            where tRS   = id

swapRule :: RuleF a -> RuleF a
swapRule (l :-> r) = r :-> l

left,right :: (a -> a) -> RuleF a -> RuleF a

left f (l :-> r)  = f l :-> r
right f (l :-> r) = l   :-> f r

-- -----------
-- * Variables
-- -----------
instance (Functor termF, Foldable termF, Ord var) => GetVars var (Term ann termF var) where getVars = Set.fromList . toList

-- ------------------------------------------
-- * GetFresh: Variants
-- ------------------------------------------

class (Traversable termF) => GetFresh ann termF var thing | thing -> ann termF var where
    getFreshM :: (MonadVariant var m, MonadEnv ann termF var m) => thing -> m thing
instance (Monoid ann, Measured var ann, Traversable termF) => GetFresh ann termF var (Term ann termF var) where
    getFreshM = fresh
instance (Traversable termF, GetFresh ann termF var t) => GetFresh ann termF var [t] where
    getFreshM = getFreshMdefault

getFreshMdefault :: (Traversable t, GetFresh ann term v a, MonadVariant v m, MonadEnv ann term v m) => t a -> m (t a)
getFreshMdefault = T.mapM getFreshM

getFresh :: forall ann t v m thing. (Ord v, Measured v ann, MonadVariant v m, GetFresh ann t v thing) => thing -> m thing
getFresh t = evalStateT (getFreshM t) (mempty :: Substitution ann t v)

getVariant :: (Monoid ann, Measured v ann, Enum v, Rename v, GetFresh ann termF v t, GetVars v t') => t -> t' -> t
getVariant u t = evalState (getFresh u) ([toEnum 0..] \\ Set.toList (getVars t))

-- ---------------------
-- * Signatures
-- ---------------------

instance (HasId t, Functor t, Foldable t) => HasSignature (Term ann t v) where
  type SignatureId (Term ann t v) = TermId t
  getSignature t = Sig{ definedSymbols = Map.empty
                        , constructorSymbols = all }
     where
      all =  Map.fromList [(f,length (directSubterms t))
                                  | t <- subterms t
                                  , Just f <- [rootSymbol t]]

instance (Functor t, Foldable t, HasId t) => HasSignature [Term ann t v] where
  type SignatureId [Term ann t v] = TermId t
  getSignature terms = Sig{ definedSymbols     = Map.empty
                          , constructorSymbols = all
                          }
    where all =  Map.fromList [(f,length (directSubterms t))
                                  | t <- concatMap subterms terms
                                  , Just f <- [rootSymbol t]]


instance (Functor t, Foldable t,  HasId t) => HasSignature (Rule ann t v) where
  type SignatureId (Rule ann t v) = TermId t
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

instance (Functor t, Foldable t,  HasId t) => HasSignature [Rule ann t v] where
  type SignatureId [Rule ann t v] = TermId t
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


isConstructorTerm :: (Functor t, Foldable t, HasId t, HasSignature sig, TermId t ~ SignatureId sig) => sig -> Term ann t v -> Bool
isConstructorTerm sig t =  (`Set.member` getConstructorSymbols sig) `all` collectIds t

isRootDefined :: ( HasId t, HasSignature sig, TermId t ~ SignatureId sig) => sig -> Term ann t v -> Bool
isRootDefined sig t
   | Just id <- rootSymbol t = id `Set.member` getDefinedSymbols sig
   | otherwise = False

collectIds :: (Functor t, Foldable t, HasId t) => Term ann t v -> [TermId t]
collectIds = catMaybes . foldTerm (const [Nothing]) (\t -> getId t : concat (toList t))

-- -------------
-- * Unification
-- -------------
getUnifier :: (Foldable termF, Measured var ann, GetUnifier ann termF var t, Ord var) =>
              t -> t -> Maybe (Substitution ann termF var)
getUnifier t u = zonkSubst <$> execStateT (getUnifierM t u) mempty

unifies' :: forall ann termF v t.
            (Measured v ann, Foldable termF, Ord v, GetUnifier ann termF v t) =>
            t -> t -> Bool
unifies' s t = isJust (getUnifier s t)

class Functor termF => GetUnifier ann termF var t | t -> ann termF var
    where getUnifierM :: (MonadEnv ann termF var m, Ord var) => t -> t -> m ()

instance (Monoid ann, Measured var ann, Eq var, Unify f) => GetUnifier ann f var (Term ann f var) where
  getUnifierM = unifyM
instance (GetUnifier ann termF var t) => GetUnifier ann termF var [t] where
  getUnifierM = getUnifierMdefault


getUnifierMdefault :: (Ord var, GetUnifier ann termF var t, MonadEnv ann termF var m, Functor f, Foldable f, Eq (f())) =>
                     f t -> f t -> m ()
getUnifierMdefault t u
    | (const () <$> t) == (const () <$> u) = zipWithM_ getUnifierM (toList t) (toList u)
    | otherwise = fail "structure mismatch"

-- ------------
-- * Matching
-- ------------
getMatcher :: (Foldable termF, Measured var ann, GetMatcher ann termF var t, Ord var) =>
              t -> t -> Maybe (Substitution ann termF var)
getMatcher t u = execStateT (getMatcherM t u) mempty

matches' :: (Ord v, Measured v ann, Foldable termF, GetMatcher ann termF v t) => t -> t -> Bool
matches' s t = isJust (getMatcher s t)

class Functor termF =>  GetMatcher ann termF var t | t -> ann termF var
    where getMatcherM :: MonadEnv ann termF var m => t -> t -> m ()

instance (Eq var, Measured var ann, Match f) => GetMatcher ann f var (Term ann f var) where
  getMatcherM = matchM
instance (GetMatcher ann termF var t) => GetMatcher ann termF var [t] where
  getMatcherM = getMatcherMdefault

getMatcherMdefault :: (GetMatcher ann termF var t, MonadEnv ann termF var m, Functor f, Foldable f, Eq (f())) =>
                     f t -> f t -> m ()
getMatcherMdefault t u
    | (const () <$> t) == (const () <$> u) = zipWithM_ getMatcherM (toList t) (toList u)
    | otherwise = fail "structure mismatch"

-- ----------------------------
-- * Equivalence up to renaming
-- ----------------------------
--instance (Ord v, Enum v, Ord (Term t v), GetUnifier t v thing, GetVars v thing, GetFresh t v thing) =>
instance (Enum v, Rename v, Measured v ann, GetMatcher ann t v thing, GetVars v thing, GetFresh ann t v thing) =>
         Eq (EqModulo thing) where
           EqModulo t1 == EqModulo t2 = t1 `equiv'` t2
{-
equiv' :: forall termF var t ann.
         (Ord var, Enum var, Rename var, Ord (Term ann termF var),
         GetUnifier ann termF var t, GetVars var t, GetFresh ann termF var t,
         Measured var ann
         ) => t -> t -> Bool
equiv' t u = maybe False isRenaming (getUnifier (getVariant t u) u)
-}

equiv' :: forall termF var t ann.
         (Foldable termF, Ord var, Enum var, Rename var, Measured var ann,
         GetMatcher ann termF var t, GetVars var t, GetFresh ann termF var t
         ) => t -> t -> Bool
equiv' t u = let t' = getVariant t u in matches' t' u && matches' u t'
