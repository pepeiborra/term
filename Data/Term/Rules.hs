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
   Signature(..), mapSignature, allSymbols, HasSignature(..),
   getArity, getArities, getConstructorSymbols, getDefinedSymbols, getAllSymbols,
   isConstructorTerm, isRootDefined, collectIds,
   GetVars(..),
   GetUnifier(..), getUnifier, unifies', equiv', equiv2', getUnifierMdefault,
   GetMatcher(..), getMatcher, matches', getMatcherMdefault,
   GetFresh(..), getFresh, getVariant, getFreshMdefault
  ) where

import Control.Applicative
import Control.Monad.Free
#ifdef TRANSFORMERS
import Control.Monad.Trans.State (evalState, execStateT, evalStateT)
#else
import Control.Monad.State (evalState, execStateT, evalStateT)
#endif
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

import Data.Term
import Data.Term.Var
import Data.Term.IOVar


-- ----------------
-- * Concrete rules
-- ----------------
infix 1 :->
data RuleF a = (:->) {lhs,rhs::a} deriving (Eq, Ord, Show)
instance Functor RuleF where fmap f (l :-> r) = f l :-> f r
instance Foldable RuleF where foldMap f (l :-> r) = f l `mappend` f r
instance Traversable RuleF where traverse f (l :-> r) = (:->) <$> f l <*> f r
instance Traversable t => GetFresh t v (Rule t v) where getFreshM = getFreshMdefault
instance (Eq v, Traversable t, Eq (t())) => GetUnifier t v (Rule t v) where getUnifierM = getUnifierMdefault
instance (Eq v, Traversable t, Eq (t())) => GetMatcher t v (Rule t v) where getMatcherM = getMatcherMdefault

type Rule t v = RuleF (Term t v)

{-# RULES "rules/tRS" forall x. tRS (rules x) = x #-}
{-# RULES "tRS/rules" forall x. rules (tRS x) = x #-}

class HasRules t v trs | trs -> t v where rules :: trs -> [Rule t v]
class HasRules t v trs => IsTRS t v trs | trs -> t v where tRS :: [Rule t v] -> trs

instance HasRules t v (Rule t v)            where rules = (:[])
instance HasRules t v a => HasRules t v [a] where rules = foldMap rules
instance IsTRS    t v [Rule t v]            where tRS   = id

swapRule :: RuleF a -> RuleF a
swapRule (l :-> r) = r :-> l

left,right :: (a -> a) -> RuleF a -> RuleF a

left f (l :-> r)  = f l :-> r
right f (l :-> r) = l   :-> f r

-- -----------
-- * Variables
-- -----------
class Ord var => GetVars var t | t -> var where getVars :: t -> Set var
instance (Functor termF, Foldable termF, Ord var) => GetVars var (Term termF var) where getVars = Set.fromList . toList
instance (GetVars var t, Foldable f) => GetVars var (f t) where getVars = foldMap getVars
--instance (GetVars t var, Foldable f, Foldable g) => GetVars (g(f t)) var where getVars = (foldMap.foldMap) getVars

instance GetVars Var Var where getVars = Set.singleton
instance GetVars (IOVar t) (IOVar t) where getVars = Set.singleton

-- ------------------------------------------
-- * GetFresh: Variants
-- ------------------------------------------

class (Traversable termF) => GetFresh termF var thing | thing -> termF var where
    getFreshM :: (MonadFresh var m, MonadEnv termF var m) => thing -> m thing
instance (Traversable termF) => GetFresh termF var (Term termF var) where
    getFreshM = fresh
instance (Traversable termF, GetFresh termF var t) => GetFresh termF var [t] where
    getFreshM = getFreshMdefault

getFreshMdefault :: (Traversable t, GetFresh term v a, MonadFresh v m, MonadEnv term v m) => t a -> m (t a)
getFreshMdefault = T.mapM getFreshM

getFresh :: forall t v m thing. (Ord v, MonadFresh v m, GetFresh t v thing) => thing -> m thing
getFresh t = evalStateT (getFreshM t) (mempty :: Substitution t v)

getVariant :: (Enum v, GetFresh termF v t, GetVars v t') => t -> t' -> t
getVariant u t = evalState (getFresh u) ([toEnum 0..] \\ Set.toList (getVars t))

-- ---------------------
-- * Signatures
-- ---------------------
data Signature id = Sig {constructorSymbols, definedSymbols :: Map id Int}
   deriving (Eq, Ord, Show)

instance Ord id => Monoid (Signature id) where
    mempty  = Sig mempty mempty
    mappend (Sig c1 s1) (Sig c2 s2) = Sig (mappend c1 c2) (mappend s1 s2)

instance Ord id => HasSignature (Signature id) where
    type SignatureId (Signature id) = id
    getSignature = id

class Ord (SignatureId l) => HasSignature l where
  type SignatureId l :: *
  getSignature :: l -> Signature (SignatureId l)

instance (HasId t, Foldable t) => HasSignature (Term t v) where
  type SignatureId (Term t v) = TermId t
  getSignature t = Sig{ definedSymbols = Map.empty
                        , constructorSymbols = all }
     where
      all =  Map.fromList [(f,length (directSubterms t))
                                  | t <- subterms t
                                  , Just f <- [rootSymbol t]]

instance (Foldable t, HasId t) => HasSignature [Term t v] where
  type SignatureId [Term t v] = TermId t
  getSignature terms = Sig{ definedSymbols     = Map.empty
                          , constructorSymbols = all
                          }
    where all =  Map.fromList [(f,length (directSubterms t))
                                  | t <- concatMap subterms terms
                                  , Just f <- [rootSymbol t]]


instance (Foldable t,  HasId t) => HasSignature (Rule t v) where
  type SignatureId (Rule t v) = TermId t
  getSignature (l :-> r) = Sig{ definedSymbols = Map.singleton d (length $ directSubterms l)
                              , constructorSymbols = all}
    where Just d = rootSymbol l
          all = Map.fromList [(f,length (directSubterms t))
                                  | t <- concatMap subterms (r : directSubterms l)
                                  , Just f <- [rootSymbol t]]

instance (Foldable t,  HasId t) => HasSignature [Rule t v] where
  type SignatureId [Rule t v] = TermId t
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

instance (HasSignature [a]) => HasSignature (Set a) where
  type SignatureId (Set a) = SignatureId [a]
  getSignature = getSignature . toList

mapSignature :: (Ord id, Ord id') => (id -> id') -> Signature id -> Signature id'
mapSignature f (Sig cc dd) = Sig (Map.mapKeys f cc) (Map.mapKeys f dd)

allSymbols :: Ord id => Signature id -> Set id
allSymbols s = Map.keysSet(definedSymbols s) `mappend` Map.keysSet (constructorSymbols s)

getDefinedSymbols, getConstructorSymbols, getAllSymbols :: ( HasSignature l) => l -> Set (SignatureId l)
getArities :: ( HasSignature sig) => sig -> Map (SignatureId sig) Int
getArity :: ( HasSignature sig) => sig -> SignatureId sig -> Int

getDefinedSymbols     = Map.keysSet . definedSymbols . getSignature
getConstructorSymbols = Map.keysSet . constructorSymbols . getSignature
getAllSymbols         = allSymbols . getSignature

getArities sig = constructorSymbols `mappend` definedSymbols
  where Sig{..} = getSignature sig
getArity l f = fromMaybe (error ("getArity: symbol not in signature"))
                         (Map.lookup f constructorSymbols `mplus` Map.lookup f definedSymbols)
  where  Sig{..} = getSignature l

isConstructorTerm :: (Foldable t, HasId t, HasSignature sig, TermId t ~ SignatureId sig) => sig -> Term t v -> Bool
isConstructorTerm sig t = (`Set.member` getConstructorSymbols sig) `all` collectIds t

isRootDefined :: ( HasId t, HasSignature sig, TermId t ~ SignatureId sig) => sig -> Term t v -> Bool
isRootDefined sig t
   | Just id <- rootSymbol t = id `Set.member` getDefinedSymbols sig
   | otherwise = False

collectIds :: (Foldable t, HasId t) => Term t v -> [TermId t]
collectIds = catMaybes . foldTerm (const [Nothing]) (\t -> getId t : concat (toList t))

-- -------------
-- * Unification
-- -------------
getUnifier :: (GetUnifier termF var t, Ord var) => t -> t -> Maybe (Substitution termF var)
getUnifier t u = execStateT (getUnifierM t u) mempty

unifies' :: forall termF v t. (Ord v, GetUnifier termF v t) => t -> t -> Bool
unifies' s t = isJust (getUnifier s t)

class Functor termF => GetUnifier termF var t | t -> termF var
    where getUnifierM :: (MonadEnv termF var m, Ord var) => t -> t -> m ()

instance (Eq var, Unify f) => GetUnifier f var (Term f var) where
  getUnifierM = unifyM
instance (GetUnifier termF var t) => GetUnifier termF var [t] where
  getUnifierM = getUnifierMdefault


getUnifierMdefault :: (Ord var, GetUnifier termF var t, MonadEnv termF var m, Functor f, Foldable f, Eq (f())) =>
                     f t -> f t -> m ()
getUnifierMdefault t u
    | fmap (const ()) t == fmap (const ()) u = zipWithM_ getUnifierM (toList t) (toList u)
    | otherwise = fail "structure mismatch"

-- ------------
-- * Matching
-- ------------
getMatcher :: (GetMatcher termF var t, Ord var) => t -> t -> Maybe (Substitution termF var)
getMatcher t u = execStateT (getMatcherM t u) mempty

matches' :: (Ord v, GetMatcher termF v t) => t -> t -> Bool
matches' s t = isJust (getMatcher s t)

class Functor termF =>  GetMatcher termF var t | t -> termF var
    where getMatcherM :: MonadEnv termF var m => t -> t -> m ()

instance (Eq var, Match f) => GetMatcher f var (Term f var) where
  getMatcherM = matchM
instance (GetMatcher termF var t) => GetMatcher termF var [t] where
  getMatcherM = getMatcherMdefault

getMatcherMdefault :: (GetMatcher termF var t, MonadEnv termF var m, Functor f, Foldable f, Eq (f())) =>
                     f t -> f t -> m ()
getMatcherMdefault t u
    | fmap (const ()) t == fmap (const ()) u = zipWithM_ getMatcherM (toList t) (toList u)
    | otherwise = fail "structure mismatch"

-- ----------------------------
-- * Equivalence up to renaming
-- ----------------------------
--instance (Ord v, Enum v, Ord (Term t v), GetUnifier t v thing, GetVars v thing, GetFresh t v thing) =>
instance (Enum v, GetMatcher t v thing, GetVars v thing, GetFresh t v thing) =>
         Eq (EqModulo thing) where
           EqModulo t1 == EqModulo t2 = t1 `equiv2'` t2

equiv' :: forall termF var t.
         (Ord var, Enum var, Ord (Term termF var),
         GetUnifier termF var t, GetVars var t, GetFresh termF var t) => t -> t -> Bool
equiv' t u = maybe False isRenaming (getUnifier (getVariant t u) u)
equiv2' t u = let t' = getVariant t u in matches' t' u && matches' u t'
