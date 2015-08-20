{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, UndecidableInstances, TypeSynonymInstances #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeOperators #-}

{-| This module works with an abstract notion of rule.

    A rule is a set of terms (generally a pair) which must
    be treated as a whole. Concrete examples include
    term rewriting rules and prolog clauses.

    To do this the module provides
    generalizations of the unify, match, equiv, fresh and vars
    operations which work with sets of terms.
-}
module Data.Term.Rules
  (RuleF(..), Rule, RuleFor, left, right, HasRules(..), swapRule, IsTRS(..),
   Signature(..), Signature,
   mapSignature, allSymbols, arities, HasSignature(..),
   getArity, getArities, getConstructorSymbols, getDefinedSymbols, getAllSymbols,
   isConstructorTerm, isRootDefined, isDuplicating, collectIds,
   GetVars(..),
   GetUnifier(..), getUnifier, unifies', equiv', equiv2', getUnifierMdefault,
   GetMatcher(..), getMatcher, matches', getMatcherMdefault,
   GetFresh(..), getFresh, getVariant, getFreshMdefault
  ) where


import Control.Applicative.Compose
import Control.DeepSeq
import Control.DeepSeq.Extras
import Control.Monad.Free

import Data.Foldable (Foldable, foldMap, toList)

import Data.Maybe


import qualified Data.Traversable as T
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Term.Substitutions
import Control.Monad.Variant
import Prelude.Extras

import Data.Term hiding (Rule)



import qualified Data.Id.Family as Family
import qualified Data.Rule.Family as Family

import Debug.Hoed.Observe

-- ----------------
-- * Concrete rules
-- ----------------
infix 1 :->
data RuleF a = (:->) {lhs,rhs::a} deriving (Eq, Ord, Show)
instance Eq1 RuleF where (==#) = (==)
instance Functor RuleF where fmap f (l :-> r) = f l :-> f r
instance Foldable RuleF where foldMap f (l :-> r) = f l `mappend` f r
instance Traversable RuleF where traverse f (l :-> r) = (:->) <$> f l <*> f r
instance GetFresh a => GetFresh (RuleF a) where getFreshM = getFreshMdefault
instance GetVars t => GetVars (RuleF t) where getVars = foldMap getVars
instance Applicative RuleF where
  pure x = x :-> x
  (fa :-> fb) <*> (a :-> b) = fa a :-> fb b
instance (Eq v, Unify t) => GetUnifier (Rule t v) where getUnifierM = getUnifierMdefault
instance (Eq v, Match t) => GetMatcher (Rule t v) where getMatcherM = getMatcherMdefault
type instance Var (RuleF a) = Var a
type instance TermF (RuleF a) = TermF a
type instance Id (RuleF a) = Id a

instance NFData1 RuleF where
  rnf1 (a :-> b) = rnf a `seq` rnf b `seq` ()
instance NFData a => NFData (RuleF a) where rnf = rnf1

type Rule t v = RuleF (Term t v)
type RuleFor (t :: k)  = Rule (TermF t) (Var t)

{-# RULES "rules/tRS" forall x. tRS (rules x) = x #-}
{-# RULES "tRS/rules" forall x. rules (tRS x) = x #-}


class HasRules trs where
  rules :: trs -> [Family.Rule trs]
class HasRules trs => IsTRS trs where tRS :: [Family.Rule trs] -> trs

type instance Family.Rule (RuleF a) = RuleF a

instance HasRules (RuleF a) where rules = (:[])
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

instance Foldable Signature where
  foldMap f Sig{..} =
    foldMap f (Map.keys constructorSymbols) `mappend` foldMap f (Map.keys definedSymbols)

type instance Family.Id (Signature id) = id

instance Ord id => Monoid (Signature id) where
    mempty  = Sig mempty mempty
    mappend (Sig c1 s1) (Sig c2 s2) = Sig c s where
      c = mappend c1 c2 `Map.difference` s
      s = mappend s1 s2

instance Ord id => HasSignature (Signature id) where
    getSignature = id

instance NFData1 Signature where
  rnf1 (Sig cc dd) = rnf cc `seq` rnf dd `seq` ()

instance NFData a => NFData (Signature a) where rnf = rnf1

class Ord (Family.Id l) => HasSignature l where
  getSignature :: l -> Signature (Family.Id l)

instance (HasId1 t, Foldable t, Ord(Id t)) => HasSignature (Term t v) where
  getSignature t = Sig{ definedSymbols = Map.empty
                      , constructorSymbols = all }
     where
      all =  Map.fromList [(f,length (directSubterms t))
                                  | t <- subterms t
                                  , Just f <- [rootSymbol t]]

instance (HasSignature a, Foldable f, Ord(Id (f a)), Id (f a) ~ Id a
         ) => HasSignature (f a) where
  getSignature = foldMap getSignature

instance (HasId a, HasSignature a) => HasSignature (RuleF a) where
  getSignature (l :-> r)
    | Just d <- getId l
    = all `mappend` mempty { definedSymbols = Map.singleton d (getArity all d) }
    | otherwise
    = all
    where
      all = foldMap getSignature [l,r]

instance (HasSignature [a]) => HasSignature (Set a) where getSignature = getSignature . toList
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

isConstructorTerm :: (Functor t, Foldable t, HasId1 t, HasSignature sig, Family.Id t ~ Family.Id sig) => sig -> Term t v -> Bool
isConstructorTerm sig t = (`Set.member` getConstructorSymbols sig) `all` collectIds t

isRootDefined :: ( HasId1 t, HasSignature sig, Family.Id t ~ Family.Id sig) => sig -> Term t v -> Bool
isRootDefined sig t
   | Just id <- rootSymbol t = id `Set.member` getDefinedSymbols sig
   | otherwise = False

isDuplicating :: (Foldable termF, Functor termF, Ord v) => RuleF (Term termF v) -> Bool
isDuplicating (l :-> r) = any (\(v,occurrences) -> occurrences > occurrences_in_l v)
                              (Map.toList $ vars_r)
  where
      count xx = Map.fromListWith (+) [(x,1::Int) | x <- xx]
      vars_r = count (vars r)
      vars_l = count (vars l)
      occurrences_in_l v = fromMaybe 0 $ Map.lookup v vars_l


collectIds :: (Functor t, Foldable t, HasId1 t) => Term t v -> [Family.Id t]
collectIds = catMaybes . foldTerm (const [Nothing]) (\t -> getId1 t : concat (toList t))

-- -------------
-- * Unification
-- -------------

getUnifier :: (GetUnifier t, Observable (Var t), Ord (Var t), Functor(TermF t), Foldable(TermF t)
              ) => t -> t -> Maybe (SubstitutionFor t)
getUnifier t u = fmap zonkSubst $ execMEnv  (getUnifierM t u)

unifies' :: (Observable(Var t), Ord (Var t), GetUnifier t, Functor(TermF t), Foldable(TermF t)
            ) => t -> t -> Bool
unifies' s t = isJust (getUnifier s t)

class GetUnifier t where
  getUnifierM :: (MonadEnv m, Var t ~ Var m, TermF t ~ TermF m, Ord (Var t)) => t -> t -> m ()

instance (Eq var, Unify f) => GetUnifier (Term f var) where
  getUnifierM = unifyM
instance (GetUnifier t) => GetUnifier [t] where
  getUnifierM = getUnifierMdefault


getUnifierMdefault :: (Ord (Var t), GetUnifier t, MonadEnv m, Match f,
                      TermF m ~ TermF t, Var m ~ Var t) =>
                     f t -> f t -> m ()
getUnifierMdefault t u = do
  constraints <- T.sequence (getUnifierM <$> Compose(Just t) <*> Compose(Just u))
  when (not $ isJust $ decompose constraints) $ fail "structure mismatch"
  return ()

-- ------------
-- * Matching
-- ------------

getMatcher :: (GetMatcher t, Observable (Var t), Ord (Var t), Functor (TermF t), Foldable(TermF t)
              ) => t -> t -> Maybe (SubstitutionFor t)
getMatcher t u = execMEnv (getMatcherM t u)

matches' :: (Observable (Var t), Ord (Var t), GetMatcher t, Functor (TermF t), Foldable(TermF t)
            ) => t -> t -> Bool
matches' s t = isJust (getMatcher s t)

class GetMatcher t
    where getMatcherM :: (MonadEnv m, Var t ~ Var m, TermF t ~ TermF m) => t -> t -> m ()

instance (Eq var, Match f) => GetMatcher (Term f var) where
  getMatcherM = matchM
instance (GetMatcher t) => GetMatcher [t] where
  getMatcherM = getMatcherMdefault

getMatcherMdefault :: (Match f, GetMatcher t, MonadEnv m,
                       TermF t ~ TermF m, Var t ~ Var m) =>
                     f t -> f t -> m ()
getMatcherMdefault t u = do
  constraints <- T.sequence(getMatcherM <$> Compose(Just t) <*> Compose(Just u))
  when (not $ isJust $ decompose constraints) $ fail "structure mismatch"
  return ()


-- ----------------------------
-- * Equivalence up to renaming
-- ----------------------------
--instance (Ord v, Enum v, Ord (Term t v), GetUnifier t v thing, GetVars v thing, GetFresh t v thing) =>
instance (v ~ Var thing, Enum v, Rename v, Ord v, Observable v,
          Traversable (TermF thing),
          GetMatcher thing, GetVars thing, GetFresh thing) =>
         Eq (EqModulo thing) where
           EqModulo t1 == EqModulo t2 = t1 `equiv2'` t2

equiv' :: (var ~ Var t, Ord var, Enum var, Rename var, Observable var,
          Traversable (TermF t), Ord (TermFor t),
          GetMatcher t, GetVars t, GetFresh t) => t -> t -> Bool
equiv' t u = maybe False isRenaming (getMatcher (getVariant t u) u)
equiv2' t u = let t' = getVariant t u in matches' t' u && matches' u t'

instance (Ord v, Rename v, Enum v, Observable v, Unify t, Ord (Term t v)) => Eq (EqModulo (Rule t v)) where
    EqModulo t1 == EqModulo t2 = t1 `equiv'` t2

instance (Ord v, Rename v, Enum v, Observable v, Unify t, Ord (Term t v)) => Ord (EqModulo (Rule t v)) where
    t1 `compare` t2 = if t1 == t2 then EQ else compare (eqModulo t1) (eqModulo t2)


-- ------------------
-- * Other instances
-- ------------------
instance Observable1 RuleF where observer1 (l :-> r) = send "(:->)" (return (:->) << l << r)
instance Observable a => Observable (RuleF a) where
  observers = observers1
  observer  = observer1
