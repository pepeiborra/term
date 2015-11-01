{-# LANGUAGE TypeFamilies #-}

module Data.Term (
-- * Type Families
     Term, Var, Id,
-- * Terms
     TermF, TermFor, UnwrappedTermFor, foldTerm, foldTermM, mapTerm, evalTerm,
-- * Subterms
     subterms, properSubterms, directSubterms, mapSubterms, mapMSubterms, collect,
     someSubterm, someSubterm', someSubtermDeep,
-- * Positions
     Position, positions, (!), (!*), (!?), updateAt, updateAt', updateAtM, occurrences,
-- * Variables
     Rename(..), isVar, vars, isLinear,
-- * Annotating terms
     WithNote(..), WithNote1(..), note, dropNote, noteV, annotateWithPos, annotateWithPosV, annotate,
-- * Ids
     HasId(..), HasId1(..), MapId(..), rootSymbol, mapRootSymbol, mapTermSymbols, mapTermSymbolsM,
-- * Matching & Unification (without occurs check)
     Match(..), Unify(..), unify, unifies, occursIn,
     match, matches, equiv, equiv2, EqModulo(..),
-- * Substitutions
     Substitution, Substitution_(..), SubstitutionFor,
     mapSubst, fromListSubst, domain, codomain, subst, unSubst,
     lookupSubst, applySubst, zonkTerm, zonkTermM, zonkSubst, isEmpty, isRenaming, restrictTo, liftSubst,
     equiv, equiv2, EqModulo(..),
-- * Variables
     GetVars(..), GetFresh(..), getFresh, getVariant, getFreshMdefault,
-- * Environment monad
     MonadEnv(..), find', MEnvT, evalMEnv, execMEnv, runMEnv, evalMEnv, execMEnv, runMEnv,
-- * Fresh monad
     MonadVariant(..), fresh, freshWith, freshWith', variant
     ) where

import Control.Monad.Env
import Control.Monad.Variant
import Data.Term.Base
import Data.Term.Family
import Data.Term.Substitutions
import Prelude.Extras

type instance Id (Lift1 f) = Id f
