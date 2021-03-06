{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.Term.Ppr where

import           Control.Monad.Free
import qualified Data.Map                       as Map
import           Text.PrettyPrint.HughesPJClass as Pretty
import           Data.Foldable (Foldable)
import           Data.Term hiding (Var)
import qualified Data.Var.Family as Family
import           Data.Term.Rules
import           Data.Term.Var
import           Data.Term.IOVar
import           Data.Term.Substitutions


instance (Pretty (f(Term f a)), Pretty a) => Pretty (Term f a) where
    pPrint (Impure t) = pPrint t
    pPrint (Pure a) = pPrint a

instance Pretty Var where
    pPrint (VName v)  = text v
    pPrint (VAuto v_i) = text "V" <> Pretty.int v_i

instance Pretty a => Pretty (RuleF a) where
    pPrint (l :-> r) = pPrint l <+> text "->" <+> pPrint r

instance (Pretty a, Pretty(Family.Var a), Ord(Family.Var a)
         ) => Pretty (Substitution_ a) where
    pPrint = braces . hcat . punctuate comma . map (\(v,t) -> pPrint v <+> equals <+> pPrint t) . Map.toList . unSubst

instance Pretty (IOVar t) where pPrint = text . show
instance Pretty a => Pretty (EqModulo a) where pPrint = pPrint . eqModulo
