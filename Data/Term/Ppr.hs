{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances, OverlappingInstances #-}
module Data.Term.Ppr where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Text.PrettyPrint.HughesPJClass as Pretty

import Data.Term
import Data.Term.Var
import Data.Term.IOVar


--instance Pretty Char where ppr = char
instance Pretty Doc    where pPrint d = d

instance Pretty a => Pretty (Set a)            where pPrint = braces   . hcat . punctuate comma . map pPrint . Set.toList
instance (Pretty k, Pretty a) => Pretty (Map k a) where
    pPrint m = vcat$ concat [[pPrint k, nest 2 (pPrint v)] | (k,v) <-  Map.toList m]

instance (Pretty (f(Free f a)), Pretty a) => Pretty (Term f a) where pPrint (Impure t) = pPrint t; pPrint (Pure a) = pPrint a

instance Pretty Var where
    pPrint (VName v)  = text v
    pPrint (VAuto v_i) = text "V" <> Pretty.int v_i

instance (Pretty var, Pretty (Free termF var)) => Pretty (Substitution termF var) where
    pPrint = braces . hcat . punctuate comma . map (\(v,t) -> pPrint v <+> equals <+> pPrint t) . Map.toList . unSubst

instance Pretty (IOVar t) where pPrint = text . show
instance Pretty a => Pretty (EqModulo a) where pPrint = pPrint . eqModulo