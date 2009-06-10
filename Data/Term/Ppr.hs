{-# LANGUAGE UndecidableInstances, OverlappingInstances #-}
module Data.Term.Ppr where

import Data.Char (isAlpha)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Text.PrettyPrint as Ppr

import Data.Term
import Data.Term.Rules
import Data.Term.Simple
import Data.Term.Var
import Data.Term.IOVar

class Ppr a where ppr :: a -> Doc

--instance Ppr Char where ppr = char
instance Ppr Doc    where ppr d = d
instance Ppr String where ppr = text
instance Ppr Int    where ppr = Ppr.int
instance Ppr Bool where ppr = text . show
instance Ppr a => Ppr (Maybe a) where
    ppr Nothing  = text "Nothing"
    ppr (Just a) = text "Just" <+> ppr a
instance Ppr a => Ppr [a]     where ppr = brackets . hcat . punctuate comma . map ppr
instance Ppr () where ppr _ = empty
instance (Ppr a, Ppr b) => Ppr (a,b) where ppr (a,b) = parens (ppr a <> comma <> ppr b)
instance (Ppr a, Ppr b, Ppr c) => Ppr (a,b,c) where ppr (a,b,c) = parens (ppr a <> comma <> ppr b <> comma <> ppr c)
instance (Ppr a, Ppr b, Ppr c, Ppr d) => Ppr (a,b,c,d) where
    ppr (a,b,c,d) = parens (fsep $ punctuate comma [ppr a, ppr b, ppr c, ppr d])
instance Ppr a => Ppr (Set a)            where ppr = braces   . hcat . punctuate comma . map ppr . Set.toList
instance (Ppr k, Ppr a) => Ppr (Map k a) where ppr = vcat . map ppr . Map.toList
instance (Ppr a, Ppr b) => Ppr (Either a b) where ppr = either ppr ppr

instance (Ppr (f(Free f a)), Ppr a) => Ppr (Term f a) where ppr (Impure t) = ppr t; ppr (Pure a) = ppr a

instance Ppr Var where
    ppr (VName v)  = text v
    ppr (VAuto v_i) = text "V" <> Ppr.int v_i

instance (Ppr a, Ppr id) => Ppr (TermF id a) where
    ppr (Term n []) = ppr n
    ppr (Term n [x,y]) | not (any isAlpha $ show $ ppr n) = ppr x <+> ppr n <+> ppr y
    ppr (Term n tt) = ppr n <> parens (hcat$ punctuate comma$ map ppr tt)

instance Ppr a => Ppr (TermF String a) where
    ppr (Term n []) = text n
    ppr (Term n [x,y]) | not (any isAlpha n) = ppr x <+> text n <+> ppr y
    ppr (Term n tt) = text n <> parens (hcat$ punctuate comma $ map ppr tt)

instance Ppr a => Ppr (RuleF a) where
    ppr (l :-> r) = ppr l <+> text "->" <+> ppr r

instance Ppr (IOVar t) where ppr = text . show