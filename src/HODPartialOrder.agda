{-# OPTIONS --cubical-compatible --safe #-}
open import Level
open import Ordinals
import HODBase
import OD
open import Relation.Binary.Structures using (IsStrictPartialOrder)
open import  Relation.Binary.PropositionalEquality hiding ( [_] )

module HODPartialOrder {n : Level } (O : Ordinals {n} ) (HODAxiom : HODBase.ODAxiom O)  (ho< : OD.ODAxiom-ho< O HODAxiom )
       (AC : OD.AxiomOfChoice O HODAxiom )  (_<_ : (x y : HODBase.HOD O ) → Set n ) (PO : IsStrictPartialOrder _≡_ _<_ )
   where

-- open import Data.Nat renaming ( zero to Zero ; suc to Suc ;  ℕ to Nat ; _⊔_ to _n⊔_ )
open import Data.Empty
open import Data.Unit
open import Relation.Nullary
open import Relation.Binary  hiding (_⇔_)
open import Relation.Binary.Core hiding (_⇔_)
import Relation.Binary.Reasoning.Setoid as EqR
open import Induction.WellFounded

open import logic
import OrdUtil
open import nat

open Ordinals.Ordinals  O
open Ordinals.IsOrdinals isOrdinal
-- open Ordinals.IsNext isNext
open OrdUtil O
import ODUtil
open ODUtil O HODAxiom ho<
import ODC

-- Ordinal Definable Set

open HODBase.HOD
open HODBase.OD

open _∧_
open _∨_
open Bool

open  HODBase._==_

open HODBase.ODAxiom HODAxiom
open OD O HODAxiom
open AxiomOfChoice AC

open _∧_
open _∨_
open Bool


<-TransFinite : {ψ : HOD → Set n} 
     → WellFounded _<_ 
     → ({x : HOD} → ({y : HOD} → y < x → ψ y) → ψ x ) → (x : HOD) → ψ x
<-TransFinite {ψ} wfa ind x = induction x (wfa x) where
     induction : (x : HOD) → Acc _<_ x → ψ x
     induction x (acc rs) = ind {x} (λ {y} y<x → induction y (rs y<x) ) 
