open import Level
open import Ordinals
module VL {n : Level } (O : Ordinals {n}) where

open import zf
open import logic
import OD 
open import Relation.Nullary 
open import Relation.Binary 
open import Data.Empty 
open import Relation.Binary
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality
open import Data.Nat renaming ( zero to Zero ; suc to Suc ;  ℕ to Nat ; _⊔_ to _n⊔_ ) 
import BAlgbra 
open BAlgbra O
open inOrdinal O
open OD O
open OD.OD
open ODAxiom odAxiom
-- import ODC
open _∧_
open _∨_
open Bool
open HOD

-- The cumulative hierarchy 
--    V 0 := ∅ 
--    V α + 1 := P ( V α ) 
--    V α := ⋃ { V β | β < α }

V : ( β : Ordinal ) → HOD
V β = TransFinite1  Vβ₁ β where
   Vβ₁ : (x : Ordinal ) → ( ( y : Ordinal) → y o< x → HOD )  → HOD
   Vβ₁ x Vβ₀ with trio< x o∅
   Vβ₁ x Vβ₀ | tri< a ¬b ¬c = ⊥-elim ( ¬x<0 a)
   Vβ₁ x Vβ₀ | tri≈ ¬a refl ¬c = Ord o∅
   Vβ₁ x Vβ₀ | tri> ¬a ¬b c with Oprev-p  x
   Vβ₁ x Vβ₀ | tri> ¬a ¬b c | yes p = Power ( Vβ₀ (Oprev.oprev p ) (subst (λ k → _ o< k) (Oprev.oprev=x  p) <-osuc ))
   Vβ₁ x Vβ₀ | tri> ¬a ¬b c | no ¬p = 
        record { od = record { def = λ y → (y o< x ) ∧ ((lt : y o< x ) →  odef (Vβ₀ y lt) x ) } ; odmax = x; <odmax = λ {x} lt → proj1 lt }

--
-- Definition for Power Set
--
record Definitions  : Set (suc n) where
   field
      Definition : HOD → HOD   

open Definitions

Df : Definitions → (x : HOD) → HOD
Df D x = Power x ∩ Definition D x 

-- The constructible Sets
--    L 0 := ∅ 
--    L α + 1 := Df (L α)   -- Definable Power Set
--    V α := ⋃ { L β | β < α }

L : ( β : Ordinal ) → Definitions → HOD
L β D = TransFinite1  Lβ₁ β where
   Lβ₁ : (x : Ordinal ) → ( ( y : Ordinal) → y o< x → HOD )  → HOD
   Lβ₁ x Lβ₀ with trio< x o∅
   Lβ₁ x Lβ₀ | tri< a ¬b ¬c = ⊥-elim ( ¬x<0 a)
   Lβ₁ x Lβ₀ | tri≈ ¬a refl ¬c = Ord o∅
   Lβ₁ x Lβ₀ | tri> ¬a ¬b c with Oprev-p  x
   Lβ₁ x Lβ₀ | tri> ¬a ¬b c | yes p = Df D ( Lβ₀ (Oprev.oprev p ) (subst (λ k → _ o< k) (Oprev.oprev=x  p) <-osuc ))
   Lβ₁ x Lβ₀ | tri> ¬a ¬b c | no ¬p = 
        record { od = record { def = λ y → (y o< x ) ∧ ((lt : y o< x ) →  odef (Lβ₀ y lt) x ) } ; odmax = x; <odmax = λ {x} lt → proj1 lt }

V=L0 : Set (suc n)
V=L0 = (x : Ordinal) → V x ≡  L x record { Definition = λ y → y }
