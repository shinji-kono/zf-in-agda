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
import OrdUtil
import ODUtil
open Ordinals.Ordinals  O
open Ordinals.IsOrdinals isOrdinal
open Ordinals.IsNext isNext
open OrdUtil O
open ODUtil O

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
V β = TransFinite  V1 β where
   V1 : (x : Ordinal ) → ( ( y : Ordinal) → y o< x → HOD )  → HOD
   V1 x V0 with trio< x o∅
   V1 x V0 | tri< a ¬b ¬c = ⊥-elim ( ¬x<0 a)
   V1 x V0 | tri≈ ¬a refl ¬c = Ord o∅
   V1 x V0 | tri> ¬a ¬b c with Oprev-p  x
   V1 x V0 | tri> ¬a ¬b c | yes p = Power ( V0 (Oprev.oprev p ) (subst (λ k → _ o< k) (Oprev.oprev=x  p) <-osuc ))
   V1 x V0 | tri> ¬a ¬b c | no ¬p = 
        record { od = record { def = λ y → (y o< x ) ∧ ((lt : y o< x ) →  odef (V0 y lt) x ) } ; odmax = x; <odmax = λ {x} lt → proj1 lt }

--
-- L ⊆ HOD ⊆ V
--
-- HOD=V : (x : HOD) → V (odmax x) ∋ x
-- HOD=V x = {!!}

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
L β D = TransFinite  L1 β where
   L1 : (x : Ordinal ) → ( ( y : Ordinal) → y o< x → HOD )  → HOD
   L1 x L0 with trio< x o∅
   L1 x L0 | tri< a ¬b ¬c = ⊥-elim ( ¬x<0 a)
   L1 x L0 | tri≈ ¬a refl ¬c = Ord o∅
   L1 x L0 | tri> ¬a ¬b c with Oprev-p  x
   L1 x L0 | tri> ¬a ¬b c | yes p = Df D ( L0 (Oprev.oprev p ) (subst (λ k → _ o< k) (Oprev.oprev=x  p) <-osuc ))
   L1 x L0 | tri> ¬a ¬b c | no ¬p = 
        record { od = record { def = λ y → (y o< x ) ∧ ((lt : y o< x ) →  odef (L0 y lt) x ) } ; odmax = x; <odmax = λ {x} lt → proj1 lt }

V=L0 : Set (suc n)
V=L0 = (x : Ordinal) → V x ≡  L x record { Definition = λ y → y }
