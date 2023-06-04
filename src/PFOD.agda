open import Level
open import Ordinals
module PFOD {n : Level } (O : Ordinals {n})   where

import filter 
open import logic
-- open import partfunc {n} O
import OD 

open import Relation.Nullary 
open import Relation.Binary 
open import Data.Empty 
open import Relation.Binary
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality
open import Data.Nat renaming ( zero to Zero ; suc to Suc ;  ℕ to Nat ; _⊔_ to _n⊔_ ) 
import BAlgebra 

open BAlgebra O

open inOrdinal O
open OD O
open OD.OD
open ODAxiom odAxiom
-- open ODAxiom-ho< odAxiom-ho<
import OrdUtil
import ODUtil
open Ordinals.Ordinals  O
open Ordinals.IsOrdinals isOrdinal
-- open Ordinals.IsNext isNext
open OrdUtil O
open ODUtil O


import ODC

open filter O

open _∧_
open _∨_
open Bool


open HOD

-------
--    the set of finite partial functions from ω to 2
--
--

open import Data.List hiding (filter)
open import Data.Maybe 

open import ZProduct O

data Hω2 :  (i : Nat) ( x : Ordinal  ) → Set n where
  hφ :  Hω2 0 o∅
  h0 : {i : Nat} {x : Ordinal  } → Hω2 i x  →
    Hω2 (Suc i) (& (Union ((nat→ω i , nat→ω i) ,  * x )))
  he : {i : Nat} {x : Ordinal  } → Hω2 i x  →
    Hω2 (Suc i) x

record  Hω2r (x : Ordinal) : Set n where
  field
    count : Nat
    hω2 : Hω2 count x

open Hω2r

hw⊆POmega :  {y : Ordinal} → Hω2r y → odef (Power Omega) y
hw⊆POmega {y} r = odmax1 (Hω2r.count r) (Hω2r.hω2 r) where
    odmax1 : {y : Ordinal} (i : Nat)  →  Hω2 i y → odef (Power Omega) y
    odmax1 0 hφ z xz = ⊥-elim ( ¬x<0 (subst (λ k → odef k z) o∅≡od∅  xz ))
    odmax1 (Suc i) (h0 {_} {y} hw) = pf01 where
        pf00 : odef ( Power Omega) y
        pf00 = odmax1 i hw
        pf01 : odef (Power Omega) (& (Union ((nat→ω i , nat→ω i ) , * y)))
        pf01 z xz with subst (λ k → odef k z ) *iso xz
        ... | record { owner = owner ; ao = case1 refl ; ox = ox } = pf02 where
             pf02 : Omega-d z
             pf02 with subst (λ k → odef k z) *iso ox
             ... | case1 refl = ω∋nat→ω {i}
             ... | case2 refl = ω∋nat→ω {i}
        ... | record { owner = owner ; ao = case2 refl ; ox = ox } = pf00 _ (subst (λ k → odef k z) *iso ox)
    odmax1 (Suc i) (he {_} {y} hw) = pf00 where
        pf00 : odef ( Power Omega) y
        pf00 = odmax1 i hw

--
-- Set of limited partial function of Omega
--
HODω2 :  HOD
HODω2 = record { od = record { def = λ x → Hω2r x } ; odmax = & (Power Omega)
  ; <odmax = λ lt → odef< (hw⊆POmega  lt) } 

HODω2⊆Omega : {x : HOD} → HODω2 ∋ x → x ⊆ Omega 
HODω2⊆Omega {x} hx {z} wz = hw⊆POmega hx _ (subst (λ k → odef k z) (sym *iso) wz)

record HwStep : Set n where
   field 
     x : Ordinal
     i : Nat
     isHw : Hω2 i x

3→Hω2 : List Two → HOD
3→Hω2 t = * (HwStep.x (list→hod t))  where
   list→hod : List Two → HwStep
   list→hod []  = record { x = o∅ ; i = 0 ; isHw = hφ }
   list→hod (i0 ∷ t)  = record { x = & (Union ( (nat→ω (HwStep.i pf01) , nat→ω (HwStep.i pf01))  , * x )) 
            ; i = Suc (HwStep.i pf01) ; isHw = h0 (HwStep.isHw pf01) } where 
        pf01 : HwStep
        pf01 = list→hod t 
        x = HwStep.x pf01
   list→hod (i1 ∷ t)  = list→hod t 

Hω2→3 : (x :  HOD) → HODω2 ∋ x → List Two 
Hω2→3 x = lemma where
   lemma : { y : Ordinal } →  Hω2r y → List Two
   lemma record { count = 0 ; hω2 = hφ } = []
   lemma record { count = (Suc i) ; hω2 = (h0 hω3) } = i0 ∷ lemma record { count = i ; hω2 =  hω3 }
   lemma record { count = (Suc i) ; hω2 = (he hω3) } = i1 ∷ lemma record { count = i ; hω2 =  hω3 }

ω→2 : HOD
ω→2 = Power Omega

ω2→f : (x : HOD) → ω→2 ∋ x → Nat → Two
ω2→f x lt n with ODC.∋-p O x (nat→ω n)
ω2→f x lt n | yes p = i1
ω2→f x lt n | no ¬p = i0

fω→2-sel : ( f : Nat → Two ) (x : HOD) → Set n
fω→2-sel f x = (Omega ∋ x) ∧ ( (lt : odef Omega (&  x) ) → f (ω→nat x lt) ≡ i1 )

fω→2 : (Nat → Two) → HOD
fω→2 f = Select Omega (fω→2-sel f)

open _==_

import Axiom.Extensionality.Propositional
postulate f-extensionality : { n m : Level}  → Axiom.Extensionality.Propositional.Extensionality n m

ω2∋f : (f : Nat → Two) → ω→2 ∋ fω→2 f
ω2∋f f = power← Omega (fω→2 f) (λ {x} lt →  proj1 ((proj2 (selection {fω→2-sel f} {Omega} )) lt))

ω→2f≡i1 : (X i : HOD) → (iω : Omega ∋ i) → (lt : ω→2 ∋ X ) → ω2→f X lt (ω→nat i iω)  ≡ i1 → X ∋ i
ω→2f≡i1 X i iω lt eq with ODC.∋-p O X (nat→ω (ω→nat i iω))
ω→2f≡i1 X i iω lt eq | yes p = subst (λ k → X ∋ k ) (nat→ω-iso iω) p

ω2→f-iso : (X : HOD) → ( lt : ω→2 ∋ X ) → fω→2 ( ω2→f X lt )  =h= X
eq→ (ω2→f-iso X lt) {x} ⟪ ωx , ⟪ ωx1 , iso ⟫ ⟫ = le00 where
    le00 : odef X x
    le00 = subst (λ k → odef X k) &iso ( ω→2f≡i1 _ _ ωx1 lt  (iso ωx1)  )
eq← (ω2→f-iso X lt) {x} Xx = ⟪ subst (λ k → odef Omega k) &iso le02  , ⟪ le02 , le01 ⟫ ⟫ where
    le02 : Omega ∋ * x
    le02 = power→ Omega _ lt (subst (λ k → odef X k) (sym &iso) Xx) 
    le01 : (wx : odef Omega (& (* x))) → ω2→f X lt (ω→nat (* x) wx) ≡ i1
    le01 wx   with ODC.∋-p O X (nat→ω (ω→nat _ wx) )
    ... | yes p  = refl
    ... | no ¬p  = ⊥-elim ( ¬p (subst (λ k → odef X k ) le03 Xx )) where
        le03 :  x ≡ & (nat→ω (ω→nato wx))
        le03 = subst₂ (λ j k → j ≡ k ) &iso refl (cong (&) (sym ( nat→ω-iso wx ) ) )

fω→2-iso : (f : Nat → Two) → ω2→f ( fω→2 f ) (ω2∋f f) ≡ f
fω→2-iso f = f-extensionality (λ x → le01 x ) where
    le01 : (x : Nat) → ω2→f (fω→2 f) (ω2∋f f) x ≡ f x
    le01 x with  ODC.∋-p O (fω→2 f) (nat→ω x) 
    le01 x | yes p = subst (λ k → i1 ≡ f k ) (ω→nat-iso0 x (proj1 (proj2 p)) (trans *iso *iso)) (sym ((proj2 (proj2 p)) le02)) where
        le02 :  Omega-d (& (* (& (nat→ω x))))
        le02 = proj1 (proj2 p )
    le01 x | no ¬p = sym ( ¬i1→i0 le04 ) where
        le04 : ¬ f x ≡ i1
        le04 fx=1 = ¬p ⟪ ω∋nat→ω {x} , ⟪ subst (λ k → Omega-d k) (sym &iso) (ω∋nat→ω {x})  , le05 ⟫ ⟫ where
            le05 : (lt : Omega-d (& (* (& (nat→ω x))))) → f (ω→nato lt) ≡ i1
            le05 lt = trans (cong f (ω→nat-iso0 x lt (trans *iso *iso))) fx=1

