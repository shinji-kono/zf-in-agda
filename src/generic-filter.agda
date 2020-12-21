open import Level
open import Ordinals
module generic-filter {n : Level } (O : Ordinals {n})   where

import filter 
open import zf
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
import BAlgbra 

open BAlgbra O

open inOrdinal O
open OD O
open OD.OD
open ODAxiom odAxiom
import OrdUtil
import ODUtil
open Ordinals.Ordinals  O
open Ordinals.IsOrdinals isOrdinal
open Ordinals.IsNext isNext
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

import OPair
open OPair O

ODSuc : (y : HOD) → infinite ∋ y → HOD
ODSuc y lt = Union (y , (y , y)) 

data Hω2 :  (i : Nat) ( x : Ordinal  ) → Set n where
  hφ :  Hω2 0 o∅
  h0 : {i : Nat} {x : Ordinal  } → Hω2 i x  →
    Hω2 (Suc i) (& (Union ((< nat→ω i , nat→ω 0 >) ,  * x )))
  h1 : {i : Nat} {x : Ordinal  } → Hω2 i x  →
    Hω2 (Suc i) (& (Union ((< nat→ω i , nat→ω 1 >) ,  * x )))
  he : {i : Nat} {x : Ordinal  } → Hω2 i x  →
    Hω2 (Suc i) x

record  Hω2r (x : Ordinal) : Set n where
  field
    count : Nat
    hω2 : Hω2 count x

open Hω2r

HODω2 :  HOD
HODω2 = record { od = record { def = λ x → Hω2r x } ; odmax = next o∅ ; <odmax = odmax0 } where
    P  : (i j : Nat) (x : Ordinal ) → HOD
    P  i j x = ((nat→ω i , nat→ω i) , (nat→ω i , nat→ω j)) , * x
    nat1 : (i : Nat) (x : Ordinal) → & (nat→ω i) o< next x
    nat1 i x =  next< nexto∅ ( <odmax infinite (ω∋nat→ω {i}))
    lemma1 : (i j : Nat) (x : Ordinal ) → osuc (& (P i j x)) o< next x
    lemma1 i j x = osuc<nx (pair-<xy (pair-<xy (pair-<xy (nat1 i x) (nat1 i x) ) (pair-<xy (nat1 i x) (nat1 j x) ) )
         (subst (λ k → k o< next x) (sym &iso) x<nx ))
    lemma : (i j : Nat) (x : Ordinal ) → & (Union (P i j x)) o< next x
    lemma i j x = next< (lemma1 i j x ) ho<
    odmax0 :  {y : Ordinal} → Hω2r y → y o< next o∅ 
    odmax0 {y} r with hω2 r
    ... | hφ = x<nx
    ... | h0 {i} {x} t = next< (odmax0 record { count = i ; hω2 = t }) (lemma i 0 x)
    ... | h1 {i} {x} t = next< (odmax0 record { count = i ; hω2 = t }) (lemma i 1 x)
    ... | he {i} {x} t = next< (odmax0 record { count = i ; hω2 = t }) x<nx

3→Hω2 : List (Maybe Two) → HOD
3→Hω2 t = list→hod t 0 where
   list→hod : List (Maybe Two) → Nat → HOD
   list→hod [] _ = od∅
   list→hod (just i0 ∷ t) i = Union (< nat→ω i , nat→ω 0 > , ( list→hod t (Suc i) )) 
   list→hod (just i1 ∷ t) i = Union (< nat→ω i , nat→ω 1 > , ( list→hod t (Suc i) )) 
   list→hod (nothing ∷ t) i = list→hod t (Suc i ) 

Hω2→3 : (x :  HOD) → HODω2 ∋ x → List (Maybe Two) 
Hω2→3 x = lemma where
   lemma : { y : Ordinal } →  Hω2r y → List (Maybe Two)
   lemma record { count = 0 ; hω2 = hφ } = []
   lemma record { count = (Suc i) ; hω2 = (h0 hω3) } = just i0 ∷ lemma record { count = i ; hω2 =  hω3 }
   lemma record { count = (Suc i) ; hω2 = (h1 hω3) } = just i1 ∷ lemma record { count = i ; hω2 =  hω3 }
   lemma record { count = (Suc i) ; hω2 = (he hω3) } = nothing ∷ lemma record { count = i ; hω2 =  hω3 }

ω→2 : HOD
ω→2 = Power infinite

ω→2f : (x : HOD) → ω→2 ∋ x → Nat → Two
ω→2f x lt n with ODC.∋-p O x (nat→ω n)
ω→2f x lt n | yes p = i1
ω→2f x lt n | no ¬p = i0

fω→2-sel : ( f : Nat → Two ) (x : HOD) → Set n
fω→2-sel f x = (infinite ∋ x) ∧ ( (lt : odef infinite (&  x) ) → f (ω→nat x lt) ≡ i1 )

fω→2 : (Nat → Two) → HOD
fω→2 f = Select infinite (fω→2-sel f)

open _==_

import Axiom.Extensionality.Propositional
postulate f-extensionality : { n m : Level}  → Axiom.Extensionality.Propositional.Extensionality n m

ω2∋f : (f : Nat → Two) → ω→2 ∋ fω→2 f
ω2∋f f = power← infinite (fω→2 f) (λ {x} lt →  proj1 ((proj2 (selection {fω→2-sel f} {infinite} )) lt))

ω→2f≡i1 : (X i : HOD) → (iω : infinite ∋ i) → (lt : ω→2 ∋ X ) → ω→2f X lt (ω→nat i iω)  ≡ i1 → X ∋ i
ω→2f≡i1 X i iω lt eq with ODC.∋-p O X (nat→ω (ω→nat i iω))
ω→2f≡i1 X i iω lt eq | yes p = subst (λ k → X ∋ k ) (nat→ω-iso iω) p

open _⊆_

-- someday ...
-- postulate 
--    ω→2f-iso : (X : HOD) → ( lt : ω→2 ∋ X ) → fω→2 ( ω→2f X lt )  =h= X
--    fω→2-iso : (f : Nat → Two) → ω→2f ( fω→2 f ) (ω2∋f f) ≡ f

record CountableOrdinal : Set (suc (suc n)) where
   field
       ctl→ : Nat → Ordinal
       ctl← : Ordinal → Nat
       ctl-iso→ : { x : Ordinal } → ctl→ (ctl← x ) ≡ x 
       ctl-iso← : { x : Nat }  → ctl← (ctl→ x ) ≡ x

record CountableHOD : Set (suc (suc n)) where
   field
       mhod : HOD
       mtl→ : Nat → Ordinal
       mtl→∈P : (i : Nat) → odef mhod (mtl→ i)
       mtl← : (x : Ordinal) → odef mhod x → Nat
       mtl-iso→ : { x : Ordinal } → (lt : odef mhod x ) → mtl→ (mtl← x lt ) ≡ x 
       mtl-iso← : { x : Nat }  → mtl← (mtl→ x ) (mtl→∈P x) ≡ x
   
       
open CountableOrdinal 
open CountableHOD

----
--   a(n) ∈ M
--   ∃ q ∈ Power P → q ∈ a(n) ∧ p(n) ⊆ q    
--
PGHOD :  (i : Nat) → (C : CountableOrdinal) → (P : HOD) → (p : Ordinal) → HOD
PGHOD i C P p = record { od = record { def = λ x  →
       odef (Power P) x ∧ odef (* (ctl→ C i)) x  ∧  ( (y : Ordinal ) → odef (* p) y →  odef (* x) y ) }
   ; odmax = odmax (Power P)  ; <odmax = λ {y} lt → <odmax (Power P) (proj1 lt) }  

---
--   p(n+1) = if PGHOD n qn otherwise p(n)
--
next-p :  (C : CountableOrdinal) (P : HOD ) (i : Nat) → (p : Ordinal) → Ordinal
next-p C P i p with is-o∅  ( & (PGHOD i C P p))  
next-p C P i p | yes y = p
next-p C P i p | no not = & (ODC.minimal O (PGHOD i C P p ) (λ eq → not (=od∅→≡o∅ eq)))  -- axiom of choice

---
--  ascendant search on p(n)
--
find-p :  (C : CountableOrdinal) (P : HOD ) (i : Nat) → (x : Ordinal) → Ordinal
find-p C P Zero x = x
find-p C P (Suc i) x = find-p C P i ( next-p C P i x )

---
-- G = { r ∈ Power P | ∃ n → r ⊆ p(n) }
--
record PDN  (C : CountableOrdinal) (P : HOD ) (x : Ordinal) : Set n where
   field
       gr : Nat
       pn<gr : (y : Ordinal) → odef (* x) y → odef (* (find-p C P gr o∅)) y
       x∈PP  : odef (Power P) x

open PDN

---
-- G as a HOD
--
PDHOD :  (C : CountableOrdinal) → (P : HOD ) → HOD
PDHOD C P = record { od = record { def = λ x →  PDN C P x }
    ; odmax = odmax (Power P) ; <odmax = λ {y} lt → <odmax (Power P) {y} (PDN.x∈PP lt)  } 

open PDN

----
--  Generic Filter on Power P for HOD's Countable Ordinal (G ⊆ Power P ≡ G i.e. Nat → P → Set )
--
--  p 0 ≡ ∅
--  p (suc n) = if ∃ q ∈ * ( ctl→ n ) ∧ p n ⊆ q → q  (axiom of choice)
---             else p n

P∅ : {P : HOD} → odef (Power P) o∅
P∅ {P} =  subst (λ k → odef (Power P) k ) ord-od∅ (lemma o∅  o∅≡od∅) where
    lemma : (x : Ordinal ) → * x ≡ od∅ → odef (Power P) (& od∅)
    lemma x eq = power← P od∅  (λ {x} lt → ⊥-elim (¬x<0 lt ))
x<y→∋ : {x y : Ordinal} → odef (* x) y → * x ∋ * y
x<y→∋ {x} {y} lt = subst (λ k → odef (* x) k ) (sym &iso) lt

P-GenericFilter : (C : CountableOrdinal) → (P : HOD ) → GenericFilter P
P-GenericFilter C P = record {
      genf = record { filter = PDHOD C P ; f⊆PL =  f⊆PL ; filter1 = {!!} ; filter2 = {!!} }
    ; generic = λ D → {!!}
   } where
        find-p-⊆P : (C : CountableOrdinal) (P : HOD ) (i : Nat) → (x y : Ordinal)  → odef (Power P) x → odef (* (find-p C P i x)) y → odef P y 
        find-p-⊆P C P Zero x y Px Py = subst (λ k → odef P k ) &iso
            ( incl (ODC.power→⊆ O P (* x) (d→∋ (Power P)  Px)) (x<y→∋ Py))
        find-p-⊆P C P (Suc i) x y Px Py = find-p-⊆P C P i (next-p C P i x)  y {!!} {!!}
        f⊆PL :  PDHOD C P ⊆ Power P
        f⊆PL = record { incl = λ {x} lt → power← P x (λ {y} y<x →
             find-p-⊆P C P (gr lt) o∅ (& y) P∅ (pn<gr lt (& y) (subst (λ k → odef k (& y)) (sym *iso) y<x))) }


open GenericFilter
open Filter

record Incompatible  (P : HOD ) : Set (suc (suc n)) where
   field
      except : HOD → ( HOD ∧ HOD )
      incompatible : { p : HOD } →  Power P ∋ p  →  Power P ∋ proj1 (except p )  →  Power P ∋ proj2 (except p ) 
          → ( p ⊆ proj1 (except p)  ) ∧ ( p ⊆ proj2 (except p)  )
          → ∀ ( r : HOD ) →  Power P ∋ r → ¬ (( proj1 (except p)  ⊆ r ) ∧ ( proj2 (except p)  ⊆ r ))

lemma725 : (M : CountableHOD ) (C : CountableOrdinal) (P : HOD ) →  mhod M ∋ Power P
    →  Incompatible P → ¬ ( mhod M ∋ filter ( genf ( P-GenericFilter C P )))
lemma725 = {!!}

lemma725-1 :   Incompatible HODω2
lemma725-1 = {!!}

lemma726 :  (C : CountableOrdinal) (P : HOD ) 
    →  Union ( filter ( genf ( P-GenericFilter C HODω2 ))) =h= ω→2
lemma726 = {!!}

--
--   val x G = { val y G | ∃ p → G ∋ p → x ∋ < y , p > }
--
--   W (ω , H ( ω , 2 )) = { p ∈ ( Nat → H (ω , 2) ) |  { i ∈ Nat → p i ≠ i1 } is finite }
--



