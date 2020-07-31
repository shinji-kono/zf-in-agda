open import Level
open import Ordinals
module generic-filter {n : Level } (O : Ordinals {n})   where

import filter 
open import zf
open import logic
open import partfunc {n} O
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

open PFunc

_f∩_ : (f g : PFunc (Lift n Nat) (Lift n Two) ) →  PFunc (Lift n Nat) (Lift n Two)
f f∩ g = record { dom = λ x → (dom f x ) ∧ (dom g x ) ∧ ((fr : dom f x ) → (gr : dom g x ) → pmap f x fr ≡ pmap g x gr)
              ; pmap = λ x p →  pmap f x (proj1  p) ; meq = meq f }

_↑_ :  (Nat → Two) → Nat →  PFunc (Lift n Nat) (Lift n Two)
_↑_  f i = record { dom = λ x → Lift n (lower x ≤ i) ; pmap = λ x _ → lift (f (lower x)) ; meq = λ {x} {p} {q} → refl }

record _f⊆_ (f g : PFunc (Lift n Nat) (Lift n Two)  ) : Set (suc n) where
  field
     extend : {x : Nat} → (fr : dom f (lift x) ) →  dom g (lift x  )
     feq : {x : Nat} → {fr : dom f (lift x) } →  pmap f (lift x) fr ≡ pmap g (lift x) (extend fr)

open _f⊆_ 
open import Data.Nat.Properties

ODSuc : (y : HOD) → infinite ∋ y → HOD
ODSuc y lt = Union (y , (y , y)) 

data Hω2 :  (i : Nat) ( x : Ordinal  ) → Set n where
  hφ :  Hω2 0 o∅
  h0 : {i : Nat} {x : Ordinal  } → Hω2 i x  →
    Hω2 (Suc i) (od→ord (Union ((< nat→ω i , nat→ω 0 >) ,  ord→od x )))
  h1 : {i : Nat} {x : Ordinal  } → Hω2 i x  →
    Hω2 (Suc i) (od→ord (Union ((< nat→ω i , nat→ω 1 >) ,  ord→od x )))
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
    P  i j x = ((nat→ω i , nat→ω i) , (nat→ω i , nat→ω j)) , ord→od x
    nat1 : (i : Nat) (x : Ordinal) → od→ord (nat→ω i) o< next x
    nat1 i x =  next< nexto∅ ( <odmax infinite (ω∋nat→ω {i}))
    lemma1 : (i j : Nat) (x : Ordinal ) → osuc (od→ord (P i j x)) o< next x
    lemma1 i j x = osuc<nx (pair-<xy (pair-<xy (pair-<xy (nat1 i x) (nat1 i x) ) (pair-<xy (nat1 i x) (nat1 j x) ) )
         (subst (λ k → k o< next x) (sym diso) x<nx ))
    lemma : (i j : Nat) (x : Ordinal ) → od→ord (Union (P i j x)) o< next x
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
fω→2-sel f x = (infinite ∋ x) ∧ ( (lt : odef infinite (od→ord  x) ) → f (ω→nat x lt) ≡ i1 )

fω→2 : (Nat → Two) → HOD
fω→2 f = Select infinite (fω→2-sel f)

open _==_

postulate f-extensionality : { n m : Level}  → Relation.Binary.PropositionalEquality.Extensionality n m

ω2∋f : (f : Nat → Two) → ω→2 ∋ fω→2 f
ω2∋f f = power← infinite (fω→2 f) (λ {x} lt →  proj1 ((proj2 (selection {fω→2-sel f} {infinite} )) lt))

ω→2f≡i1 : (X i : HOD) → (iω : infinite ∋ i) → (lt : ω→2 ∋ X ) → ω→2f X lt (ω→nat i iω)  ≡ i1 → X ∋ i
ω→2f≡i1 X i iω lt eq with ODC.∋-p O X (nat→ω (ω→nat i iω))
ω→2f≡i1 X i iω lt eq | yes p = subst (λ k → X ∋ k ) (nat→ω-iso iω) p

open _⊆_

-- someday ...
postulate 
   ω→2f-iso : (X : HOD) → ( lt : ω→2 ∋ X ) → fω→2 ( ω→2f X lt )  =h= X
   fω→2-iso : (f : Nat → Two) → ω→2f ( fω→2 f ) (ω2∋f f) ≡ f

↑n : (f n : HOD) → ((ω→2 ∋ f ) ∧ (infinite ∋ n)) → HOD
↑n f n lt = 3→Hω2 ( ω→2f f (proj1 lt) 3↑ (ω→nat n (proj2 lt) ))

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
       odef P x ∧ odef (ord→od (ctl→ C i)) x  ∧  ( (y : Ordinal ) → odef (ord→od p) y →  odef (ord→od x) y ) }
   ; odmax = odmax P  ; <odmax = λ {y} lt → <odmax P (proj1 lt) }  

---
--   p(n+1) = if PGHOD n qn otherwise p(n)
--
next-p :  (C : CountableOrdinal) (P : HOD ) (i : Nat) → (p : Ordinal) → Ordinal
next-p C P i p with ODC.decp O ( PGHOD i C P p =h= od∅ )
next-p C P i p | yes y = p
next-p C P i p | no not = od→ord (ODC.minimal O (PGHOD i C P p ) not)

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
       pn<gr : (y : Ordinal) → odef (ord→od x) y → odef (ord→od (find-p C P gr o∅)) y
       px∈ω  : odef (Power P) x

open PDN

---
-- G as a HOD
--
PDHOD :  (C : CountableOrdinal) → (P : HOD ) → HOD
PDHOD C P = record { od = record { def = λ x →  PDN C P x }
    ; odmax = odmax (Power P) ; <odmax = λ {y} lt → <odmax (Power P) {y} (PDN.px∈ω lt)  } where

open PDN

----
--  Generic Filter on Power P for HOD's Countable Ordinal (G ⊆ Power P ≡ G i.e. Nat → P → Set )
--
--  p 0 ≡ ∅
--  p (suc n) = if ∃ q ∈ ord→od ( ctl→ n ) ∧ p n ⊆ q → q  (axiom of choice)
---             else p n

P-GenericFilter : (C : CountableOrdinal) → (P : HOD ) → GenericFilter P
P-GenericFilter C P = record {
      genf = record { filter = PDHOD C P ; f⊆PL =  f⊆PL ; filter1 = {!!} ; filter2 = {!!} }
    ; generic = λ D → {!!}
   } where
        P∅ : {P : HOD} → odef (Power P) o∅
        P∅ {P} =  subst (λ k → odef (Power P) k ) ord-od∅ (lemma o∅  o∅≡od∅) where
            lemma : (x : Ordinal ) → ord→od x ≡ od∅ → odef (Power P) (od→ord od∅)
            lemma x eq = power← P od∅  (λ {x} lt → ⊥-elim (¬x<0 lt ))
        x<y→∋ : {x y : Ordinal} → odef (ord→od x) y → ord→od x ∋ ord→od y
        x<y→∋ {x} {y} lt = subst (λ k → odef (ord→od x) k ) (sym diso) lt
        find-p-⊆P : (C : CountableOrdinal) (P : HOD ) (i : Nat) → (x y : Ordinal)  → odef (Power P) x → odef (ord→od (find-p C P i x)) y → odef P y 
        find-p-⊆P C P Zero x y Px Py = subst (λ k → odef P k ) diso
            ( incl (ODC.power→⊆ O P (ord→od x) (d→∋ (Power P)  Px)) (x<y→∋ Py))
        find-p-⊆P C P (Suc i) x y Px Py = find-p-⊆P C P i (next-p C P i x)  y {!!} {!!}
        f⊆PL :  PDHOD C P ⊆ Power P
        f⊆PL = record { incl = λ {x} lt → power← P x (λ {y} y<x →
             find-p-⊆P C P (gr lt) o∅ (od→ord y) P∅ (pn<gr lt (od→ord y) (subst (λ k → odef k (od→ord y)) (sym oiso) y<x))) }


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




