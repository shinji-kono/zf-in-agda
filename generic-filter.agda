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

ω→2f≡i0 : (X i : HOD) → (iω : infinite ∋ i) → (lt : ω→2 ∋ X ) → ω→2f X lt (ω→nat i iω)  ≡ i1 → X ∋ i
ω→2f≡i0 X i iω lt eq with ODC.∋-p O X (nat→ω (ω→nat i iω))
ω→2f≡i0 X i iω lt eq | yes p = subst (λ k → X ∋ k ) (nat→ω-iso iω) p

ω→2f-iso : (X : HOD) → ( lt : ω→2 ∋ X ) → fω→2 ( ω→2f X lt )  =h= X
ω→2f-iso X lt = record {
     eq→ = eq1
   ; eq← = eq2
  } where
     eq1 : {x : Ordinal} → odef (fω→2 (ω→2f X lt)) x → odef X x
     eq1 {x} fx = {!!} where
         x-nat : odef infinite x
         x-nat =  subst (λ k → odef infinite k) diso ( ODC.double-neg-eilm O
             (power→ infinite _ (ω2∋f (ω→2f X lt)) (d→∋ (fω→2 (ω→2f X lt)) fx ))) 
         i : Nat
         i = ω→nat (ord→od x) (d→∋ infinite x-nat)
         is-i1 : ω→2f X lt i ≡ i1
         is-i1 = {!!}
     eq2 : {x : Ordinal} → odef X x → odef (fω→2 (ω→2f X lt)) x
     eq2 {x} Xx = {!!} where
         x-nat : odef infinite x
         x-nat = {!!}
  
fω→2-iso : (f : Nat → Two) → ω→2f ( fω→2 f ) (ω2∋f f) ≡ f
fω→2-iso f = f-extensionality (λ x → eq1 x ) where
     eq1 : (x : Nat) → ω→2f (fω→2 f) (ω2∋f f) x ≡ f x
     eq1 x = {!!}


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

PGHOD :  (i : Nat) → (C : CountableOrdinal) → (P : HOD) → (p : Ordinal) → HOD
PGHOD i C P p = record { od = record { def = λ x  → odef P x ∧ odef (ord→od (ctl→ C i)) x  ∧  ( (y : Ordinal ) → odef (ord→od p) y →  odef (ord→od x) y ) }
   ; odmax = odmax P  ; <odmax = λ {y} lt → <odmax P (proj1 lt) }  

next-p :  (C : CountableOrdinal) (P : HOD ) (i : Nat) → (p : Ordinal) → Ordinal
next-p C P i p with ODC.decp O ( PGHOD i C P p =h= od∅ )
next-p C P i p | yes y = p
next-p C P i p | no not = od→ord (ODC.minimal O (PGHOD i C P p ) not)

find-p :  (C : CountableOrdinal) (P : HOD ) (i : Nat) → (x : Ordinal) → Ordinal
find-p C P Zero x = x
find-p C P (Suc i) x = find-p C P i ( next-p C P i x )

record PDN  (C : CountableOrdinal) (P : HOD ) (x : Ordinal) : Set n where
   field
       gr : Nat
       pn<gr : (y : Ordinal) → odef (ord→od x) y → odef (ord→od (find-p C P gr o∅)) y
       px∈ω  : odef P x

open PDN

PDHOD :  (C : CountableOrdinal) → (P : HOD ) → HOD
PDHOD C P = record { od = record { def = λ x →  PDN C P x }
    ; odmax = odmax (Power P) ; <odmax = {!!}  } where

--
--  p 0 ≡ ∅
--  p (suc n) = if ∃ q ∈ ord→od ( ctl→ n ) ∧ p n ⊆ q → q 
---             else p n

P-GenericFilter : (C : CountableOrdinal) → (P : HOD ) → GenericFilter P
P-GenericFilter C P = record {
      genf = record { filter = PDHOD C P ; f⊆PL = {!!} ; filter1 = {!!} ; filter2 = {!!} }
    ; generic = λ D → {!!}
   }

open GenericFilter
open Filter

record Incompatible  (P : HOD ) : Set (suc (suc n)) where
   field
      except : HOD → ( HOD ∧ HOD )
      incompatible : { p : HOD } →  P ∋ p  →  P ∋ proj1 (except p )  →  P ∋ proj2 (except p ) 
          → ( p ⊆ proj1 (except p)  ) ∧ ( p ⊆ proj2 (except p)  )
          → ∀ ( r : HOD ) →  P ∋ r → ¬ (( proj1 (except p)  ⊆ r ) ∧ ( proj2 (except p)  ⊆ r ))

lemma725 : (M : CountableHOD ) (C : CountableOrdinal) (P : HOD ) →  mhod M ∋ P
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




