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

record CountableModel (P : HOD) : Set (suc (suc n)) where
   field
       ctl-M : Ordinal
       ctl→ : Nat → Ordinal
       ctl← : (x : Ordinal )→  x o< ctl-M → Nat
       ctl<M : (x : Nat) → ctl→ x o< ctl-M
       ctl-iso→ : { x : Ordinal } → (lt : x o< ctl-M)  → ctl→ (ctl← x lt ) ≡ x 
       ctl-iso← : { x : Nat }  →  ctl← (ctl→ x ) (ctl<M x)  ≡ x
       ctl-P∈M : Power P ∈ * ctl-M
--
-- almmost universe
-- find-p contains ∃ x : Ordinal → x o< & M → ∀ r ∈ M → ∈ Ord x
-- 


-- we expect  P ∈ * ctl-M ∧ G  ⊆ Power P  , ¬ G ∈ * ctl-M, 

open CountableModel 

----
--   a(n) ∈ M
--   ∃ q ∈ Power P → q ∈ a(n) ∧ p(n) ⊆ q    
--
PGHOD :  (i : Nat) (P : HOD) (C : CountableModel P) → (p : Ordinal) → HOD
PGHOD i P C p = record { od = record { def = λ x  →
       odef (Power P) x ∧ odef (* (ctl→ C i)) x  ∧  ( (y : Ordinal ) → odef (* p) y →  odef (* x) y ) }
   ; odmax = odmax (Power P)  ; <odmax = λ {y} lt → <odmax (Power P) (proj1 lt) }  

---
--   p(n+1) = if (f n) != ∅ then (f n) otherwise p(n)
--  
find-p :  (P : HOD ) (C : CountableModel P)  (i : Nat) → (x : Ordinal) → Ordinal
find-p P C Zero x = x
find-p P C (Suc i) x with is-o∅ ( & ( PGHOD i P C (find-p P C i x)) )
... | yes y  = find-p P C i x
... | no not  = & (ODC.minimal O ( PGHOD i P C (find-p P C i x)) (λ eq → not (=od∅→≡o∅ eq)))  -- axiom of choice

---
-- G = { r ∈ Power P | ∃ n → p(n) ⊆ r }
--
record PDN  (P p : HOD ) (C : CountableModel P)  (x : Ordinal) : Set n where
   field
       gr : Nat
       pn<gr : (y : Ordinal) → odef (* (find-p P C gr (& p))) y → odef (* x) y 
       x∈PP  : odef (Power P) x

open PDN

---
-- G as a HOD
--
PDHOD :  (P p : HOD ) (C : CountableModel P ) → HOD
PDHOD P p C  = record { od = record { def = λ x →  PDN P p C x }
    ; odmax = odmax (Power P) ; <odmax = λ {y} lt → <odmax (Power P) {y} (PDN.x∈PP lt)  } 

open PDN

----
--  Generic Filter on Power P for HOD's Countable Ordinal (G ⊆ Power P ≡ G i.e. Nat → P → Set )
--
--  p 0 ≡ ∅
--  p (suc n) = if ∃ q ∈ M ∧ p n ⊆ q → q  (by axiom of choice) ( q =  * ( ctl→ n ) )
---             else p n

P∅ : {P : HOD} → odef (Power P) o∅
P∅ {P} =  subst (λ k → odef (Power P) k ) ord-od∅ (lemma o∅  o∅≡od∅) where
    lemma : (x : Ordinal ) → * x ≡ od∅ → odef (Power P) (& od∅)
    lemma x eq = power← P od∅  (λ {x} lt → ⊥-elim (¬x<0 lt ))
x<y→∋ : {x y : Ordinal} → odef (* x) y → * x ∋ * y
x<y→∋ {x} {y} lt = subst (λ k → odef (* x) k ) (sym &iso) lt

open import Data.Nat.Properties
open import nat
open _⊆_

p-monotonic1 :  (P p : HOD ) (C : CountableModel P ) → {n : Nat} → (* (find-p P C n (& p))) ⊆ (* (find-p P C (Suc n) (& p)))
p-monotonic1 P p C {n} with is-o∅ (& (PGHOD n P C (find-p P C n (& p))))
... | yes y =   refl-⊆
... | no not = record { incl = λ {x} lt → proj2 (proj2 fmin∈PGHOD) (& x) lt  } where
    fmin : HOD
    fmin = ODC.minimal O (PGHOD n P C (find-p P C n (& p))) (λ eq → not (=od∅→≡o∅ eq))
    fmin∈PGHOD : PGHOD n P C (find-p P C n (& p)) ∋ fmin
    fmin∈PGHOD = ODC.x∋minimal O (PGHOD n P C (find-p P C n (& p))) (λ eq → not (=od∅→≡o∅ eq))

p-monotonic :  (P p : HOD ) (C : CountableModel P ) → {n m : Nat} → n ≤ m → (* (find-p P C n (& p))) ⊆ (* (find-p P C m (& p)))
p-monotonic P p C {Zero} {Zero} n≤m = refl-⊆
p-monotonic P p C {Zero} {Suc m} z≤n = trans-⊆ (p-monotonic P p C {Zero} {m} z≤n ) (p-monotonic1 P p C {m} )  
p-monotonic P p C {Suc n} {Suc m} (s≤s n≤m) with <-cmp n m
... | tri< a ¬b ¬c = trans-⊆ (p-monotonic P p C {Suc n} {m} a) (p-monotonic1 P p C {m} )  
... | tri≈ ¬a refl ¬c = refl-⊆
... | tri> ¬a ¬b c = ⊥-elim ( nat-≤> n≤m c )

P-GenericFilter : (P p0 : HOD ) → Power P ∋ p0 → (C : CountableModel P) → GenericFilter P
P-GenericFilter P p0 Pp0 C = record {
      genf = record { filter = PDHOD P p0 C ; f⊆PL =  f⊆PL ; filter1 = f1 ; filter2 = f2 }
    ; generic = fdense
   } where
        PGHOD∈PL :  (i : Nat) → (x : Ordinal) →  PGHOD i P C x ⊆ Power P
        PGHOD∈PL i x = record { incl = λ {x} p → proj1 p }
        f⊆PL :  PDHOD P p0 C ⊆ Power P
        f⊆PL = record { incl = λ {x} lt →  x∈PP lt  }
        f1 : {p q : HOD} → q ⊆ P → PDHOD P p0 C ∋ p → p ⊆ q → PDHOD P p0 C ∋ q
        f1 {p} {q}  q⊆P PD∋p p⊆q =  record { gr = gr PD∋p ;  pn<gr = f04 ; x∈PP = power←  _ _ (incl q⊆P) } where
           f04 : (y : Ordinal) → odef (* (find-p P C (gr PD∋p) (& p0))) y → odef (* (& q)) y
           f04 y lt1 = subst₂ (λ j k → odef j k ) (sym *iso) &iso (incl p⊆q (subst₂ (λ j k → odef k j ) (sym &iso) *iso ( pn<gr PD∋p y  lt1 )))
               -- odef (* (find-p P C (gr PD∋p) (& p0))) y → odef (* (& q)) y
        f2 : {p q : HOD} → PDHOD P p0 C ∋ p → PDHOD P p0 C ∋ q → PDHOD P p0 C ∋ (p ∩ q)
        f2 {p} {q} PD∋p PD∋q with <-cmp (gr PD∋p) (gr PD∋q)
        ... | tri< a ¬b ¬c = record { gr = gr PD∋p ;  pn<gr = λ y lt → subst (λ k → odef k y ) (sym *iso) (f3 y lt); x∈PP = ODC.power-∩ O (x∈PP PD∋p) (x∈PP PD∋q)   }  where
            f3 : (y : Ordinal) → odef (* (find-p P C (gr PD∋p) (& p0))) y → odef (p ∩ q) y
            f3 y lt = ⟪ subst (λ k → odef k y) *iso (pn<gr PD∋p y lt) , subst (λ k → odef k y) *iso (pn<gr PD∋q y (f5 lt)) ⟫ where
               f5 : odef (* (find-p P C (gr PD∋p) (& p0))) y → odef (* (find-p P C (gr PD∋q) (& p0))) y
               f5 lt = subst (λ k → odef (* (find-p P C (gr PD∋q) (& p0))) k ) &iso ( incl (p-monotonic P p0 C {gr PD∋p} {gr PD∋q} (<to≤ a))
                   (subst (λ k → odef (* (find-p P C (gr PD∋p) (& p0))) k ) (sym &iso) lt) )
        ... | tri≈ ¬a refl ¬c = record { gr = gr PD∋p ;  pn<gr =  λ y lt → subst (λ k → odef k y ) (sym *iso) (f4 y lt);  x∈PP = ODC.power-∩ O (x∈PP PD∋p) (x∈PP PD∋q)   }  where
            f4 : (y : Ordinal) → odef (* (find-p P C (gr PD∋p) (& p0))) y → odef (p ∩ q) y
            f4 y lt = ⟪ subst (λ k → odef k y) *iso (pn<gr PD∋p y lt) , subst (λ k → odef k y) *iso (pn<gr PD∋q y lt) ⟫ 
        ... | tri> ¬a ¬b c = record { gr = gr PD∋q ;  pn<gr =  λ y lt → subst (λ k → odef k y ) (sym *iso) (f3 y lt) ; x∈PP = ODC.power-∩ O (x∈PP PD∋p) (x∈PP PD∋q)   } where
            f3 : (y : Ordinal) → odef (* (find-p P C (gr PD∋q) (& p0))) y → odef (p ∩ q) y
            f3 y lt = ⟪ subst (λ k → odef k y) *iso (pn<gr PD∋p y (f5 lt)) , subst (λ k → odef k y) *iso (pn<gr PD∋q y lt) ⟫ where
               f5 : odef (* (find-p P C (gr PD∋q) (& p0))) y → odef (* (find-p P C (gr PD∋p) (& p0))) y
               f5 lt = subst (λ k → odef (* (find-p P C (gr PD∋p) (& p0))) k ) &iso ( incl (p-monotonic P p0 C {gr PD∋q} {gr PD∋p} (<to≤ c))
                   (subst (λ k → odef (* (find-p P C (gr PD∋q) (& p0))) k ) (sym &iso) lt) )
        fdense : (D : Dense P ) → ¬ (filter.Dense.dense D ∩ PDHOD P p0 C) ≡ od∅
        fdense D eq0  = ⊥-elim (  ∅< {Dense.dense D ∩ PDHOD P p0 C} fd01 (≡od∅→=od∅ eq0 )) where
           open Dense
           fd : HOD
           fd = dense-f D p0
           PP∋D : dense D ⊆ Power P
           PP∋D = d⊆P D
           fd00 : PDHOD P p0 C ∋ p0
           fd00 = record { gr = 0 ; pn<gr = λ y lt → lt ; x∈PP = Pp0 }
           fd02 : dense D ∋ dense-f D p0 
           fd02 = dense-d D (ODC.power→⊆ O _ _ Pp0 )
           fd04 : dense-f D p0 ⊆ P
           fd04 = ODC.power→⊆ O _ _ ( incl PP∋D fd02 )
           fd03 : PDHOD P p0 C  ∋ dense-f D p0 
           fd03 = f1 {p0} {dense-f D p0} fd04 fd00 ( dense-p D (ODC.power→⊆ O _ _ Pp0 ) )
           fd01 : (dense D ∩ PDHOD P p0 C) ∋ fd
           fd01 = ⟪ fd02 , fd03 ⟫ 

open GenericFilter
open Filter

record Incompatible  (P : HOD ) : Set (suc (suc n)) where
   field
      q : {p : HOD } → Power P ∋ p → HOD 
      r : {p : HOD } → Power P ∋ p → HOD 
      incompatible : { p : HOD } →  (P∋p : Power P ∋ p)  →  Power P ∋ q P∋p  →  Power P ∋ r P∋p
          → ( p ⊆ q P∋p)   ∧ ( p ⊆ r P∋p)  
          → ∀ ( s : HOD ) →  Power P ∋ s → ¬ (( q P∋p  ⊆ s  ) ∧ ( r P∋p  ⊆ s ))

lemma725 : (P p : HOD ) (C : CountableModel P) 
    →  * (ctl-M C) ∋ Power P
    →  (pp0 : Power P ∋ p)
    →  Incompatible P → ¬ ( * (ctl-M C) ∋ filter ( genf ( P-GenericFilter P p pp0 C )))
lemma725 = {!!}

open import PFOD O

-- HODω2 : HOD
-- 
-- ω→2 : HOD
-- ω→2 = Power infinite

lemma725-1 :   Incompatible HODω2
lemma725-1 = {!!}

lemma726 :  (C : CountableModel HODω2) 
    →  Union ( Replace' (Power HODω2) (λ p lt → filter ( genf ( P-GenericFilter HODω2 p lt C )))) =h= ω→2 -- HODω2 ∋ p
lemma726 = {!!}

--
--   val x G = { val y G | ∃ p → G ∋ p → x ∋ < y , p > }
--

record valR (x : HOD) {P : HOD} (G : GenericFilter P) : Set (suc n) where
   field
     valx : HOD

record valS (ox oy oG : Ordinal) : Set n where
   field
     op : Ordinal
     p∈G : odef (* oG) op 
     is-val : odef (* ox) ( & < * oy , * op >  )

val : (x : HOD) {P : HOD }
    →  (G : GenericFilter P)
    →  HOD
val x G = TransFinite {λ x → HOD } ind (& x) where
  ind : (x : Ordinal) → ((y : Ordinal) → y o< x → HOD) → HOD
  ind x valy = record { od = record { def = λ y → valS x y (& (filter (genf G))) } ; odmax = {!!} ; <odmax = {!!} }


--
--   W (ω , H ( ω , 2 )) = { p ∈ ( Nat → H (ω , 2) ) |  { i ∈ Nat → p i ≠ i1 } is finite }
--



