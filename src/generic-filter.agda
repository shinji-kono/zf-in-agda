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
import BAlgebra 

open BAlgebra O

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

record CountableModel : Set (suc (suc n)) where
   field
       ctl-M : HOD
       ctl→ : Nat → Ordinal
       ctl<M : (x : Nat) → odef (ctl-M) (ctl→ x) 
       ctl← : (x : Ordinal )→  odef (ctl-M ) x → Nat
       ctl-iso→ : { x : Ordinal } → (lt : odef (ctl-M) x )  → ctl→ (ctl← x lt ) ≡ x 
       -- we have no otherway round
       -- ctl-iso← : { x : Nat }  →  ctl← (ctl→ x ) (ctl<M x)  ≡ x
--
-- almmost universe
-- find-p contains ∃ x : Ordinal → x o< & M → ∀ r ∈ M → ∈ Ord x
-- 

-- we expect  P ∈ * ctl-M ∧ G  ⊆ L ⊆ Power P  , ¬ G ∈ * ctl-M, 

open CountableModel 

----
--   a(n) ∈ M
--   ∃ q ∈ L ⊆ Power P → q ∈ a(n) ∧ q ⊆ p(n)    
--
PGHOD :  (i : Nat) (L : HOD) (C : CountableModel ) → (p : Ordinal) → HOD
PGHOD i L C p = record { od = record { def = λ x  →
       odef L x ∧ odef (* (ctl→ C i)) x  ∧  ( (y : Ordinal ) → odef (* x) y →  odef (* p) y ) }
   ; odmax = odmax L  ; <odmax = λ {y} lt → <odmax L (proj1 lt) }  

---
--   p(n+1) = if ({q | q ∈ a(n) ∧ q ⊆ p(n))} != ∅ then q otherwise p(n)
--  
find-p :  (L : HOD ) (C : CountableModel )  (i : Nat) → (x : Ordinal) → Ordinal
find-p L C Zero x = x
find-p L C (Suc i) x with is-o∅ ( & ( PGHOD i L C (find-p L C i x)) )
... | yes y  = find-p L C i x
... | no not  = & (ODC.minimal O ( PGHOD i L C (find-p L C i x)) (λ eq → not (=od∅→≡o∅ eq)))  -- axiom of choice

---
-- G = { r ∈ L ⊆ Power P | ∃ n → p(n) ⊆ r }
--
record PDN  (L p : HOD ) (C : CountableModel )  (x : Ordinal) : Set n where
   field
       gr : Nat
       pn<gr : (y : Ordinal) → odef (* (find-p L C gr (& p))) y → odef (* x) y 
       x∈PP  : odef L x

open PDN

---
-- G as a HOD
--
PDHOD :  (L p : HOD ) (C : CountableModel  ) → HOD
PDHOD L p C  = record { od = record { def = λ x →  PDN L p C x }
    ; odmax = odmax L ; <odmax = λ {y} lt → <odmax L {y} (PDN.x∈PP lt)  } 

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

p-monotonic1 :  (L p : HOD ) (C : CountableModel  ) → {n : Nat} → (* (find-p L C (Suc n) (& p))) ⊆ (* (find-p L C n (& p)))
p-monotonic1 L p C {n} {x} with is-o∅ (& (PGHOD n L C (find-p L C n (& p))))
... | yes y =  refl-⊆ {* (find-p L C n (& p))}
... | no not = λ  lt →   proj2 (proj2 fmin∈PGHOD) _ lt   where
    fmin : HOD
    fmin = ODC.minimal O (PGHOD n L C (find-p L C n (& p))) (λ eq → not (=od∅→≡o∅ eq))
    fmin∈PGHOD : PGHOD n L C (find-p L C n (& p)) ∋ fmin
    fmin∈PGHOD = ODC.x∋minimal O (PGHOD n L C (find-p L C n (& p))) (λ eq → not (=od∅→≡o∅ eq))

p-monotonic :  (L p : HOD ) (C : CountableModel  ) → {n m : Nat} → n ≤ m → (* (find-p L C m (& p))) ⊆ (* (find-p L C n (& p)))
p-monotonic L p C {Zero} {Zero} n≤m = refl-⊆ {* (find-p L C Zero (& p))}
p-monotonic L p C {Zero} {Suc m} z≤n lt = (p-monotonic L p C {Zero} {m} z≤n ) (p-monotonic1 L p C {m} lt ) 
p-monotonic L p C {Suc n} {Suc m} (s≤s n≤m) with <-cmp n m
... | tri< a ¬b ¬c = λ lt → (p-monotonic L p C {Suc n} {m} a) (p-monotonic1 L p C {m} lt ) 
... | tri≈ ¬a refl ¬c = λ x → x
... | tri> ¬a ¬b c = ⊥-elim ( nat-≤> n≤m c )

P-GenericFilter : (P L p0 : HOD ) → (LP : L ⊆ Power P) → L ∋ p0 → (C : CountableModel ) → GenericFilter {L} {P} LP ( ctl-M C )
P-GenericFilter P L p0 L⊆PP Lp0 C = record {
      genf = record { filter = PDHOD L p0 C ; f⊆L =  f⊆PL ; filter1 = λ L∋q PD∋p p⊆q → f1 L∋q PD∋p p⊆q ; filter2 = f2 }
    ; generic = fdense
   } where
        f⊆PL :  PDHOD L p0 C ⊆ L 
        f⊆PL lt = x∈PP lt  
        f1 : {p q : HOD} → L ∋  q → PDHOD L p0 C ∋ p → p ⊆ q → PDHOD L p0 C ∋ q
        f1 {p} {q} L∋q PD∋p p⊆q =  record { gr = gr PD∋p ;  pn<gr = f04 ; x∈PP = L∋q } where
           f04 : (y : Ordinal) → odef (* (find-p L C (gr PD∋p) (& p0))) y → odef (* (& q)) y
           f04 y lt1 = subst₂ (λ j k → odef j k ) (sym *iso) &iso (p⊆q (subst₂ (λ j k → odef k j ) (sym &iso) *iso ( pn<gr PD∋p y lt1 )))
               -- odef (* (find-p P C (gr PD∋p) (& p0))) y → odef (* (& q)) y
        f2 : {p q : HOD} → PDHOD L p0 C ∋ p → PDHOD L p0 C ∋ q → L ∋ (p ∩ q) → PDHOD L p0 C ∋ (p ∩ q)
        f2 {p} {q} PD∋p PD∋q L∋pq with <-cmp (gr PD∋q) (gr PD∋p)
        ... | tri< a ¬b ¬c = record { gr = gr PD∋p ;  pn<gr = λ y lt → subst (λ k → odef k y ) (sym *iso) (f3 y lt ) ; x∈PP = L∋pq } where
            f3 : (y : Ordinal) → odef (* (find-p L C (gr PD∋p) (& p0))) y → odef (p ∩ q) y
            f3 y lt = ⟪ subst (λ k → odef k y) *iso (pn<gr PD∋p y lt) , subst (λ k → odef k y) *iso (pn<gr PD∋q y (f5 lt)) ⟫ where
               f5 : odef (* (find-p L C (gr PD∋p) (& p0))) y → odef (* (find-p L C (gr PD∋q) (& p0))) y
               f5 lt = subst (λ k → odef (* (find-p L C (gr PD∋q) (& p0))) k ) &iso ( (p-monotonic L p0 C {gr PD∋q} {gr PD∋p} (<to≤ a))
                   (subst (λ k → odef (* (find-p L C (gr PD∋p) (& p0))) k ) (sym &iso) lt) )
        ... | tri≈ ¬a refl ¬c = record { gr = gr PD∋p ;  pn<gr =  λ y lt → subst (λ k → odef k y ) (sym *iso) (f4 y lt) ; x∈PP = L∋pq } where
            f4 : (y : Ordinal) → odef (* (find-p L C (gr PD∋p) (& p0))) y → odef (p ∩ q) y
            f4 y lt = ⟪ subst (λ k → odef k y) *iso (pn<gr PD∋p y lt) , subst (λ k → odef k y) *iso (pn<gr PD∋q y lt) ⟫ 
        ... | tri> ¬a ¬b c = record { gr = gr PD∋q ;  pn<gr =  λ y lt → subst (λ k → odef k y ) (sym *iso) (f3 y lt) ; x∈PP = L∋pq } where 
            f3 : (y : Ordinal) → odef (* (find-p L C (gr PD∋q) (& p0))) y → odef (p ∩ q) y
            f3 y lt = ⟪ subst (λ k → odef k y) *iso (pn<gr PD∋p y (f5 lt)), subst (λ k → odef k y) *iso (pn<gr PD∋q y lt) ⟫ where
               f5 : odef (* (find-p L C (gr PD∋q) (& p0))) y → odef (* (find-p L C (gr PD∋p) (& p0))) y
               f5 lt = subst (λ k → odef (* (find-p L C (gr PD∋p) (& p0))) k ) &iso ( (p-monotonic L p0 C {gr PD∋p} {gr PD∋q} (<to≤ c))
                   (subst (λ k → odef (* (find-p L C (gr PD∋q) (& p0))) k ) (sym &iso) lt) )
        fdense : (D : Dense L⊆PP ) → (ctl-M C ) ∋ Dense.dense D  → ¬ (filter.Dense.dense D ∩ PDHOD L p0 C) ≡ od∅
        fdense D MD eq0  = ⊥-elim (  ∅< {Dense.dense D ∩ PDHOD L p0 C} fd01 (≡od∅→=od∅ eq0 )) where
           open Dense
           fd09 : (i : Nat ) → odef L (find-p L C i (& p0))
           fd09 Zero = Lp0
           fd09 (Suc i) with is-o∅ ( & ( PGHOD i L C (find-p L C i (& p0))) )
           ... | yes _ = fd09 i
           ... | no not = fd17 where
              fd19 =  ODC.minimal O ( PGHOD i L C (find-p L C i (& p0))) (λ eq → not (=od∅→≡o∅ eq))  
              fd18 : PGHOD i L C (find-p L C i (& p0)) ∋ fd19
              fd18 = ODC.x∋minimal O (PGHOD i L C (find-p L C i (& p0))) (λ eq → not (=od∅→≡o∅ eq))
              fd17 :  odef L ( & (ODC.minimal O ( PGHOD i L C (find-p L C i (& p0))) (λ eq → not (=od∅→≡o∅ eq)))  )
              fd17 = proj1 fd18 
           an :  Nat
           an = ctl← C (& (dense D)) MD  
           pn : Ordinal
           pn = find-p L C an (& p0)
           pn+1 : Ordinal
           pn+1 = find-p L C (Suc an) (& p0)
           d=an : dense D ≡ * (ctl→ C an) 
           d=an = begin dense D ≡⟨ sym *iso ⟩
                    * ( & (dense D)) ≡⟨ cong (*) (sym (ctl-iso→  C MD )) ⟩
                    * (ctl→ C an) ∎  where open ≡-Reasoning
           fd07 : odef (dense D) pn+1
           fd07 with is-o∅ ( & ( PGHOD an L C (find-p L C an (& p0))) )
           ... | yes y = ⊥-elim ( ¬x<0 ( _==_.eq→ fd10 ⟪ fd13 , ⟪ fd14 , fd15 ⟫ ⟫ ) ) where
              fd12 : L ∋ * (find-p L C an (& p0))
              fd12 = subst (λ k → odef L k) (sym &iso) (fd09 an )
              fd11 : Ordinal
              fd11 = & ( dense-f D fd12 )
              fd13 : L ∋ ( dense-f D fd12 )
              fd13 = (d⊆P D) (  dense-d D fd12 )
              fd14 : (* (ctl→ C an)) ∋ ( dense-f D fd12 )
              fd14 = subst (λ k → odef k (& ( dense-f D fd12 ) )) d=an (  dense-d D fd12 ) 
              fd15 :  (y : Ordinal) → odef (* (& (dense-f D fd12))) y → odef (* (find-p L C an (& p0))) y
              fd15 y lt = subst (λ k → odef  (* (find-p L C an (& p0)))  k ) &iso ( (dense-p D  fd12 ) fd16  ) where
                  fd16 : odef (dense-f D fd12) (& ( * y))
                  fd16 = subst₂ (λ j k → odef j k ) (*iso) (sym &iso) lt
              fd10 :  PGHOD an L C (find-p L C an (& p0)) =h= od∅
              fd10 = ≡o∅→=od∅ y
           ... | no not = fd27 where
              fd29 =  ODC.minimal O ( PGHOD an L C (find-p L C an (& p0))) (λ eq → not (=od∅→≡o∅ eq))
              fd28 : PGHOD an L C (find-p L C an (& p0)) ∋ fd29
              fd28 = ODC.x∋minimal O (PGHOD an L C (find-p L C an (& p0))) (λ eq → not (=od∅→≡o∅ eq))
              fd27 :  odef (dense D) (& fd29)
              fd27 = subst (λ k → odef k (& fd29)) (sym d=an) (proj1 (proj2 fd28)) 
           fd03 : odef (PDHOD L p0 C) pn+1
           fd03 = record { gr = Suc an ; pn<gr = λ y lt → lt ; x∈PP = fd09 (Suc an)} 
           fd01 : (dense D ∩ PDHOD L p0 C) ∋ (* pn+1)
           fd01 = ⟪ subst (λ k → odef (dense D)  k ) (sym &iso) fd07 , subst (λ k → odef  (PDHOD L p0 C) k) (sym &iso) fd03 ⟫  

open GenericFilter
open Filter

record NonAtomic  (L a : HOD ) (L∋a : L ∋ a ) : Set (suc (suc n)) where
   field
      b : HOD
      0<b : ¬ o∅ ≡ & b
      b<a : b ⊆ a

lemma232 : (P L p : HOD ) (C : CountableModel ) 
    →  (LP : L ⊆ Power P ) →  (Lp0 : L ∋ p  )
    →  ( {q : HOD} → (Lq : L ∋ q ) → NonAtomic L q Lq )
    →  ¬ ( (ctl-M C) ∋ filter ( genf ( P-GenericFilter P L p LP Lp0  C )) )
lemma232 P L p C LP Lp0 NA MG = {!!} where
    D : HOD  -- P - G
    D = ?

--
-- P-Generic Filter defines a countable model D ⊂ C from P
--

--
-- in D, we have V ≠ L
--

--
--   val x G = { val y G | ∃ p → G ∋ p → x ∋ < y , p > }
--

record valR (x : HOD) {P L : HOD} {LP : L ⊆ Power P} (C : CountableModel ) (G : GenericFilter {L} {P} LP (ctl-M C) ) : Set (suc n) where
   field
     valx : HOD

record valS (ox oy oG : Ordinal) : Set n where
   field
     op : Ordinal
     p∈G : odef (* oG) op 
     is-val : odef (* ox) ( & < * oy , * op >  )

val : (x : HOD) {P L : HOD } {LP : L ⊆ Power P}
    →  (G : GenericFilter {L} {P} LP {!!} )
    →  HOD
val x G = TransFinite {λ x → HOD } ind (& x) where
  ind : (x : Ordinal) → ((y : Ordinal) → y o< x → HOD) → HOD
  ind x valy = record { od = record { def = λ y → valS x y (& (filter (genf G))) } ; odmax = {!!} ; <odmax = {!!} }

