open import Level
open import Ordinals
module filter {n : Level } (O : Ordinals {n})   where

open import zf
open import logic
import OD 

open import Relation.Nullary
open import Relation.Binary
open import Data.Empty
open import Relation.Binary
open import Relation.Binary.Core
open import  Relation.Binary.PropositionalEquality
open import Data.Nat renaming ( zero to Zero ; suc to Suc ;  ℕ to Nat ; _⊔_ to _n⊔_ ) 
import BAlgbra

open BAlgbra O

open inOrdinal O
open OD O
open OD.OD
open ODAxiom odAxiom

import ODC

open _∧_
open _∨_
open Bool

-- Kunen p.76 and p.53, we use ⊆
record Filter  ( L : OD  ) : Set (suc n) where
   field
       filter : OD   
       f⊆PL :  filter ⊆ Power L 
       filter1 : { p q : OD } →  q ⊆ L  → filter ∋ p →  p ⊆ q  → filter ∋ q
       filter2 : { p q : OD } → filter ∋ p →  filter ∋ q  → filter ∋ (p ∩ q)

open Filter

record prime-filter { L : OD } (P : Filter L) : Set (suc (suc n)) where
   field
       proper  : ¬ (filter P ∋ od∅)
       prime   : {p q : OD } →  filter P ∋ (p ∪ q) → ( filter P ∋ p ) ∨ ( filter P ∋ q )

record ultra-filter { L : OD } (P : Filter L) : Set (suc (suc n)) where
   field
       proper  : ¬ (filter P ∋ od∅)
       ultra   : {p : OD } → p ⊆ L →  ( filter P ∋ p ) ∨ (  filter P ∋ ( L ＼ p) )

open _⊆_

trans-⊆ :  { A B C : OD} → A ⊆ B → B ⊆ C → A ⊆ C
trans-⊆ A⊆B B⊆C = record { incl = λ x → incl B⊆C (incl A⊆B x) }

power→⊆ :  ( A t : OD) → Power A ∋ t → t ⊆ A
power→⊆ A t  PA∋t = record { incl = λ {x} t∋x → ODC.double-neg-eilm O (t1 t∋x) } where
   t1 : {x : OD }  → t ∋ x → ¬ ¬ (A ∋ x)
   t1 = zf.IsZF.power→ isZF A t PA∋t

∈-filter : {L p : OD} → (P : Filter L ) → filter P ∋ p → p ⊆ L
∈-filter {L} {p} P lt = power→⊆ L p ( incl (f⊆PL P) lt )

∪-lemma1 : {L p q : OD } → (p ∪ q)  ⊆ L → p ⊆ L
∪-lemma1 {L} {p} {q} lt = record { incl = λ {x} p∋x → incl lt (case1 p∋x) }

∪-lemma2 : {L p q : OD } → (p ∪ q)  ⊆ L → q ⊆ L
∪-lemma2 {L} {p} {q} lt = record { incl = λ {x} p∋x → incl lt (case2 p∋x) }

q∩q⊆q : {p q : OD } → (q ∩ p) ⊆ q 
q∩q⊆q = record { incl = λ lt → proj1 lt } 

-----
--
--  ultra filter is prime
--

filter-lemma1 :  {L : OD} → (P : Filter L)  → ∀ {p q : OD } → ultra-filter P  → prime-filter P 
filter-lemma1 {L} P u = record {
         proper = ultra-filter.proper u
       ; prime = lemma3
    } where
  lemma3 : {p q : OD} → filter P ∋ (p ∪ q) → ( filter P ∋ p ) ∨ ( filter P ∋ q )
  lemma3 {p} {q} lt with ultra-filter.ultra u (∪-lemma1 (∈-filter P lt) )
  ... | case1 p∈P  = case1 p∈P
  ... | case2 ¬p∈P = case2 (filter1 P {q ∩ (L ＼ p)} (∪-lemma2 (∈-filter P lt)) lemma7 lemma8) where
    lemma5 : ((p ∪ q ) ∩ (L ＼ p)) ==  (q ∩ (L ＼ p))
    lemma5 = record { eq→ = λ {x} lt → record { proj1 = lemma4 x lt ; proj2 = proj2 lt  }
       ;  eq← = λ {x} lt → record { proj1 = case2 (proj1 lt) ; proj2 = proj2 lt }
      } where
         lemma4 : (x : Ordinal ) → def ((p ∪ q) ∩ (L ＼ p)) x → def q x
         lemma4 x lt with proj1 lt
         lemma4 x lt | case1 px = ⊥-elim ( proj2 (proj2 lt) px )
         lemma4 x lt | case2 qx = qx
    lemma6 : filter P ∋ ((p ∪ q ) ∩ (L ＼ p))
    lemma6 = filter2 P lt ¬p∈P
    lemma7 : filter P ∋ (q ∩ (L ＼ p))
    lemma7 =  subst (λ k → filter P ∋ k ) (==→o≡ lemma5 ) lemma6
    lemma8 : (q ∩ (L ＼ p)) ⊆ q
    lemma8 = q∩q⊆q

-----
--
--  if Filter contains L, prime filter is ultra
--

filter-lemma2 :  {L : OD} → (P : Filter L)  → prime-filter P → ultra-filter P
filter-lemma2 {L} P prime  = {!!}

generated-filter : {L : OD} → Filter L → (p : OD ) → Filter ( record { def = λ x → def L x ∨ (x ≡ od→ord p) } )
generated-filter {L} P p = {!!}

record Dense  (P : OD ) : Set (suc n) where
   field
       dense : OD
       incl :  dense ⊆ P 
       dense-f : OD → OD
       dense-p :  { p : OD} → P ∋ p  → p ⊆ (dense-f p) 

-- H(ω,2) = Power ( Power ω ) = Def ( Def ω))

infinite = ZF.infinite OD→ZF

module in-countable-ordinal {n : Level} where

   import ordinal

   -- open  ordinal.C-Ordinal-with-choice 

   Hω2 : Filter (Power (Power infinite))
   Hω2 = {!!}


record Ideal  ( L : OD  ) : Set (suc n) where
   field
       ideal : OD   
       i⊆PL :  ideal ⊆ Power L 
       ideal1 : { p q : OD } →  q ⊆ L  → ideal ∋ p →  q ⊆ p  → ideal ∋ q
       ideal2 : { p q : OD } → ideal ∋ p →  ideal ∋ q  → ideal ∋ (p ∪ q)

open Ideal

proper-ideal : {L : OD} → (P : Ideal L ) → {p : OD} → Set n
proper-ideal {L} P {p} = ideal P ∋ od∅

prime-ideal : {L : OD} → Ideal L → ∀ {p q : OD } → Set n
prime-ideal {L} P {p} {q} =  ideal P ∋ ( p ∩ q) → ( ideal P ∋ p ) ∨ ( ideal P ∋ q )

