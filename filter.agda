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
record Filter  ( L : HOD  ) : Set (suc n) where
   field
       filter : HOD   
       f⊆PL :  filter ⊆ Power L 
       filter1 : { p q : HOD } →  q ⊆ L  → filter ∋ p →  p ⊆ q  → filter ∋ q
       filter2 : { p q : HOD } → filter ∋ p →  filter ∋ q  → filter ∋ (p ∩ q)

open Filter

record prime-filter { L : HOD } (P : Filter L) : Set (suc (suc n)) where
   field
       proper  : ¬ (filter P ∋ od∅)
       prime   : {p q : HOD } →  filter P ∋ (p ∪ q) → ( filter P ∋ p ) ∨ ( filter P ∋ q )

record ultra-filter { L : HOD } (P : Filter L) : Set (suc (suc n)) where
   field
       proper  : ¬ (filter P ∋ od∅)
       ultra   : {p : HOD } → p ⊆ L →  ( filter P ∋ p ) ∨ (  filter P ∋ ( L ＼ p) )

open _⊆_

trans-⊆ :  { A B C : HOD} → A ⊆ B → B ⊆ C → A ⊆ C
trans-⊆ A⊆B B⊆C = record { incl = λ x → incl B⊆C (incl A⊆B x) }

power→⊆ :  ( A t : HOD) → Power A ∋ t → t ⊆ A
power→⊆ A t  PA∋t = record { incl = λ {x} t∋x → ODC.double-neg-eilm O (t1 t∋x) } where
   t1 : {x : HOD }  → t ∋ x → ¬ ¬ (A ∋ x)
   t1 = zf.IsZF.power→ isZF A t PA∋t

∈-filter : {L p : HOD} → (P : Filter L ) → filter P ∋ p → p ⊆ L
∈-filter {L} {p} P lt = power→⊆ L p ( incl (f⊆PL P) lt )

∪-lemma1 : {L p q : HOD } → (p ∪ q)  ⊆ L → p ⊆ L
∪-lemma1 {L} {p} {q} lt = record { incl = λ {x} p∋x → incl lt (case1 p∋x) }

∪-lemma2 : {L p q : HOD } → (p ∪ q)  ⊆ L → q ⊆ L
∪-lemma2 {L} {p} {q} lt = record { incl = λ {x} p∋x → incl lt (case2 p∋x) }

q∩q⊆q : {p q : HOD } → (q ∩ p) ⊆ q 
q∩q⊆q = record { incl = λ lt → proj1 lt } 

open HOD
_=h=_ : (x y : HOD) → Set n
x =h= y  = od x == od y

-----
--
--  ultra filter is prime
--

filter-lemma1 :  {L : HOD} → (P : Filter L)  → ∀ {p q : HOD } → ultra-filter P  → prime-filter P 
filter-lemma1 {L} P u = record {
         proper = ultra-filter.proper u
       ; prime = lemma3
    } where
  lemma3 : {p q : HOD} → filter P ∋ (p ∪ q) → ( filter P ∋ p ) ∨ ( filter P ∋ q )
  lemma3 {p} {q} lt with ultra-filter.ultra u (∪-lemma1 (∈-filter P lt) )
  ... | case1 p∈P  = case1 p∈P
  ... | case2 ¬p∈P = case2 (filter1 P {q ∩ (L ＼ p)} (∪-lemma2 (∈-filter P lt)) lemma7 lemma8) where
    lemma5 : ((p ∪ q ) ∩ (L ＼ p)) =h=  (q ∩ (L ＼ p))
    lemma5 = record { eq→ = λ {x} lt → record { proj1 = lemma4 x lt ; proj2 = proj2 lt  }
       ;  eq← = λ {x} lt → record { proj1 = case2 (proj1 lt) ; proj2 = proj2 lt }
      } where
         lemma4 : (x : Ordinal ) → odef ((p ∪ q) ∩ (L ＼ p)) x → odef q x
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

filter-lemma2 :  {L : HOD} → (P : Filter L)  → filter P ∋ L → prime-filter P → ultra-filter P
filter-lemma2 {L} P f∋L prime = record {
         proper = prime-filter.proper prime
       ; ultra = λ {p}  p⊆L → prime-filter.prime prime (lemma p  p⊆L)
   } where
        open _==_
        p+1-p=1 : {p : HOD} → p ⊆ L → L =h= (p ∪ (L ＼ p)) 
        eq→ (p+1-p=1 {p} p⊆L) {x} lt with ODC.decp O (odef p x)
        eq→ (p+1-p=1 {p} p⊆L) {x} lt | yes p∋x = case1 p∋x
        eq→ (p+1-p=1 {p} p⊆L) {x} lt | no ¬p = case2 (record { proj1 = lt ; proj2 = ¬p })
        eq← (p+1-p=1 {p} p⊆L) {x} ( case1 p∋x ) = subst (λ k → odef L k ) diso (incl p⊆L ( subst (λ k → odef p k) (sym diso) p∋x  )) 
        eq← (p+1-p=1 {p} p⊆L) {x} ( case2 ¬p  ) = proj1 ¬p
        lemma : (p : HOD) → p ⊆ L   →  filter P ∋ (p ∪ (L ＼ p))
        lemma p p⊆L = subst (λ k → filter P ∋ k ) (==→o≡ (p+1-p=1 p⊆L)) f∋L

record Dense  (P : HOD ) : Set (suc n) where
   field
       dense : HOD
       incl :  dense ⊆ P 
       dense-f : HOD → HOD
       dense-d :  { p : HOD} → P ∋ p  → dense ∋ dense-f p  
       dense-p :  { p : HOD} → P ∋ p  →  p ⊆ (dense-f p) 

--    the set of finite partial functions from ω to 2
--
--   ph2 : Nat → Set → 2
--   ph2 : Nat → Maybe 2
--
-- Hω2 : Filter (Power (Power infinite))

record Ideal  ( L : HOD  ) : Set (suc n) where
   field
       ideal : HOD   
       i⊆PL :  ideal ⊆ Power L 
       ideal1 : { p q : HOD } →  q ⊆ L  → ideal ∋ p →  q ⊆ p  → ideal ∋ q
       ideal2 : { p q : HOD } → ideal ∋ p →  ideal ∋ q  → ideal ∋ (p ∪ q)

open Ideal

proper-ideal : {L : HOD} → (P : Ideal L ) → {p : HOD} → Set n
proper-ideal {L} P {p} = ideal P ∋ od∅

prime-ideal : {L : HOD} → Ideal L → ∀ {p q : HOD } → Set n
prime-ideal {L} P {p} {q} =  ideal P ∋ ( p ∩ q) → ( ideal P ∋ p ) ∨ ( ideal P ∋ q )

