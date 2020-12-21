open import Level
open import Ordinals
module filter {n : Level } (O : Ordinals {n})   where

open import zf
open import logic
import OD 

open import Relation.Nullary 
open import Data.Empty 
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality
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
open ODC O

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

∈-filter : {L p : HOD} → (P : Filter L ) → filter P ∋ p → p ⊆ L
∈-filter {L} {p} P lt = power→⊆ L p ( incl (f⊆PL P) lt )

∪-lemma1 : {L p q : HOD } → (p ∪ q)  ⊆ L → p ⊆ L
∪-lemma1 {L} {p} {q} lt = record { incl = λ {x} p∋x → incl lt (case1 p∋x) }

∪-lemma2 : {L p q : HOD } → (p ∪ q)  ⊆ L → q ⊆ L
∪-lemma2 {L} {p} {q} lt = record { incl = λ {x} p∋x → incl lt (case2 p∋x) }

q∩q⊆q : {p q : HOD } → (q ∩ p) ⊆ q 
q∩q⊆q = record { incl = λ lt → proj1 lt } 

open HOD

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
    lemma5 = record { eq→ = λ {x} lt → ⟪ lemma4 x lt , proj2 lt  ⟫
       ;  eq← = λ {x} lt → ⟪  case2 (proj1 lt) , proj2 lt ⟫
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
        eq→ (p+1-p=1 {p} p⊆L) {x} lt | no ¬p = case2 ⟪ lt , ¬p ⟫
        eq← (p+1-p=1 {p} p⊆L) {x} ( case1 p∋x ) = subst (λ k → odef L k ) &iso (incl p⊆L ( subst (λ k → odef p k) (sym &iso) p∋x  )) 
        eq← (p+1-p=1 {p} p⊆L) {x} ( case2 ¬p  ) = proj1 ¬p
        lemma : (p : HOD) → p ⊆ L   →  filter P ∋ (p ∪ (L ＼ p))
        lemma p p⊆L = subst (λ k → filter P ∋ k ) (==→o≡ (p+1-p=1 p⊆L)) f∋L

record Dense  (P : HOD ) : Set (suc n) where
   field
       dense : HOD
       d⊆P :  dense ⊆ Power P 
       dense-f : HOD → HOD
       dense-d :  { p : HOD} → p ⊆ P → dense ∋ dense-f p  
       dense-p :  { p : HOD} → p ⊆ P → p ⊆ (dense-f p) 

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

----
--
-- Filter/Ideal without ZF 
--     L have to be a Latice
--

record F-Filter {n : Level} (L : Set n) (PL : (L → Set n) → Set n) ( _⊆_ : L  → L → Set n)  (_∩_ : L → L → L ) : Set (suc n) where
   field
       filter : L → Set n
       f⊆P :  PL filter 
       filter1 : { p q : L } → PL (λ x → q ⊆ x )  → filter p →  p ⊆ q  → filter q
       filter2 : { p q : L } → filter p →  filter q  → filter (p ∩ q)

Filter-is-F : {L : HOD} → (f : Filter L ) → F-Filter HOD (λ p → (x : HOD) → p x → x ⊆ L ) _⊆_ _∩_
Filter-is-F {L} f = record {
       filter = λ x → Lift (suc n) ((filter f) ∋ x)
     ; f⊆P = λ x f∋x →  power→⊆ _ _ (incl ( f⊆PL f  ) (lower f∋x ))
     ; filter1 = λ {p} {q} q⊆L f∋p  p⊆q → lift ( filter1 f (q⊆L q refl-⊆) (lower f∋p) p⊆q)
     ; filter2 = λ {p} {q} f∋p f∋q  → lift ( filter2 f (lower f∋p) (lower f∋q)) 
    }

record F-Dense {n : Level} (L : Set n) (PL : (L → Set n) → Set n) ( _⊆_ : L  → L → Set n)  (_∩_ : L → L → L ) : Set (suc n) where
   field
       dense : L → Set n
       d⊆P :  PL dense 
       dense-f : L → L 
       dense-d :  { p : L} → PL (λ x → p ⊆ x ) → dense ( dense-f p  )
       dense-p :  { p : L} → PL (λ x → p ⊆ x ) → p ⊆ (dense-f p) 

Dense-is-F : {L : HOD} → (f : Dense L ) → F-Dense HOD (λ p → (x : HOD) → p x → x ⊆ L ) _⊆_ _∩_
Dense-is-F {L} f = record {
       dense =  λ x → Lift (suc n) ((dense f) ∋ x)
    ;  d⊆P = λ x f∋x →  power→⊆ _ _ (incl ( d⊆P f  ) (lower f∋x ))
    ;  dense-f = λ x → dense-f f x
    ;  dense-d = λ {p} d → lift ( dense-d f (d p refl-⊆ ) )
    ;  dense-p = λ {p} d → dense-p f (d p refl-⊆) 
  } where open Dense

       
record GenericFilter (P : HOD) : Set (suc n) where
    field
       genf : Filter P
       generic : (D : Dense P ) → ¬ ( (Dense.dense D ∩ Filter.filter genf ) ≡ od∅ )

record F-GenericFilter {n : Level} (L : Set n) (PL : (L → Set n) → Set n) ( _⊆_ : L  → L → Set n)  (_∩_ : L → L → L ) : Set (suc n) where
    field
       GFilter : F-Filter L PL _⊆_ _∩_
       Intersection : (D : F-Dense L PL _⊆_ _∩_ ) → { x : L } → F-Dense.dense D x →  L
       Generic : (D : F-Dense L PL _⊆_ _∩_ ) → { x : L } → ( y : F-Dense.dense D x) →  F-Filter.filter GFilter (Intersection D y )

