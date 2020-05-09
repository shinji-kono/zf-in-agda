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

open inOrdinal O
open OD O
open OD.OD

open _∧_
open _∨_
open Bool

_∩_ : ( A B : OD  ) → OD
A ∩ B = record { def = λ x → def A x ∧ def B x } 

_∪_ : ( A B : OD  ) → OD
A ∪ B = record { def = λ x → def A x ∨ def B x } 

_＼_ : ( A B : OD  ) → OD
A ＼ B = record { def = λ x → def A x ∧ ( ¬ ( def B x ) ) }


record Filter  ( L : OD  ) : Set (suc n) where
   field
       filter : OD
       proper : ¬ ( filter ∋ od∅ )
       inL :  filter ⊆ L 
       filter1 : { p q : OD } →  q ⊆ L  → filter ∋ p →  p ⊆ q  → filter ∋ q
       filter2 : { p q : OD } → filter ∋ p →  filter ∋ q  → filter ∋ (p ∩ q)

open Filter

L-filter : {L : OD} → (P : Filter L ) → {p : OD} → filter P ∋ p → filter P ∋ L
L-filter {L} P {p} lt = filter1 P {p} {L} {!!} lt {!!}

prime-filter : {L : OD} → Filter L → ∀ {p q : OD } → Set n
prime-filter {L} P {p} {q} =  filter P ∋ ( p ∪ q) → ( filter P ∋ p ) ∨ ( filter P ∋ q )

ultra-filter :  {L : OD} → Filter L → ∀ {p : OD } → Set n 
ultra-filter {L} P {p} = L ∋ p →  ( filter P ∋ p ) ∨ (  filter P ∋ ( L ＼ p) )


filter-lemma1 :  {L : OD} → (P : Filter L)  → ∀ {p q : OD } → ( ∀ (p : OD ) → ultra-filter {L} P {p} ) → prime-filter {L} P {p} {q}
filter-lemma1 {L} P {p} {q} u lt = {!!}

filter-lemma2 :  {L : OD} → (P : Filter L)  → ( ∀ {p q : OD } → prime-filter {L} P {p} {q}) →  ∀ (p : OD ) → ultra-filter {L} P {p} 
filter-lemma2 {L} P prime p with prime {!!}
... | t = {!!}

generated-filter : {L : OD} → Filter L → (p : OD ) → Filter ( record { def = λ x → def L x ∨ (x ≡ od→ord p) } )
generated-filter {L} P p = record {
     proper = {!!} ; 
     filter = {!!}  ; inL = {!!} ; 
     filter1 = {!!} ; filter2 = {!!}
   }

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

