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

record Filter  ( P max : OD  )  : Set (suc n) where
   field
       _⊇_ : OD  → OD  → Set n
       G : OD 
       G∋1 : G ∋ max
       Gmax : { p : OD  } → P ∋ p → p ⊇  max 
       Gless : { p q : OD  } → G ∋ p → P ∋ q →  p ⊇ q  → G ∋ q
       Gcompat : { p q : OD  } → G ∋ p → G ∋ q → ¬ (
           ( r : OD ) →  ((  p ⊇  r ) ∧ (  p ⊇ r )))

dense :   Set (suc n)
dense = { D P p : OD  } → ({x : OD } → P ∋ p → ¬ ( ( q : OD ) → D ∋ q → od→ord p o< od→ord q ))

record NatFilter  ( P : Nat → Set n)  : Set (suc n) where
   field
       GN : Nat → Set n
       GN∋1 : GN 0
       GNmax : { p : Nat } → P p →  0 ≤ p 
       GNless : { p q : Nat } → GN p → P q →  q ≤ p  → GN q
       Gr : (  p q : Nat ) →  GN p → GN q  →  Nat
       GNcompat : { p q : Nat }  → (gp : GN p) → (gq : GN q ) → (  Gr p q gp gq ≤  p ) ∨ (  Gr p q gp gq ≤ q )

record NatDense {n : Level} ( P : Nat → Set n)  : Set (suc n) where
   field
       Gmid : { p : Nat } → P p  → Nat
       GDense : { D : Nat → Set n } → {x p : Nat } → (pp : P p ) → D (Gmid {p} pp) →  Gmid pp  ≤ p 

open OD.OD

-- H(ω,2) = Power ( Power ω ) = Def ( Def ω))

Pred :  ( Dom : OD  ) → OD 
Pred  dom = record {
      def = λ x → def dom x → {!!}
  }

Hω2 :   OD 
Hω2  = record { def = λ x → {dom : Ordinal } → x ≡ od→ord ( Pred ( ord→od dom )) }

Hω2Filter :     Filter  Hω2 od∅
Hω2Filter  = record {
       _⊇_ = _⊇_
     ; G = {!!}
     ; G∋1 = {!!}
     ; Gmax = {!!}
     ; Gless = {!!}
     ; Gcompat = {!!}
  } where
       P = Hω2
       _⊇_ : OD  → OD  → Set n
       _⊇_ = {!!}
       G : OD 
       G = {!!}
       G∋1 : G ∋ od∅
       G∋1 = {!!}
       Gmax : { p : OD  } → P ∋ p → p ⊇  od∅
       Gmax = {!!}
       Gless : { p q : OD  } → G ∋ p → P ∋ q →  p ⊇ q  → G ∋ q
       Gless = {!!}
       Gcompat : { p q : OD  } → G ∋ p → G ∋ q → ¬ (
           ( r : OD ) →  ((  p ⊇  r ) ∧ (  p ⊇ r )))
       Gcompat = {!!}

