open import Level
open import OD
open import zf
open import ordinal
module filter ( n : Level )  where

open import Relation.Nullary
open import Relation.Binary
open import Data.Empty
open import Relation.Binary
open import Relation.Binary.Core
open import  Relation.Binary.PropositionalEquality
open import Data.Nat renaming ( zero to Zero ; suc to Suc ;  ℕ to Nat ; _⊔_ to _n⊔_ ) 

od = OD→ZF {n}


record Filter {n : Level} ( P max : OD {suc n} )  : Set (suc (suc n)) where
   field
       _⊇_ : OD {suc n} → OD {suc n} → Set (suc n)
       G : OD {suc n}
       G∋1 : G ∋ max
       Gmax : { p : OD {suc n} } → P ∋ p → p ⊇  max 
       Gless : { p q : OD {suc n} } → G ∋ p → P ∋ q →  p ⊇ q  → G ∋ q
       Gcompat : { p q : OD {suc n} } → G ∋ p → G ∋ q → ¬ (
           ( r : OD {suc n}) →  ((  p ⊇  r ) ∧ (  p ⊇ r )))

dense :  {n : Level} → Set (suc (suc n))
dense {n} = { D P p : OD {suc n} } → ({x : OD {suc n}} → P ∋ p → ¬ ( ( q : OD {suc n}) → D ∋ q → od→ord p o< od→ord q ))

record NatFilter {n : Level} ( P : Nat → Set n)  : Set (suc n) where
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

Pred : {n : Level} ( Dom : OD {suc n} ) → OD {suc n}
Pred {n} dom = record {
      def = λ x → def dom x → Set n
  }

Hω2 : {n : Level} →  OD {suc n}
Hω2 {n} = record { def = λ x → {dom : Ordinal {suc n}} → x ≡ od→ord ( Pred ( ord→od dom )) }

Hω2Filter :   {n : Level} → Filter {n} Hω2 od∅
Hω2Filter {n} = record {
       _⊇_ = _⊇_
     ; G = {!!}
     ; G∋1 = {!!}
     ; Gmax = {!!}
     ; Gless = {!!}
     ; Gcompat = {!!}
  } where
       P = Hω2
       _⊇_ : OD {suc n} → OD {suc n} → Set (suc n)
       _⊇_ = {!!}
       G : OD {suc n}
       G = {!!}
       G∋1 : G ∋ od∅
       G∋1 = {!!}
       Gmax : { p : OD {suc n} } → P ∋ p → p ⊇  od∅
       Gmax = {!!}
       Gless : { p q : OD {suc n} } → G ∋ p → P ∋ q →  p ⊇ q  → G ∋ q
       Gless = {!!}
       Gcompat : { p q : OD {suc n} } → G ∋ p → G ∋ q → ¬ (
           ( r : OD {suc n}) →  ((  p ⊇  r ) ∧ (  p ⊇ r )))
       Gcompat = {!!}

