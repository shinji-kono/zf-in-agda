open import Level 
module NSet (n : Level) where

open import logic
open import nat
open import Data.Nat hiding (suc ; zero)
open import Data.Nat.Properties
open import Relation.Binary  hiding (_⇔_)
open import  Relation.Binary.PropositionalEquality hiding ( [_] )

--
-- Primitive Set on ℕ
--

record NSet : Set (suc zero) where
   field
      def : ℕ → Set 

--
-- Set as an equation on ℕ
--
eqa1 : NSet
eqa1 = record { def = λ x →  x * x + 6 ≡ 5 * x   }

open NSet

_∋_ : NSet → ℕ → Set 
S ∋ x = def S x

eq1∋2 : eqa1 ∋ 2
eq1∋2 = refl

eq1∋3 : eqa1 ∋ 3
eq1∋3 = refl

--
-- The solution
--

eqa2 : NSet
eqa2 = record { def = λ x →  (x ≡ 2) ∨ ( x ≡ 3 )   }

eq2∋3 : eqa2 ∋ 3
eq2∋3 = case2 refl

record _==_  ( a b :  NSet  ) : Set  where
  field
     eq→ : ∀ { x : ℕ } → def a x → def b x 
     eq← : ∀ { x : ℕ } → def b x → def a x 

_⊆_ : (a b : NSet ) → Set
_⊆_ a b  = ∀ {x : ℕ} → def a x → def b x

eq2⊆eq1 : eqa2 ⊆ eqa1
eq2⊆eq1 {2} (case1 refl) = refl
eq2⊆eq1 {3} (case2 refl) = refl

-- the other way is slightly difficut

data ⊥ : Set where                                          

⊥-elim : {A : Set } → ⊥ →  A                                      
⊥-elim ()                                          

¬_ : Set → Set                                                                          
¬ A = A → ⊥

n∅ : NSet
n∅  = record { def = λ y → y < 0 }        

¬n∅∋x : {x : ℕ } → ¬ ( n∅ ∋ x  )
¬n∅∋x ()

¬n∅∋x' : {x : ℕ } → ¬ ( n∅ ∋ x  )
¬n∅∋x' {x} nx = ⊥-elim ( n1 nx ) where
   n1 : x < 0 → ⊥
   n1 ()

--
-- Set of subset of ℕ
--

record NSetSet : Set (suc zero) where
   field
      ndef : NSet → Set 

open NSetSet

record _=n=_  ( a b :  NSetSet  ) : Set (suc zero) where
  field
     eq→ : ∀ { x : NSet } → ndef a x → ndef b x 
     eq← : ∀ { x : NSet } → ndef b x → ndef a x 

eqa3 : NSetSet
eqa3 = record { ndef = λ x →  x == eqa2   }

--
--  Can we defined hierarchy of Set in monothic and consitent way?
--     equations on Ordinal is an solution (Ordinal Definable Set)
--     but we need some axioms to achive ZF Set Theory
--




