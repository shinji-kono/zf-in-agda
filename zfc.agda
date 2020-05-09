module zfc where

open import Level
open import Relation.Binary
open import Relation.Nullary
open import logic

record IsZFC {n m : Level }
     (ZFSet : Set n)
     (_∋_ : ( A x : ZFSet  ) → Set m)
     (_≈_ : Rel ZFSet m)
     (∅  : ZFSet)
     (Select :  (X : ZFSet  ) → ( ψ : (x : ZFSet ) → Set m ) → ZFSet ) 
       : Set (suc (n ⊔ suc m)) where
  field
     -- ∀ X [ ∅ ∉ X → (∃ f : X → ⋃ X ) → ∀ A ∈ X ( f ( A ) ∈ A ) ]
     choice-func : (X : ZFSet ) → {x : ZFSet } → ¬ ( x ≈ ∅ ) → ( X ∋ x ) → ZFSet
     choice : (X : ZFSet  ) → {A : ZFSet } → ( X∋A : X ∋ A ) → (not : ¬ ( A ≈ ∅ )) → A ∋ choice-func X not X∋A
  infixr  200 _∈_
  infixr  230 _∩_ 
  _∈_ : ( A B : ZFSet  ) → Set m
  A ∈ B = B ∋ A
  _∩_ : ( A B : ZFSet  ) → ZFSet
  A ∩ B = Select A (  λ x → ( A ∋ x ) ∧ ( B ∋ x )  )

record ZFC {n m : Level } : Set (suc (n ⊔ suc m)) where
  field
     ZFSet : Set n
     _∋_ : ( A x : ZFSet  ) → Set m 
     _≈_ : ( A B : ZFSet  ) → Set m
     ∅  : ZFSet
     Select :  (X : ZFSet  ) → ( ψ : (x : ZFSet ) → Set m ) → ZFSet 
     isZFC : IsZFC ZFSet _∋_ _≈_ ∅ Select

