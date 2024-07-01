{-# OPTIONS --cubical-compatible --safe #-}
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
       : Set (suc (n ⊔ suc m)) where
  field
     -- ∀ X [ ∅ ∉ X → (∃ f : X → ⋃ X ) → ∀ A ∈ X ( f ( A ) ∈ A ) ]
     choice-func : (X : ZFSet ) → {x : ZFSet } → ¬ ( x ≈ ∅ ) → ( X ∋ x ) → ZFSet
     choice : (X : ZFSet  ) → {A : ZFSet } → ( X∋A : X ∋ A ) → (not : ¬ ( A ≈ ∅ )) → A ∋ choice-func X not X∋A

record ZFC {n m : Level } : Set (suc (n ⊔ suc m)) where
  field
     ZFSet : Set n
     _∋_ : ( A x : ZFSet  ) → Set m 
     _≈_ : ( A B : ZFSet  ) → Set m
     ∅  : ZFSet
     isZFC : IsZFC ZFSet _∋_ _≈_ ∅ 

