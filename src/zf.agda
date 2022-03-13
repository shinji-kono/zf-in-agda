module zf where

open import Level

open import logic

open import Relation.Nullary
open import Relation.Binary hiding (_⇔_)
open import Data.Empty

record IsZF {n m : Level }
     (ZFSet : Set n)
     (_∋_ : ( A x : ZFSet  ) → Set m)
     (_≈_ : Rel ZFSet m)
     (∅  : ZFSet)
     (_,_ : ( A B : ZFSet  ) → ZFSet)
     (Union : ( A : ZFSet  ) → ZFSet)
     (Power : ( A : ZFSet  ) → ZFSet)
     (Select :  (X : ZFSet  ) → ( ψ : (x : ZFSet ) → Set m ) → ZFSet ) 
     (Replace : ZFSet → ( ZFSet → ZFSet ) → ZFSet )
     (infinite : ZFSet)
       : Set (suc (n ⊔ suc m)) where
  field
     isEquivalence : IsEquivalence {n} {m} {ZFSet} _≈_ 
     -- ∀ x ∀ y ∃ z ∀ t ( z ∋ t → t ≈ x ∨ t  ≈ y)
     pair→ : ( x y t : ZFSet  ) →  (x , y)  ∋ t  → ( t ≈ x ) ∨ ( t ≈ y ) 
     pair← : ( x y t : ZFSet  ) →  ( t ≈ x ) ∨ ( t ≈ y )  →  (x , y)  ∋ t 
     -- ∀ x ∃ y ∀ z (z ∈ y ⇔ ∃ u ∈ x  ∧ (z ∈ u))
     union→ : ( X z u : ZFSet ) → ( X ∋ u ) ∧ (u ∋ z ) → Union X ∋ z
     union← : ( X z : ZFSet ) → (X∋z : Union X ∋ z ) →  ¬  ( (u : ZFSet ) → ¬ ((X ∋  u) ∧ (u ∋ z )))
  _∈_ : ( A B : ZFSet  ) → Set m
  A ∈ B = B ∋ A
  _⊆_ : ( A B : ZFSet  ) → ∀{ x : ZFSet } →  Set m
  _⊆_ A B {x} = A ∋ x →  B ∋ x
  _∩_ : ( A B : ZFSet  ) → ZFSet
  A ∩ B = Select A (  λ x → ( A ∋ x ) ∧ ( B ∋ x )  )
  _∪_ : ( A B : ZFSet  ) → ZFSet
  A ∪ B = Union (A , B)    
  ｛_｝ : ZFSet → ZFSet
  ｛ x ｝ = ( x ,  x )
  infixr  200 _∈_
  infixr  230 _∩_ _∪_
  infixr  220 _⊆_ 
  field
     empty :  ∀( x : ZFSet  ) → ¬ ( ∅ ∋ x )
     -- power : ∀ X ∃ A ∀ t ( t ∈ A ↔ t ⊆ X ) )
     power→ : ∀( A t : ZFSet  ) → Power A ∋ t → ∀ {x}  →  t ∋ x → ¬ ¬ ( A ∋ x ) -- _⊆_ t A {x} 
     power← : ∀( A t : ZFSet  ) → ( ∀ {x}  →  _⊆_ t A {x})  → Power A ∋ t 
     -- extensionality : ∀ z ( z ∈ x ⇔ z ∈ y ) ⇒ ∀ w ( x ∈ w ⇔ y ∈ w )
     extensionality :  { A B w : ZFSet  } → ( (z : ZFSet) → ( A ∋ z ) ⇔ (B ∋ z)  ) → ( A ∈ w ⇔ B ∈ w )
     -- regularity without minimum
     ε-induction : { ψ : ZFSet → Set (suc m Level.⊔ n)}
              → ( {x : ZFSet } → ({ y : ZFSet } →  x ∋ y → ψ y ) → ψ x )
              → (x : ZFSet ) → ψ x
     -- infinity : ∃ A ( ∅ ∈ A ∧ ∀ x ∈ A ( x ∪ { x } ∈ A ) )
     infinity∅ :  ∅ ∈ infinite
     infinity :  ∀( x : ZFSet  ) → x ∈ infinite →  ( x ∪ ｛ x ｝) ∈ infinite 
     selection : { ψ : ZFSet → Set m } → ∀ { X y : ZFSet  } →  ( ( y ∈ X ) ∧ ψ y ) ⇔ (y ∈  Select X ψ ) 
     -- replacement : ∀ x ∀ y ∀ z ( ( ψ ( x , y ) ∧ ψ ( x , z ) ) → y = z ) → ∀ X ∃ A ∀ y ( y ∈ A ↔ ∃ x ∈ X ψ ( x , y ) )
     replacement← : {ψ : ZFSet → ZFSet} → ∀ ( X x : ZFSet  ) → x ∈ X → ψ x ∈  Replace X ψ 
     replacement→ : {ψ : ZFSet → ZFSet} → ∀ ( X x : ZFSet  ) →  ( lt : x ∈  Replace X ψ ) → ¬ ( ∀ (y : ZFSet)  →  ¬ ( x ≈ ψ y ) )

record ZF {n m : Level } : Set (suc (n ⊔ suc m)) where
  infixr  210 _,_
  infixl  200 _∋_ 
  infixr  220 _≈_
  field
     ZFSet : Set n
     _∋_ : ( A x : ZFSet  ) → Set m 
     _≈_ : ( A B : ZFSet  ) → Set m
  -- ZF Set constructor
     ∅  : ZFSet
     _,_ : ( A B : ZFSet  ) → ZFSet
     Union : ( A : ZFSet  ) → ZFSet
     Power : ( A : ZFSet  ) → ZFSet
     Select :  (X : ZFSet  ) → ( ψ : (x : ZFSet ) → Set m ) → ZFSet 
     Replace : ZFSet → ( ZFSet → ZFSet ) → ZFSet
     infinite : ZFSet
     isZF : IsZF ZFSet _∋_ _≈_ ∅ _,_ Union Power Select Replace infinite 

