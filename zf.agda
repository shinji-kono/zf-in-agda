module zf where

open import Level

data Bool : Set where
   true : Bool
   false : Bool

record  _∧_  {n m : Level} (A  : Set n) ( B : Set m ) : Set (n ⊔ m) where
   field 
      proj1 : A
      proj2 : B

data  _∨_  {n m : Level} (A  : Set n) ( B : Set m ) : Set (n ⊔ m) where
   case1 : A → A ∨ B
   case2 : B → A ∨ B

_⇔_ : {n : Level } → ( A B : Set n )  → Set  n
_⇔_ A B =  ( A → B ) ∧ ( B → A )

open import Relation.Nullary
open import Relation.Binary

infixr  130 _∧_
infixr  140 _∨_
infixr  150 _⇔_

record IsZF {n m : Level }
     (ZFSet : Set n)
     (_∋_ : ( A x : ZFSet  ) → Set m)
     (_≈_ : Rel ZFSet m)
     (∅  : ZFSet)
     (_,_ : ( A B : ZFSet  ) → ZFSet)
     (Union : ( A : ZFSet  ) → ZFSet)
     (Power : ( A : ZFSet  ) → ZFSet)
     (Select : ZFSet → ( ZFSet → Set m ) → ZFSet )
     (Replace : ZFSet → ( ZFSet → ZFSet ) → ZFSet )
     (infinite : ZFSet)
       : Set (suc (n ⊔ m)) where
  field
     isEquivalence : IsEquivalence {n} {m} {ZFSet} _≈_ 
     -- ∀ x ∀ y ∃ z(x ∈ z ∧ y ∈ z)
     pair : ( A B : ZFSet  ) →  ( (A , B)  ∋ A ) ∧ ( (A , B)  ∋ B  )
     -- ∀ x ∃ y ∀ z (z ∈ y ⇔ ∃ u ∈ x  ∧ (z ∈ u))
     union-u : ( X z : ZFSet  ) → Union X ∋ z → ZFSet
     union→ : ( X z u : ZFSet ) → ( X ∋ u ) ∧ (u ∋ z ) → Union X ∋ z
     union← : ( X z : ZFSet ) → (X∋z : Union X ∋ z ) → (X ∋ union-u X z X∋z)  ∧ (union-u X z X∋z ∋ z )
  _∈_ : ( A B : ZFSet  ) → Set m
  A ∈ B = B ∋ A
  _⊆_ : ( A B : ZFSet  ) → ∀{ x : ZFSet } →  Set m
  _⊆_ A B {x} = A ∋ x →  B ∋ x
  _∩_ : ( A B : ZFSet  ) → ZFSet
  A ∩ B = Select A (  λ x → ( A ∋ x ) ∧ ( B ∋ x )  )
  _∪_ : ( A B : ZFSet  ) → ZFSet
  A ∪ B = Union (A , B)    -- Select A (  λ x → ( A ∋ x ) ∨ ( B ∋ x )  ) is easer
  ｛_｝ : ZFSet → ZFSet
  ｛ x ｝ = ( x ,  x )
  infixr  200 _∈_
  infixr  230 _∩_ _∪_
  infixr  220 _⊆_ 
  field
     empty :  ∀( x : ZFSet  ) → ¬ ( ∅ ∋ x )
     -- power : ∀ X ∃ A ∀ t ( t ∈ A ↔ t ⊆ X ) )
     power→ : ∀( A t : ZFSet  ) → Power A ∋ t → ∀ {x}  →  _⊆_ t A {x} 
     power← : ∀( A t : ZFSet  ) → ( ∀ {x}  →  _⊆_ t A {x})  → Power A ∋ t 
     -- extensionality : ∀ z ( z ∈ x ⇔ z ∈ y ) ⇒ ∀ w ( x ∈ w ⇔ y ∈ w )
     extensionality :  { A B : ZFSet  } → ( (z : ZFSet) → ( A ∋ z ) ⇔ (B ∋ z)  ) → A ≈ B
     -- regularity : ∀ x ( x ≠ ∅ → ∃ y ∈ x ( y ∩ x = ∅ ) )
     minimul : (x : ZFSet ) → ¬ (x ≈ ∅) → ZFSet 
     regularity : ∀( x : ZFSet  ) → (not : ¬ (x ≈ ∅)) → (  minimul x not  ∈ x ∧  (  minimul x not  ∩ x  ≈ ∅ ) )
     -- infinity : ∃ A ( ∅ ∈ A ∧ ∀ x ∈ A ( x ∪ { x } ∈ A ) )
     infinity∅ :  ∅ ∈ infinite
     infinity :  ∀( X x : ZFSet  ) → x ∈ infinite →  ( x ∪ ｛ x ｝) ∈ infinite 
     selection : { ψ : ZFSet → Set m } → ∀ { X y : ZFSet  } →  ( ( y ∈ X ) ∧ ψ y ) ⇔ (y ∈  Select X ψ ) 
     -- replacement : ∀ x ∀ y ∀ z ( ( ψ ( x , y ) ∧ ψ ( x , z ) ) → y = z ) → ∀ X ∃ A ∀ y ( y ∈ A ↔ ∃ x ∈ X ψ ( x , y ) )
     replacement : {ψ : ZFSet → ZFSet} → ∀ ( X x : ZFSet  ) →  ( ψ x ∈  Replace X ψ )  

record ZF {n m : Level } : Set (suc (n ⊔ m)) where
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
     Select : ZFSet → ( ZFSet → Set m ) → ZFSet
     Replace : ZFSet → ( ZFSet → ZFSet ) → ZFSet
     infinite : ZFSet
     isZF : IsZF ZFSet _∋_ _≈_ ∅ _,_ Union Power Select Replace infinite 

