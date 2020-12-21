open import Level
module Ordinals where

open import zf

open import Data.Nat renaming ( zero to Zero ; suc to Suc ;  ℕ to Nat ; _⊔_ to _n⊔_ ) 
open import Data.Empty
open import  Relation.Binary.PropositionalEquality
open import  logic
open import  nat
open import Data.Unit using ( ⊤ )
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.Core

record Oprev {n : Level} (ord : Set n) (osuc :  ord → ord ) (x : ord ) : Set (suc n) where
   field
     oprev : ord
     oprev=x : osuc oprev ≡ x 

record IsOrdinals {n : Level} (ord : Set n)  (o∅ : ord ) (osuc : ord → ord )  (_o<_ : ord → ord → Set n) (next : ord → ord ) : Set (suc (suc n)) where
   field
     ordtrans : {x y z : ord }  → x o< y → y o< z → x o< z
     trio<    : Trichotomous {n} _≡_  _o<_ 
     ¬x<0     : { x : ord  } → ¬ ( x o< o∅  )
     <-osuc   : { x : ord  } → x o< osuc x
     osuc-≡<  : { a x : ord  } → x o< osuc a  →  (x ≡ a ) ∨ (x o< a)  
     Oprev-p  : ( x : ord  ) → Dec ( Oprev ord osuc x )
     TransFinite : { ψ : ord  → Set (suc n) }
          → ( (x : ord)  → ( (y : ord  ) → y o< x → ψ y ) → ψ x )
          →  ∀ (x : ord)  → ψ x


record IsNext {n : Level } (ord : Set n)  (o∅ : ord ) (osuc : ord → ord )  (_o<_ : ord → ord → Set n) (next : ord → ord ) : Set (suc (suc n)) where
   field
     x<nx :    { y : ord } → (y o< next y )
     osuc<nx : { x y : ord } → x o< next y → osuc x o< next y 
     ¬nx<nx :  {x y : ord} → y o< x → x o< next y →  ¬ ((z : ord) → ¬ (x ≡ osuc z)) 

record Ordinals {n : Level} : Set (suc (suc n)) where
   field
     Ordinal : Set n
     o∅ : Ordinal
     osuc : Ordinal → Ordinal
     _o<_ : Ordinal → Ordinal → Set n
     next :  Ordinal → Ordinal
     isOrdinal : IsOrdinals Ordinal o∅ osuc _o<_ next
     isNext : IsNext Ordinal o∅ osuc _o<_ next

module inOrdinal  {n : Level} (O : Ordinals {n} ) where

  open Ordinals  O
  open IsOrdinals isOrdinal
  open IsNext isNext

  TransFinite0 : { ψ : Ordinal  → Set n }
          → ( (x : Ordinal)  → ( (y : Ordinal  ) → y o< x → ψ y ) → ψ x )
          →  ∀ (x : Ordinal)  → ψ x
  TransFinite0 {ψ} ind x = lower (TransFinite {λ y → Lift (suc n) ( ψ y)} ind1 x) where
       ind1 : (z : Ordinal) → ((y : Ordinal) → y o< z → Lift (suc n) (ψ y)) → Lift (suc n) (ψ z)
       ind1 z prev = lift (ind z (λ y y<z → lower (prev y y<z ) )) 

