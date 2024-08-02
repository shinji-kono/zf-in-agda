{-# OPTIONS --cubical-compatible --safe #-}

open import Level
module Ordinals where

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

record IsOrdinals {n : Level} (ord : Set n)  (o∅ : ord ) (osuc : ord → ord )  (_o<_ : ord → ord → Set n)  : Set (suc (suc n)) where
   field
     ordtrans : {x y z : ord }  → x o< y → y o< z → x o< z
     trio<    : Trichotomous {n} _≡_  _o<_ 
     ¬x<0     : { x : ord  } → ¬ ( x o< o∅  )
     <-osuc   : { x : ord  } → x o< osuc x
     osuc-≡<  : { a x : ord  } → x o< osuc a  →  (x ≡ a ) ∨ (x o< a)  
     Oprev-p  : ( x : ord  ) → Dec0 ( Oprev ord osuc x )
     o<-irr   : { x y : ord } → { lt lt1 : x o< y } → lt ≡ lt1
     TransFinite : { ψ : ord  → Set (suc n) }
          → ( (x : ord)  → ( (y : ord  ) → y o< x → ψ y ) → ψ x )
          →  ∀ (x : ord)  → ψ x

record Ordinals {n : Level} : Set (suc (suc n)) where
   field
     Ordinal : Set n
     o∅ : Ordinal
     osuc : Ordinal → Ordinal
     _o<_ : Ordinal → Ordinal → Set n
     isOrdinal : IsOrdinals Ordinal o∅ osuc _o<_ 

module inOrdinal  {n : Level} (O : Ordinals {n} ) where

  open Ordinals  O
  open IsOrdinals isOrdinal

  TransFinite0 : { ψ : Ordinal  → Set n }
          → ( (x : Ordinal)  → ( (y : Ordinal  ) → y o< x → ψ y ) → ψ x )
          →  ∀ (x : Ordinal)  → ψ x
  TransFinite0 {ψ} ind x = lower (TransFinite {λ y → Lift (suc n) ( ψ y)} ind1 x) where
       ind1 : (z : Ordinal) → ((y : Ordinal) → y o< z → Lift (suc n) (ψ y)) → Lift (suc n) (ψ z)
       ind1 z prev = lift (ind z (λ y y<z → lower (prev y y<z ) )) 

