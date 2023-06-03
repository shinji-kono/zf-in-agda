{-# OPTIONS --allow-unsolved-metas #-}

open import Level
open import Ordinals
module cardinal {n : Level } (O : Ordinals {n}) where

open import logic
-- import OD
import OD hiding ( _⊆_ )

import ODC
open import Data.Nat renaming ( zero to Zero ; suc to Suc ;  ℕ to Nat ; _⊔_ to _n⊔_ )
open import Relation.Binary.PropositionalEquality
open import Data.Nat.Properties
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.Core

open inOrdinal O
open OD O
open OD.OD
open ODAxiom odAxiom
open import ZProduct O

import OrdUtil
import ODUtil
open Ordinals.Ordinals  O
open Ordinals.IsOrdinals isOrdinal
open Ordinals.IsNext isNext
open OrdUtil O
open ODUtil O

_⊆_ : ( A B : HOD ) → Set n
_⊆_ A B = {x : Ordinal } → odef A x → odef B x


open _∧_
open _∨_
open Bool
open _==_

open HOD

record OrdBijection (A B : Ordinal ) : Set n where
   field
       fun←  : (x : Ordinal ) → odef (* A)  x → Ordinal
       fun→  : (x : Ordinal ) → odef (* B)  x → Ordinal
       funB  : (x : Ordinal ) → ( lt : odef (* A)  x ) → odef (* B) ( fun← x lt )
       funA  : (x : Ordinal ) → ( lt : odef (* B)  x ) → odef (* A) ( fun→ x lt )
       fiso← : (x : Ordinal ) → ( lt : odef (* B)  x ) → fun← ( fun→ x lt ) ( funA x lt ) ≡ x
       fiso→ : (x : Ordinal ) → ( lt : odef (* A)  x ) → fun→ ( fun← x lt ) ( funB x lt ) ≡ x

ordbij-refl : { a b : Ordinal } → a ≡ b → OrdBijection a b
ordbij-refl {a} refl = record {
       fun←  = λ x _ → x 
     ; fun→  = λ x _ → x 
     ; funB  = λ x lt → lt
     ; funA  = λ x lt → lt
     ; fiso← = λ x lt → refl
     ; fiso→ = λ x lt → refl
    }

open Injection
open OrdBijection

record IsImage (a b : Ordinal) (iab : Injection a b ) (x : Ordinal ) : Set n where
   field
      ax : odef (* a) x
      bx : odef (* b) (i→ iab _ ax)

Image : { a b : Ordinal } → Injection a b → HOD
Image {a} {b} iab = record { od = record { def = λ x → IsImage a b iab x } ; odmax = a ; <odmax = λ lt → ?  }

image=a : ?
image=a = ?

_=c=_ : ( A B : HOD ) → Set n
A =c= B = OrdBijection ( & A ) ( & B )

c=→≡ : {A B : HOD} → A =c= B → (A ≡ ?) ∧ (B ≡ ?)
c=→≡ = ?

≡→c= : {A B : HOD} → A ≡ B → A =c= B
≡→c= = ?

open import BAlgebra O

_-_ : (a b : Ordinal ) → Ordinal 
a - b = & ( (* a) ＼ (* b) )

-→<  : (a b : Ordinal ) → (a - b) o≤ a
-→< a b = ?

Bernstein1 : {a b : Ordinal } → a o< b → Injection a b ∧  Injection b a → Injection (b - a) b ∧  Injection b (b - a) 
Bernstein1 = ?

Bernstein : {a b : Ordinal } → Injection a b → Injection b a → OrdBijection a b
Bernstein {a} {b} iab iba = be00 where
    a⊆b : * a ⊆ * b
    a⊆b {x} ax = subst (λ k → odef (* b) k) be01 ( iB iab _ ax ) where
        be01 : i→ iab x ax ≡ x
        be01 = ?
        be02 : x ≡  i→ iba x ?
        be02 = iiso iab ? ? ax ( iB iba _ ? ) ? 
    b⊆a : * b ⊆ * a
    b⊆a bx = ?
    be05 : {a b : Ordinal } → a o< b → Injection a b → Injection b a → ⊥ 
    be05 {a} {b} a<b iab iba = TransFinite0 {λ x → (b : Ordinal) → x o< b → Injection x b → Injection b x → ⊥  } 
          ind a b a<b iab iba where
       ind :(x : Ordinal) →
            ((y : Ordinal) → y o< x → (b : Ordinal) → y o< b → Injection y b → Injection b y → ⊥ ) →
            (b : Ordinal) → x o< b → Injection x b → Injection b x → ⊥ 
       ind x prev b x<b ixb ibx = ?
    be00 : OrdBijection a b
    be00 with trio< a b
    ... | tri< a ¬b ¬c = ⊥-elim ( be05 a iab iba )
    ... | tri≈ ¬a b ¬c = ordbij-refl b
    ... | tri> ¬a ¬b c = ⊥-elim ( be05 c iba iab )

_c<_ : ( A B : HOD ) → Set n
A c< B = ¬ ( Injection (& A)  (& B) )

Card : OD
Card = record { def = λ x → (a : Ordinal) → a o< x → ¬ OrdBijection a x }

record Cardinal (a : Ordinal ) : Set (suc n) where
   field
       card : Ordinal
       ciso : OrdBijection a card
       cmax : (x : Ordinal) → card o< x → ¬ OrdBijection a x

Cardinal∈ : { s : HOD } → { t : Ordinal } → Ord t ∋ s →   s c< Ord t
Cardinal∈ = {!!}

Cardinal⊆ : { s t : HOD } → s ⊆ t →  ( s c< t ) ∨ ( s =c= t )
Cardinal⊆ = {!!}

Cantor1 : { u : HOD } → u c< Power u
Cantor1 = {!!}

Cantor2 : { u : HOD } → ¬ ( u =c=  Power u )
Cantor2 = {!!}




