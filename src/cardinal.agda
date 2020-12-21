open import Level
open import Ordinals
module cardinal {n : Level } (O : Ordinals {n}) where

open import zf
open import logic
import OD 
import ODC
import OPair
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
open OPair O
open ODAxiom odAxiom

import OrdUtil
import ODUtil
open Ordinals.Ordinals  O
open Ordinals.IsOrdinals isOrdinal
open Ordinals.IsNext isNext
open OrdUtil O
open ODUtil O


open _∧_
open _∨_
open Bool
open _==_

open HOD

-- _⊗_ : (A B : HOD) → HOD
-- A ⊗ B  = Union ( Replace B (λ b → Replace A (λ a → < a , b > ) ))

Func :  OD
Func = record { def = λ x → def ZFProduct x
    ∧ ( (a b c : Ordinal) → odef (* x) (& < * a , * b >) ∧ odef (* x) (& < * a , * c >) →  b ≡  c ) }  

FuncP :  ( A B : HOD ) → HOD
FuncP A B = record { od = record { def = λ x → odef (ZFP A B) x
    ∧ ( (x : Ordinal ) (p q : odef (ZFP A B ) x ) → pi1 (proj1 p) ≡ pi1 (proj1 q) → pi2 (proj1 p) ≡ pi2 (proj1 q) ) } 
       ; odmax = odmax (ZFP A B) ; <odmax = λ lt → <odmax (ZFP A B) (proj1 lt) }

record Injection (A B : Ordinal ) : Set n where
   field
       i→  : (x : Ordinal ) → odef (* A)  x → Ordinal
       iB  : (x : Ordinal ) → ( lt : odef (* A)  x ) → odef (* B) ( i→ x lt )
       iiso : (x y : Ordinal ) → ( ltx : odef (* A)  x ) ( lty : odef (* A)  y ) → i→ x ltx ≡ i→ y lty → x ≡ y  

record Bijection (A B : Ordinal ) : Set n where
   field
       fun←  : (x : Ordinal ) → odef (* A)  x → Ordinal
       fun→  : (x : Ordinal ) → odef (* B)  x → Ordinal
       funB  : (x : Ordinal ) → ( lt : odef (* A)  x ) → odef (* B) ( fun← x lt )
       funA  : (x : Ordinal ) → ( lt : odef (* B)  x ) → odef (* A) ( fun→ x lt )
       fiso← : (x : Ordinal ) → ( lt : odef (* B)  x ) → fun← ( fun→ x lt ) ( funA x lt ) ≡ x
       fiso→ : (x : Ordinal ) → ( lt : odef (* A)  x ) → fun→ ( fun← x lt ) ( funB x lt ) ≡ x
       
Bernstein : {a b : Ordinal } → Injection a b → Injection b a → Bijection a b
Bernstein = {!!}

_=c=_ : ( A B : HOD ) → Set n
A =c= B = Bijection ( & A ) ( & B )

_c<_ : ( A B : HOD ) → Set n
A c< B = ¬ ( Injection (& A)  (& B) )

Card : OD
Card = record { def = λ x → (a : Ordinal) → a o< x → ¬ Bijection a x }

record Cardinal (a : Ordinal ) : Set (suc n) where
   field
       card : Ordinal
       ciso : Bijection a card
       cmax : (x : Ordinal) → card o< x → ¬ Bijection a x

Cardinal∈ : { s : HOD } → { t : Ordinal } → Ord t ∋ s →   s c< Ord t 
Cardinal∈ = {!!}

Cardinal⊆ : { s t : HOD } → s ⊆ t →  ( s c< t ) ∨ ( s =c= t )
Cardinal⊆ = {!!}

Cantor1 : { u : HOD } → u c< Power u
Cantor1 = {!!}

Cantor2 : { u : HOD } → ¬ ( u =c=  Power u )
Cantor2 = {!!}
