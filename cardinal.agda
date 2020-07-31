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

open _∧_
open _∨_
open Bool
open _==_

open HOD

-- _⊗_ : (A B : HOD) → HOD
-- A ⊗ B  = Union ( Replace B (λ b → Replace A (λ a → < a , b > ) ))

Func :  OD
Func = record { def = λ x → def ZFProduct x
    ∧ ( (a b c : Ordinal) → odef (ord→od x) (od→ord < ord→od a , ord→od b >) ∧ odef (ord→od x) (od→ord < ord→od a , ord→od c >) →  b ≡  c ) }  

FuncP :  ( A B : HOD ) → HOD
FuncP A B = record { od = record { def = λ x → odef (ZFP A B) x
    ∧ ( (x : Ordinal ) (p q : odef (ZFP A B ) x ) → pi1 (proj1 p) ≡ pi1 (proj1 q) → pi2 (proj1 p) ≡ pi2 (proj1 q) ) } 
       ; odmax = odmax (ZFP A B) ; <odmax = λ lt → <odmax (ZFP A B) (proj1 lt) }

Func∋f : {A B x : HOD} → ( f : HOD → HOD ) → ( (x : HOD ) → A ∋ x → B ∋ f x )
    → def Func (od→ord  (Replace A (λ x → < x , f x > )))
Func∋f = {!!}

FuncP∋f : {A B x : HOD} → ( f : HOD → HOD ) → ( (x : HOD ) → A ∋ x → B ∋ f x )
    → odef (FuncP A B) (od→ord  (Replace A (λ x → < x , f x > )))
FuncP∋f = {!!}

-- Func→f : {A B f x : HOD} → def Func (od→ord f)  → (x : HOD ) → A ∋ x  → ( HOD ∧ ((y : HOD ) → B ∋ y ))
-- Func→f = {!!}
-- Func₁ : {A B f : HOD} → def Func (od→ord f) → {!!}  
-- Func₁ = {!!}
-- Cod : {A B f : HOD} → def Func (od→ord f) → {!!}
-- Cod = {!!}
-- 1-1 : {A B f : HOD} → def Func (od→ord f) → {!!}
-- 1-1 = {!!}
-- onto : {A B f : HOD} → def Func (od→ord f) → {!!}
-- onto  = {!!}

record Bijection (A B : Ordinal ) : Set n where
   field
       fun→ : Ordinal → Ordinal
       fun← : Ordinal → Ordinal
       fun→inA : (x : Ordinal) → odef (ord→od A) ( fun→ x )
       fun←inB : (x : Ordinal) → odef (ord→od B) ( fun← x )
       fiso→ : (x : Ordinal ) → odef (ord→od B)  x → fun→ ( fun← x ) ≡ x
       fiso← : (x : Ordinal ) → odef (ord→od A)  x → fun← ( fun→ x ) ≡ x
       
Card : OD
Card = record { def = λ x → (a : Ordinal) → a o< x → ¬ Bijection a x }
