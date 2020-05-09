open import Level
open import Ordinals
open import logic
open import Relation.Nullary
module LEMC {n : Level } (O : Ordinals {n} ) (p∨¬p : ( p : Set (suc n)) → p ∨ ( ¬ p )) where

open import zf
open import Data.Nat renaming ( zero to Zero ; suc to Suc ;  ℕ to Nat ; _⊔_ to _n⊔_ ) 
open import  Relation.Binary.PropositionalEquality
open import Data.Nat.Properties 
open import Data.Empty
open import Relation.Binary
open import Relation.Binary.Core

open import nat
import OD

open inOrdinal O
open OD O
open OD.OD
open OD._==_
open ODAxiom odAxiom

open import zfc

--- With assuption of OD is ordered,  p ∨ ( ¬ p ) <=> axiom of choice
---
record choiced  ( X : OD) : Set (suc n) where
  field
     a-choice : OD
     is-in : X ∋ a-choice

open choiced

OD→ZFC : ZFC
OD→ZFC   = record { 
    ZFSet = OD 
    ; _∋_ = _∋_ 
    ; _≈_ = _==_ 
    ; ∅  = od∅
    ; Select = Select
    ; isZFC = isZFC
 } where
    -- infixr  200 _∈_
    -- infixr  230 _∩_ _∪_
    isZFC : IsZFC (OD )  _∋_  _==_ od∅ Select 
    isZFC = record {
       choice-func = λ A {X} not A∋X → a-choice (choice-func X not );
       choice = λ A {X} A∋X not → is-in (choice-func X not)
     } where
         choice-func :  (X : OD ) → ¬ ( X == od∅ ) → choiced X
         choice-func  X not = have_to_find where
                 ψ : ( ox : Ordinal ) → Set (suc n)
                 ψ ox = (( x : Ordinal ) → x o< ox  → ( ¬ def X x )) ∨ choiced X
                 lemma-ord : ( ox : Ordinal  ) → ψ ox
                 lemma-ord  ox = TransFinite {ψ} induction ox where
                    ∋-p : (A x : OD ) → Dec ( A ∋ x ) 
                    ∋-p A x with p∨¬p (Lift (suc n) ( A ∋ x )) -- LEM
                    ∋-p A x | case1 (lift t)  = yes t
                    ∋-p A x | case2 t  = no (λ x → t (lift x ))
                    ∀-imply-or :  {A : Ordinal  → Set n } {B : Set (suc n) }
                        → ((x : Ordinal ) → A x ∨ B) →  ((x : Ordinal ) → A x) ∨ B
                    ∀-imply-or  {A} {B} ∀AB with p∨¬p (Lift ( suc n ) ((x : Ordinal ) → A x)) -- LEM
                    ∀-imply-or  {A} {B} ∀AB | case1 (lift t) = case1 t
                    ∀-imply-or  {A} {B} ∀AB | case2 x  = case2 (lemma (λ not → x (lift not ))) where
                         lemma : ¬ ((x : Ordinal ) → A x) →  B
                         lemma not with p∨¬p B
                         lemma not | case1 b = b
                         lemma not | case2 ¬b = ⊥-elim  (not (λ x → dont-orb (∀AB x) ¬b ))
                    induction : (x : Ordinal) → ((y : Ordinal) → y o< x → ψ y) → ψ x
                    induction x prev with ∋-p X ( ord→od x) 
                    ... | yes p = case2 ( record { a-choice = ord→od x ; is-in = p } )
                    ... | no ¬p = lemma where
                         lemma1 : (y : Ordinal) → (y o< x → def X y → ⊥) ∨ choiced X
                         lemma1 y with ∋-p X (ord→od y)
                         lemma1 y | yes y<X = case2 ( record { a-choice = ord→od y ; is-in = y<X } )
                         lemma1 y | no ¬y<X = case1 ( λ lt y<X → ¬y<X (subst (λ k → def X k ) (sym diso) y<X ) )
                         lemma :  ((y : Ordinals.ord O) → (O Ordinals.o< y) x → def X y → ⊥) ∨ choiced X
                         lemma = ∀-imply-or lemma1
                 have_to_find : choiced X
                 have_to_find = dont-or  (lemma-ord (od→ord X )) ¬¬X∋x where
                     ¬¬X∋x : ¬ ((x : Ordinal) → x o< (od→ord X) → def X x → ⊥)
                     ¬¬X∋x nn = not record {
                            eq→ = λ {x} lt → ⊥-elim  (nn x (def→o< lt) lt) 
                          ; eq← = λ {x} lt → ⊥-elim ( ¬x<0 lt )
                        }
         
