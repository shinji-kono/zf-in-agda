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

--- With assuption of HOD is ordered,  p ∨ ( ¬ p ) <=> axiom of choice
---
record choiced  ( X : HOD) : Set (suc n) where
  field
     a-choice : HOD
     is-in : X ∋ a-choice

open HOD
_=h=_ : (x y : HOD) → Set n
x =h= y  = od x == od y

open choiced

OD→ZFC : ZFC
OD→ZFC   = record { 
    ZFSet = HOD 
    ; _∋_ = _∋_ 
    ; _≈_ = _=h=_ 
    ; ∅  = od∅
    ; Select = Select
    ; isZFC = isZFC
 } where
    -- infixr  200 _∈_
    -- infixr  230 _∩_ _∪_
    isZFC : IsZFC (HOD )  _∋_  _=h=_ od∅ Select 
    isZFC = record {
       choice-func = λ A {X} not A∋X → a-choice (choice-func X not );
       choice = λ A {X} A∋X not → is-in (choice-func X not)
     } where
         --
         -- the axiom choice from LEM and OD ordering
         --
         choice-func :  (X : HOD ) → ¬ ( X =h= od∅ ) → choiced X
         choice-func  X not = have_to_find where
                 ψ : ( ox : Ordinal ) → Set (suc n)
                 ψ ox = (( x : Ordinal ) → x o< ox  → ( ¬ odef X x )) ∨ choiced X
                 lemma-ord : ( ox : Ordinal  ) → ψ ox
                 lemma-ord  ox = TransFinite1 {ψ} induction ox where
                    ∋-p : (A x : HOD ) → Dec ( A ∋ x ) 
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
                         lemma1 : (y : Ordinal) → (y o< x → odef X y → ⊥) ∨ choiced X
                         lemma1 y with ∋-p X (ord→od y)
                         lemma1 y | yes y<X = case2 ( record { a-choice = ord→od y ; is-in = y<X } )
                         lemma1 y | no ¬y<X = case1 ( λ lt y<X → ¬y<X (subst (λ k → odef X k ) (sym diso) y<X ) )
                         lemma :  ((y : Ordinals.ord O) → (O Ordinals.o< y) x → odef X y → ⊥) ∨ choiced X
                         lemma = ∀-imply-or lemma1
                 have_to_find : choiced X
                 have_to_find = dont-or  (lemma-ord (od→ord X )) ¬¬X∋x where
                     ¬¬X∋x : ¬ ((x : Ordinal) → x o< (od→ord X) → odef X x → ⊥)
                     ¬¬X∋x nn = not record {
                            eq→ = λ {x} lt → ⊥-elim  (nn x (odef→o< lt) lt) 
                          ; eq← = λ {x} lt → ⊥-elim ( ¬x<0 lt )
                        }

         --
         --  axiom regurality from ε-induction (using axiom of choice above)
         --
         --  from https://math.stackexchange.com/questions/2973777/is-it-possible-to-prove-regularity-with-transfinite-induction-only
         --
         record Minimal (x : HOD)  : Set (suc n) where
           field
               min : HOD
               x∋min :   x ∋ min 
               min-empty :  (y : HOD ) → ¬ ( min ∋ y) ∧ (x ∋ y)
         open Minimal
         open _∧_
         induction : {x : HOD} → ({y : HOD} → x ∋ y → (u : HOD ) → (u∋x : u ∋ y) → Minimal u )
              →  (u : HOD ) → (u∋x : u ∋ x) → Minimal u 
         induction {x} prev u u∋x with p∨¬p ((y : HOD) → ¬ (x ∋ y) ∧ (u ∋ y))
         ... | case1 P =
              record { min = x
                ;     x∋min = u∋x
                ;     min-empty = P
              } 
         ... | case2 NP =  min2 where
              p : HOD
              p  = record { od = record { def = λ y1 → odef x  y1 ∧ odef u y1 } ; odmax = omin (odmax x) (odmax u) ; <odmax = lemma } where
                 lemma : {y : Ordinal} → OD.def (od x) y ∧ OD.def (od u) y → y o< omin (odmax x) (odmax u)
                 lemma {y} lt = min1 (<odmax x (proj1 lt)) (<odmax u (proj2 lt))
              np : ¬ (p =h= od∅)
              np p∅ =  NP (λ y p∋y → ∅< {p} {_} p∋y p∅ ) 
              y1choice : choiced p
              y1choice = choice-func p np
              y1 : HOD
              y1 = a-choice y1choice
              y1prop : (x ∋ y1) ∧ (u ∋ y1)
              y1prop = is-in y1choice
              min2 : Minimal u
              min2 = prev (proj1 y1prop) u (proj2 y1prop)
         Min2 : (x : HOD) → (u : HOD ) → (u∋x : u ∋ x) → Minimal u 
         Min2 x u u∋x = (ε-induction1 {λ y →  (u : HOD ) → (u∋x : u ∋ y) → Minimal u  } induction x u u∋x ) 
         cx : {x : HOD} →  ¬ (x =h= od∅ ) → choiced x 
         cx {x} nx = choice-func x nx
         minimal : (x : HOD  ) → ¬ (x =h= od∅ ) → HOD 
         minimal x ne = min (Min2 (a-choice (cx {x} ne) ) x (is-in (cx ne))) 
         x∋minimal : (x : HOD  ) → ( ne : ¬ (x =h= od∅ ) ) → odef x ( od→ord ( minimal x ne ) )
         x∋minimal x ne = x∋min (Min2 (a-choice (cx {x} ne) ) x (is-in (cx ne))) 
         minimal-1 : (x : HOD  ) → ( ne : ¬ (x =h= od∅ ) ) → (y : HOD ) → ¬ ( odef (minimal x ne) (od→ord y)) ∧ (odef x (od→ord  y) )
         minimal-1 x ne y = min-empty (Min2 (a-choice (cx ne) ) x (is-in (cx ne))) y



         
