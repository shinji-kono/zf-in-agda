{-# OPTIONS --cubical-compatible --safe #-}
open import Level
open import Ordinals
open import logic
open import Relation.Nullary

open import Level
open import Ordinals
import HODBase
import OD
open import Relation.Nullary
module LEMC {n : Level } (O : Ordinals {n} ) (HODAxiom : HODBase.ODAxiom O)  (ho< : OD.ODAxiom-ho< O HODAxiom )( p∨¬p : ( p : Set n) → p ∨ ( ¬ p ) ) where

open import  Relation.Binary.PropositionalEquality hiding ( [_] )
open import Data.Empty

import OrdUtil

open Ordinals.Ordinals  O
open Ordinals.IsOrdinals isOrdinal
import ODUtil

open import logic
open import nat

open OrdUtil O
open ODUtil O HODAxiom  ho<

open _∧_
open _∨_
open Bool

open  HODBase._==_

open HODBase.ODAxiom HODAxiom  
open OD O HODAxiom

open HODBase.HOD

decp : ( p : Set n ) → Dec p   -- assuming axiom of choice    
decp  p with p∨¬p p
decp  p | case1 x = yes x
decp  p | case2 x = no x

∋-p : (A x : HOD ) → Dec ( A ∋ x ) 
∋-p A x with p∨¬p ( A ∋ x)  -- LEM
∋-p A x | case1 t  = yes t
∋-p A x | case2 t  = no (λ x → t x)

double-neg-elim : {A : Set n} → ¬ ¬ A → A      -- we don't have this in intutionistic logic
double-neg-elim  {A} notnot with decp  A                         -- assuming axiom of choice
... | yes p = p
... | no ¬p = ⊥-elim ( notnot ¬p )

--- With assuption of HOD is ordered,  p ∨ ( ¬ p ) <=> axiom of choice
---
record choiced  ( X : Ordinal ) : Set n where
  field
     a-choice : Ordinal
     is-in : odef (* X) a-choice

open choiced

oo∋ : { a : HOD} {  x : Ordinal } → odef (* (& a)) x → a ∋ * x
oo∋ {a} {x} lt = eq→   *iso (subst (λ k → odef (* (& a)) k ) (sym &iso) lt )

∋oo : { a : HOD} {  x : Ordinal } → a ∋ * x → odef (* (& a)) x 
∋oo {a} {x} lt = eq←   *iso (subst (λ k → odef a k ) &iso lt )

open import zfc

OD→ZFC : ZFC
OD→ZFC   = record { 
    ZFSet = HOD 
    ; _∋_ = _∋_ 
    ; _≈_ = _=h=_ 
    ; ∅  = od∅
    ; isZFC = isZFC
 } where
    -- infixr  200 _∈_
    -- infixr  230 _∩_ _∪_
    isZFC : IsZFC (HOD )  _∋_  _=h=_ od∅ 
    isZFC = record {
       choice-func = λ A {X} not A∋X → * (a-choice (choice-func X not) );
       choice = λ A {X} A∋X not → oo∋ (is-in (choice-func X not))
     } where
         --
         -- the axiom choice from LEM and OD ordering
         --
         choice-func :  (X : HOD ) → ¬ ( X =h= od∅ ) → choiced (& X)
         choice-func  X not = have_to_find where
                 ψ : ( ox : Ordinal ) → Set n
                 ψ ox = (( x : Ordinal ) → x o< ox  → ( ¬ odef X x )) ∨ choiced (& X)
                 lemma-ord : ( ox : Ordinal  ) → ψ ox
                 lemma-ord  ox = inOrdinal.TransFinite0 O {ψ} induction ox where
                    ∀-imply-or :  {A : Ordinal  → Set n } {B : Set n }
                        → ((x : Ordinal ) → A x ∨ B) →  ((x : Ordinal ) → A x) ∨ B
                    ∀-imply-or  {A} {B} ∀AB with p∨¬p ((x : Ordinal ) → A x) -- LEM
                    ∀-imply-or  {A} {B} ∀AB | case1 t = case1 t
                    ∀-imply-or  {A} {B} ∀AB | case2 x  = case2 (lemma (λ not → x not )) where
                         lemma : ¬ ((x : Ordinal ) → A x) →  B
                         lemma not with p∨¬p B
                         lemma not | case1 b = b
                         lemma not | case2 ¬b = ⊥-elim  (not (λ x → dont-orb (∀AB x) ¬b ))
                    induction : (x : Ordinal) → ((y : Ordinal) → y o< x → ψ y) → ψ x
                    induction x prev with ∋-p X ( * x) 
                    ... | yes p = case2 ( record { a-choice = x ; is-in = ∋oo  p } )
                    ... | no ¬p = lemma where
                         lemma1 : (y : Ordinal) → (y o< x → odef X y → ⊥) ∨ choiced (& X)
                         lemma1 y with ∋-p X (* y)
                         lemma1 y | yes y<X = case2 ( record { a-choice = y ; is-in = ∋oo y<X } )
                         lemma1 y | no ¬y<X = case1 ( λ lt y<X → ¬y<X (d→∋ X y<X) )
                         lemma :  ((y : Ordinal) → y o< x → odef X y → ⊥) ∨ choiced (& X)
                         lemma = ∀-imply-or lemma1
                 odef→o< :  {X : HOD } → {x : Ordinal } → odef X x → x o< & X 
                 odef→o<  {X} {x} lt = o<-subst  {_} {_} {x} {& X} ( c<→o< (eq← *iso (subst (λ k → odef X k) (sym &iso) lt ))) &iso &iso
                 have_to_find : choiced (& X)
                 have_to_find = dont-or  (lemma-ord (& X )) ¬¬X∋x where
                     ¬¬X∋x : ¬ ((x : Ordinal) → x o< (& X) → odef X x → ⊥)
                     ¬¬X∋x nn = not record {
                            eq→ = λ {x} lt → ⊥-elim  (nn x (odef→o< lt)  lt) 
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
         induction {x} prev u u∋x with p∨¬p ((y : Ordinal ) → ¬ (odef x y) ∧ (odef u y))
         ... | case1 P =
              record { min = x
                ;     x∋min = u∋x 
                ;     min-empty = λ y → P (& y)
              } 
         ... | case2 NP =  min2 where
              p : HOD
              p  = record { od = record { def = λ y1 → odef x  y1 ∧ odef u y1 } ; odmax = omin (odmax x) (odmax u) ; <odmax = lemma } where
                 lemma : {y : Ordinal} → odef x y ∧ odef u y → y o< omin (odmax x) (odmax u)
                 lemma {y} lt = min1 (<odmax x (proj1 lt)) (<odmax u (proj2 lt))
              np : ¬ (p =h= od∅)
              np p∅ =  NP (λ y p∋y → ∅< {p} {_} (d→∋ p p∋y) p∅ ) 
              y1choice : choiced (& p)
              y1choice = choice-func p np
              y1 : HOD
              y1 = * (a-choice y1choice)
              y1prop : (x ∋ y1) ∧ (u ∋ y1)
              y1prop = oo∋ (is-in y1choice)
              min2 : Minimal u
              min2 = prev (proj1 y1prop) u (proj2 y1prop)
         Min2 : (x : HOD) → (u : HOD ) → (u∋x : u ∋ x) → Minimal u 
         Min2 x u u∋x = (ε-induction {λ y →  (u : HOD ) → (u∋x : u ∋ y) → Minimal u  } induction x u u∋x ) 
         cx : {x : HOD} →  ¬ (x =h= od∅ ) → choiced (& x )
         cx {x} nx = choice-func x nx
         minimal : (x : HOD  ) → ¬ (x =h= od∅ ) → HOD 
         minimal x ne = min (Min2 (* (a-choice (cx {x} ne) )) x ( oo∋ (is-in (cx ne))) )
         x∋minimal : (x : HOD  ) → ( ne : ¬ (x =h= od∅ ) ) → odef x ( & ( minimal x ne ) )
         x∋minimal x ne = x∋min (Min2 (* (a-choice (cx {x} ne) )) x ( oo∋ (is-in (cx ne))) )
         minimal-1 : (x : HOD  ) → ( ne : ¬ (x =h= od∅ ) ) → (y : HOD ) → ¬ ( odef (minimal x ne) (& y)) ∧ (odef x (&  y) )
         minimal-1 x ne y = min-empty (Min2 (* (a-choice (cx ne) )) x ( oo∋ (is-in (cx ne)))) y



         
