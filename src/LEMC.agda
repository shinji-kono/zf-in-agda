open import Level
open import Ordinals
open import logic
open import Relation.Nullary
module LEMC {n : Level } (O : Ordinals {n} ) (p∨¬p : ( p : Set n) → p ∨ ( ¬ p )) where

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
import OrdUtil
import ODUtil
open Ordinals.Ordinals  O
open Ordinals.IsOrdinals isOrdinal
open Ordinals.IsNext isNext
open OrdUtil O
open ODUtil O

open import zfc

open HOD

decp : ( p : Set n ) → Dec p   -- assuming axiom of choice    
decp  p with p∨¬p p
decp  p | case1 x = yes x
decp  p | case2 x = no x

∋-p : (A x : HOD ) → Dec ( A ∋ x ) 
∋-p A x with p∨¬p ( A ∋ x)  -- LEM
∋-p A x | case1 t  = yes t
∋-p A x | case2 t  = no (λ x → t x)

double-neg-eilm : {A : Set n} → ¬ ¬ A → A      -- we don't have this in intutionistic logic
double-neg-eilm  {A} notnot with decp  A                         -- assuming axiom of choice
... | yes p = p
... | no ¬p = ⊥-elim ( notnot ¬p )

power→⊆ :  ( A t : HOD) → Power A ∋ t → t ⊆ A
power→⊆ A t  PA∋t t∋x = subst (λ k → odef A k ) &iso ( t1 (subst (λ k → odef t k ) (sym &iso) t∋x))  where
   t1 : {x : HOD }  → t ∋ x → A ∋ x
   t1 = power→ A t PA∋t

--- With assuption of HOD is ordered,  p ∨ ( ¬ p ) <=> axiom of choice
---
record choiced  ( X : Ordinal ) : Set n where
  field
     a-choice : Ordinal
     is-in : odef (* X) a-choice

open choiced

-- ∋→d : ( a : HOD  ) { x : HOD } → * (& a) ∋ x → X ∋ * (a-choice (choice-func X not))
-- ∋→d a lt = subst₂ (λ j k → odef j k) *iso (sym &iso) lt

oo∋ : { a : HOD} {  x : Ordinal } → odef (* (& a)) x → a ∋ * x
oo∋ lt = subst₂ (λ j k → odef j k) *iso (sym &iso) lt

∋oo : { a : HOD} {  x : Ordinal } → a ∋ * x → odef (* (& a)) x 
∋oo lt = subst₂ (λ j k → odef j k ) (sym *iso) &iso lt 

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
                 lemma-ord  ox = TransFinite0 {ψ} induction ox where
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
                 odef→o<  {X} {x} lt = o<-subst  {_} {_} {x} {& X} ( c<→o< ( subst₂ (λ j k → odef j k )  (sym *iso) (sym &iso)  lt )) &iso &iso
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
                 lemma : {y : Ordinal} → OD.def (od x) y ∧ OD.def (od u) y → y o< omin (odmax x) (odmax u)
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



         
