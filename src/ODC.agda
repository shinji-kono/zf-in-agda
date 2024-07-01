{-# OPTIONS --cubical-compatible --safe #-}
open import Level
open import Ordinals
import HODBase
import OD
module ODC {n : Level } (O : Ordinals {n} ) (HODAxiom : HODBase.ODAxiom O) 
       (AC : OD.AxiomOfChoice O HODAxiom )
   where

open import Data.Nat renaming ( zero to Zero ; suc to Suc ;  ℕ to Nat ; _⊔_ to _n⊔_ )
open import  Relation.Binary.PropositionalEquality hiding ( [_] )
open import Data.Nat.Properties
open import Data.Empty
open import Data.Unit
open import Relation.Nullary
open import Relation.Binary  hiding (_⇔_)
open import Relation.Binary.Core hiding (_⇔_)
import Relation.Binary.Reasoning.Setoid as EqR

open import logic
import OrdUtil
open import nat

open Ordinals.Ordinals  O
open Ordinals.IsOrdinals isOrdinal
-- open Ordinals.IsNext isNext
open OrdUtil O

-- Ordinal Definable Set

open HODBase.HOD 
open HODBase.OD 

open _∧_
open _∨_
open Bool

open  HODBase._==_

open HODBase.ODAxiom HODAxiom  
open OD O HODAxiom
open AxiomOfChoice AC

--
-- Axiom of choice in intutionistic logic implies the exclude middle
--     https://plato.stanford.edu/entries/axiom-choice/#AxiChoLog
--

pred-od :  ( p : Set n )  → HOD
pred-od  p  = record { od = record { def = λ x → (x ≡ o∅) ∧ p } ;
   odmax = osuc o∅; <odmax = λ x → subst (λ k →  k o< osuc o∅) (sym (proj1 x)) <-osuc }

ppp :  { p : Set n } { a : HOD  } → pred-od p ∋ a → p
ppp  {p} {a} d = proj2 d

p∨¬p : ( p : Set n ) → p ∨ ( ¬ p )         -- assuming axiom of choice
p∨¬p  p with is-o∅ ( & (pred-od p ))
p∨¬p  p | yes eq = case2 (¬p eq) where
   ps = pred-od p
   eqo∅ : ps =h=  od∅  → & ps ≡  o∅
   eqo∅ eq = trans (==→o≡ eq) ord-od∅
   lemma : ps =h= od∅ → p → ⊥
   lemma eq p0 = ¬x<0  {& ps} (eq→ eq record { proj1 = eqo∅ eq ; proj2 = p0 } )
   ¬p : (& ps ≡ o∅) → p → ⊥
   ¬p eq =  lemma ( begin
      pred-od p  ≈⟨ ==-sym  *iso ⟩
      * ( & ps ) ≡⟨ cong (*) eq ⟩
      * ( o∅ ) ≈⟨ o∅==od∅ ⟩
      od∅ ∎ ) where open EqR ==-Setoid
p∨¬p  p | no ¬p = case1 (ppp  {p} {minimal ps (λ eq →  ¬p (eqo∅ eq))} lemma) where
   ps = pred-od p
   eqo∅ : ps =h=  od∅  → & ps ≡  o∅
   eqo∅ eq = trans (==→o≡ eq) ord-od∅
   lemma : ps ∋ minimal ps (λ eq →  ¬p (eqo∅ eq))
   lemma = x∋minimal ps (λ eq →  ¬p (eqo∅ eq))

decp : ( p : Set n ) → Dec p   -- assuming axiom of choice
decp  p with p∨¬p p
decp  p | case1 x = yes x
decp  p | case2 x = no x

∋-p : (A x : HOD ) → Dec ( A ∋ x )
∋-p A x with p∨¬p ( A ∋ x ) -- LEM
∋-p A x | case1 t  = yes t
∋-p A x | case2 t  = no (λ x → t x)

double-neg-elim : {A : Set n} → ¬ ¬ A → A      -- we don't have this in intutionistic logic
double-neg-elim  {A} notnot with decp  A                         -- assuming axiom of choice
... | yes p = p
... | no ¬p = ⊥-elim ( notnot ¬p )

or-exclude : {A B : Set n} → A ∨ B → A ∨ ( (¬ A)  ∧  B )
or-exclude {A} {B} ab with p∨¬p A
or-exclude {A} {B} (case1 a) | case1 a0 = case1 a
or-exclude {A} {B} (case1 a) | case2 ¬a = ⊥-elim ( ¬a a )
or-exclude {A} {B} (case2 b) | case1 a = case1 a
or-exclude {A} {B} (case2 b) | case2 ¬a = case2 ⟪ ¬a , b ⟫

or-exclude1 : {A B : Set n} →  (¬ A →  B ) → A ∨ B 
or-exclude1 {A} {B} ab with p∨¬p A
... | case1 a = case1 a
... | case2 ¬a = case2 ( ab ¬a)

OrdP : ( x : Ordinal  ) ( y : HOD  ) → Dec ( Ord x ∋ y )
OrdP  x y with trio< x (& y)
OrdP  x y | tri< a ¬b ¬c = no ¬c
OrdP  x y | tri≈ ¬a refl ¬c = no ( o<¬≡ refl )
OrdP  x y | tri> ¬a ¬b c = yes c

open import zfc

HOD→ZFC : ZFC
HOD→ZFC   = record {
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
       choice-func = choice-func ;
       choice = choice
     } where
         -- Axiom of choice ( is equivalent to the existence of minimal in our case )
         -- ∀ X [ ∅ ∉ X → (∃ f : X → ⋃ X ) → ∀ A ∈ X ( f ( A ) ∈ A ) ]
         choice-func : (X : HOD  ) → {x : HOD } → ¬ ( x =h= od∅ ) → ( X ∋ x ) → HOD
         choice-func X {x} not X∋x = minimal x not
         choice : (X : HOD  ) → {A : HOD } → ( X∋A : X ∋ A ) → (not : ¬ ( A =h= od∅ )) → A ∋ choice-func X not X∋A
         choice X {A} X∋A not = x∋minimal A not

