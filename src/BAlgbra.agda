open import Level
open import Ordinals
module BAlgbra {n : Level } (O : Ordinals {n})   where

open import zf
open import logic
import OrdUtil
import OD 
import ODUtil
import ODC

open import Relation.Nullary
open import Relation.Binary
open import Data.Empty
open import Relation.Binary
open import Relation.Binary.Core
open import  Relation.Binary.PropositionalEquality
open import Data.Nat renaming ( zero to Zero ; suc to Suc ;  ℕ to Nat ; _⊔_ to _n⊔_ ; _+_ to _n+_ )  

open inOrdinal O
open Ordinals.Ordinals  O
open Ordinals.IsOrdinals isOrdinal
open Ordinals.IsNext isNext
open OrdUtil O
open ODUtil O

open OD O
open OD.OD
open ODAxiom odAxiom
open HOD

open _∧_
open _∨_
open Bool

--_∩_ : ( A B : HOD  ) → HOD
--A ∩ B = record { od = record { def = λ x → odef A x ∧ odef B x } ;
--    odmax = omin (odmax A) (odmax B) ; <odmax = λ y → min1 (<odmax A (proj1 y)) (<odmax B (proj2 y)) }

∩-comm : { A B : HOD } → (A ∩ B) ≡ (B ∩ A)
∩-comm {A} {B} = ==→o≡ record { eq← = λ {x} lt → ⟪ proj2 lt , proj1 lt ⟫ ; eq→ =  λ {x} lt → ⟪ proj2 lt , proj1 lt ⟫ }

_∪_ : ( A B : HOD  ) → HOD
A ∪ B = record { od = record { def = λ x → odef A x ∨ odef B x } ;
    odmax = omax (odmax A) (odmax B) ; <odmax = lemma } where
      lemma :  {y : Ordinal} → odef A y ∨ odef B y → y o< omax (odmax A) (odmax B)
      lemma {y} (case1 a) = ordtrans (<odmax A a) (omax-x _ _)
      lemma {y} (case2 b) = ordtrans (<odmax B b) (omax-y _ _)

_＼_ : ( A B : HOD  ) → HOD
A ＼ B = record { od = record { def = λ x → odef A x ∧ ( ¬ ( odef B x ) ) }; odmax = odmax A ; <odmax = λ y → <odmax A (proj1 y) }

¬∅∋ : {x : HOD} → ¬ ( od∅ ∋ x )
¬∅∋ {x} = ¬x<0

[a-b]∩b=0 : { A B : HOD } → (A ＼ B) ∩ B ≡ od∅
[a-b]∩b=0 {A} {B} = ==→o≡ record { eq← = λ lt → ⊥-elim ( ¬∅∋ (subst (λ k → odef od∅ k) (sym &iso) lt ))
     ; eq→ =  λ {x} lt → ⊥-elim (proj2 (proj1 lt ) (proj2 lt)) }

U-F=∅→F⊆U : {F U : HOD} →  ((x : Ordinal) →  ¬ ( odef F x ∧ ( ¬ odef U x ))) → F ⊆ U
U-F=∅→F⊆U {F} {U} not = record { incl = gt02 } where
    gt02 : { x : Ordinal } → odef F x → odef U x
    gt02 {x} fx with ODC.∋-p O U (* x)
    ... | yes y = subst (λ k → odef U k ) &iso y
    ... | no  n = ⊥-elim ( not x ⟪ fx , subst (λ k → ¬ odef U k ) &iso n ⟫ )

∪-Union : { A B : HOD } → Union (A , B) ≡ ( A ∪ B )
∪-Union {A} {B} = ==→o≡ ( record { eq→ =  lemma1 ; eq← = lemma2 } )  where
    lemma1 :  {x : Ordinal} → odef (Union (A , B)) x → odef (A ∪ B) x
    lemma1 {x} lt = lemma3 lt where
        lemma4 : {y : Ordinal} → odef (A , B) y ∧ odef (* y) x → ¬ (¬ ( odef A x ∨ odef B x) )
        lemma4 {y} z with proj1 z
        lemma4 {y} z | case1 refl = double-neg (case1 ( subst (λ k → odef k x ) *iso (proj2 z)) )
        lemma4 {y} z | case2 refl = double-neg (case2 ( subst (λ k → odef k x ) *iso (proj2 z)) )
        lemma3 : (((u : Ordinal ) → ¬ odef (A , B) u ∧ odef (* u) x) → ⊥) → odef (A ∪ B) x
        lemma3 not = ODC.double-neg-eilm O (FExists _ lemma4 not)   -- choice
    lemma2 :  {x : Ordinal} → odef (A ∪ B) x → odef (Union (A , B)) x
    lemma2 {x} (case1 A∋x) = subst (λ k → odef (Union (A , B)) k) &iso ( IsZF.union→ isZF (A , B) (* x) A
        ⟪ case1 refl , d→∋ A A∋x ⟫ )
    lemma2 {x} (case2 B∋x) = subst (λ k → odef (Union (A , B)) k) &iso ( IsZF.union→ isZF (A , B) (* x) B
        ⟪ case2 refl , d→∋ B B∋x ⟫ )

∩-Select : { A B : HOD } →  Select A (  λ x → ( A ∋ x ) ∧ ( B ∋ x )  ) ≡ ( A ∩ B )
∩-Select {A} {B} = ==→o≡ ( record { eq→ =  lemma1 ; eq← = lemma2 } ) where
    lemma1 : {x : Ordinal} → odef (Select A (λ x₁ → (A ∋ x₁) ∧ (B ∋ x₁))) x → odef (A ∩ B) x
    lemma1 {x} lt = ⟪ proj1 lt , subst (λ k → odef B k ) &iso (proj2 (proj2 lt)) ⟫
    lemma2 : {x : Ordinal} → odef (A ∩ B) x → odef (Select A (λ x₁ → (A ∋ x₁) ∧ (B ∋ x₁))) x
    lemma2 {x} lt = ⟪ proj1 lt , ⟪ d→∋ A (proj1 lt) , d→∋ B (proj2 lt) ⟫ ⟫

dist-ord : {p q r : HOD } → p ∩ ( q ∪ r ) ≡   ( p ∩ q ) ∪ ( p ∩ r )
dist-ord {p} {q} {r} = ==→o≡ ( record { eq→ = lemma1 ; eq← = lemma2 } ) where
    lemma1 :  {x : Ordinal} → odef (p ∩ (q ∪ r)) x → odef ((p ∩ q) ∪ (p ∩ r)) x
    lemma1 {x} lt with proj2 lt
    lemma1 {x} lt | case1 q∋x = case1 ⟪ proj1 lt , q∋x ⟫ 
    lemma1 {x} lt | case2 r∋x = case2 ⟪ proj1 lt , r∋x ⟫ 
    lemma2  : {x : Ordinal} → odef ((p ∩ q) ∪ (p ∩ r)) x → odef (p ∩ (q ∪ r)) x
    lemma2 {x} (case1 p∩q) = ⟪ proj1 p∩q , case1 (proj2 p∩q ) ⟫ 
    lemma2 {x} (case2 p∩r) = ⟪ proj1 p∩r , case2 (proj2 p∩r ) ⟫ 

dist-ord2 : {p q r : HOD } → p ∪ ( q ∩ r ) ≡   ( p ∪ q ) ∩ ( p ∪ r )
dist-ord2 {p} {q} {r} = ==→o≡ ( record { eq→ = lemma1 ; eq← = lemma2 } ) where
    lemma1 : {x : Ordinal} → odef (p ∪ (q ∩ r)) x → odef ((p ∪ q) ∩ (p ∪ r)) x
    lemma1 {x} (case1 cp) = ⟪ case1 cp , case1 cp ⟫
    lemma1 {x} (case2 cqr) = ⟪ case2 (proj1 cqr) , case2 (proj2 cqr) ⟫
    lemma2 : {x : Ordinal} → odef ((p ∪ q) ∩ (p ∪ r)) x → odef (p ∪ (q ∩ r)) x
    lemma2 {x} lt with proj1 lt | proj2 lt
    lemma2 {x} lt | case1 cp | _ = case1 cp
    lemma2 {x} lt | _ | case1 cp = case1 cp 
    lemma2 {x} lt | case2 cq | case2 cr = case2 ⟪ cq , cr ⟫ 

record IsBooleanAlgebra ( L : Set n)
       ( b1 : L )
       ( b0 : L )
       ( -_ : L → L  )
       ( _+_ : L → L → L )
       ( _x_ : L → L → L ) : Set (suc n) where
   field
       +-assoc : {a b c : L } → a + ( b + c ) ≡ (a + b) + c
       x-assoc : {a b c : L } → a x ( b x c ) ≡ (a x b) x c
       +-sym : {a b : L } → a + b ≡ b + a
       -sym : {a b : L } → a x b  ≡ b x a
       +-aab : {a b : L } → a + ( a x b ) ≡ a
       x-aab : {a b : L } → a x ( a + b ) ≡ a
       +-dist : {a b c : L } → a + ( b x c ) ≡ ( a x b ) + ( a x c )
       x-dist : {a b c : L } → a x ( b + c ) ≡ ( a + b ) x ( a + c )
       a+0 : {a : L } → a + b0 ≡ a
       ax1 : {a : L } → a x b1 ≡ a
       a+-a1 : {a : L } → a + ( - a ) ≡ b1
       ax-a0 : {a : L } → a x ( - a ) ≡ b0

record BooleanAlgebra ( L : Set n) : Set (suc n) where
   field
       b1 : L
       b0 : L
       -_ : L → L 
       _+_ : L → L → L
       _x_ : L → L → L
       isBooleanAlgebra : IsBooleanAlgebra L b1 b0 -_ _+_ _x_
       
