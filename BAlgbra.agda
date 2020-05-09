open import Level
open import Ordinals
module BAlgbra {n : Level } (O : Ordinals {n})   where

open import zf
open import logic
import OD 
import ODC

open import Relation.Nullary
open import Relation.Binary
open import Data.Empty
open import Relation.Binary
open import Relation.Binary.Core
open import  Relation.Binary.PropositionalEquality
open import Data.Nat renaming ( zero to Zero ; suc to Suc ;  ℕ to Nat ; _⊔_ to _n⊔_ ) 

open inOrdinal O
open OD O
open OD.OD

open _∧_
open _∨_
open Bool

_∩_ : ( A B : OD  ) → OD
A ∩ B = record { def = λ x → def A x ∧ def B x } 

_∪_ : ( A B : OD  ) → OD
A ∪ B = record { def = λ x → def A x ∨ def B x } 

_＼_ : ( A B : OD  ) → OD
A ＼ B = record { def = λ x → def A x ∧ ( ¬ ( def B x ) ) }

∪-Union : { A B : OD } → Union (A , B) ≡ ( A ∪ B )
∪-Union {A} {B} = ==→o≡ ( record { eq→ =  lemma1 ; eq← = lemma2 } )  where
    lemma1 :  {x : Ordinal} → def (Union (A , B)) x → def (A ∪ B) x
    lemma1 {x} lt = lemma3 lt where
        lemma4 : {y : Ordinal} → def (A , B) y ∧ def (ord→od y) x → ¬ (¬ ( def A x ∨ def B x) )
        lemma4 {y} z with proj1 z
        lemma4 {y} z | case1 refl = double-neg (case1 ( subst (λ k → def k x ) oiso (proj2 z)) )
        lemma4 {y} z | case2 refl = double-neg (case2 ( subst (λ k → def k x ) oiso (proj2 z)) )
        lemma3 : (((u : Ordinals.ord O) → ¬ def (A , B) u ∧ def (ord→od u) x) → ⊥) → def (A ∪ B) x
        lemma3 not = ODC.double-neg-eilm O (FExists _ lemma4 not)   -- choice
    lemma2 :  {x : Ordinal} → def (A ∪ B) x → def (Union (A , B)) x
    lemma2 {x} (case1 A∋x) = subst (λ k → def (Union (A , B)) k) diso ( IsZF.union→ isZF (A , B) (ord→od x) A
       (record { proj1 = case1 refl ; proj2 = subst (λ k → def A k) (sym diso) A∋x}))
    lemma2 {x} (case2 B∋x) = subst (λ k → def (Union (A , B)) k) diso ( IsZF.union→ isZF (A , B) (ord→od x) B
       (record { proj1 = case2 refl ; proj2 = subst (λ k → def B k) (sym diso) B∋x}))

∩-Select : { A B : OD } →  Select A (  λ x → ( A ∋ x ) ∧ ( B ∋ x )  ) ≡ ( A ∩ B )
∩-Select {A} {B} = ==→o≡ ( record { eq→ =  lemma1 ; eq← = lemma2 } ) where
    lemma1 : {x : Ordinal} → def (Select A (λ x₁ → (A ∋ x₁) ∧ (B ∋ x₁))) x → def (A ∩ B) x
    lemma1 {x} lt = record { proj1 = proj1 lt ; proj2 = subst (λ k → def B k ) diso (proj2 (proj2 lt)) }
    lemma2 : {x : Ordinal} → def (A ∩ B) x → def (Select A (λ x₁ → (A ∋ x₁) ∧ (B ∋ x₁))) x
    lemma2 {x} lt = record { proj1 = proj1 lt ; proj2 =
        record { proj1 = subst (λ k → def A k) (sym diso) (proj1 lt) ; proj2 = subst (λ k → def B k ) (sym diso) (proj2 lt) } }

dist-ord : {p q r : OD } → p ∩ ( q ∪ r ) ≡   ( p ∩ q ) ∪ ( p ∩ r )
dist-ord {p} {q} {r} = ==→o≡ ( record { eq→ = lemma1 ; eq← = lemma2 } ) where
    lemma1 :  {x : Ordinal} → def (p ∩ (q ∪ r)) x → def ((p ∩ q) ∪ (p ∩ r)) x
    lemma1 {x} lt with proj2 lt
    lemma1 {x} lt | case1 q∋x = case1 ( record { proj1 = proj1 lt ; proj2 = q∋x } )
    lemma1 {x} lt | case2 r∋x = case2 ( record { proj1 = proj1 lt ; proj2 = r∋x } )
    lemma2  : {x : Ordinal} → def ((p ∩ q) ∪ (p ∩ r)) x → def (p ∩ (q ∪ r)) x
    lemma2 {x} (case1 p∩q) = record { proj1 = proj1 p∩q ; proj2 = case1 (proj2 p∩q ) } 
    lemma2 {x} (case2 p∩r) = record { proj1 = proj1 p∩r ; proj2 = case2 (proj2 p∩r ) } 

dist-ord2 : {p q r : OD } → p ∪ ( q ∩ r ) ≡   ( p ∪ q ) ∩ ( p ∪ r )
dist-ord2 {p} {q} {r} = ==→o≡ ( record { eq→ = lemma1 ; eq← = lemma2 } ) where
    lemma1 : {x : Ordinal} → def (p ∪ (q ∩ r)) x → def ((p ∪ q) ∩ (p ∪ r)) x
    lemma1 {x} (case1 cp) = record { proj1 = case1 cp ; proj2 = case1 cp }
    lemma1 {x} (case2 cqr) = record { proj1 = case2 (proj1 cqr) ; proj2 = case2 (proj2 cqr) }
    lemma2 : {x : Ordinal} → def ((p ∪ q) ∩ (p ∪ r)) x → def (p ∪ (q ∩ r)) x
    lemma2 {x} lt with proj1 lt | proj2 lt
    lemma2 {x} lt | case1 cp | _ = case1 cp
    lemma2 {x} lt | _ | case1 cp = case1 cp 
    lemma2 {x} lt | case2 cq | case2 cr = case2 ( record { proj1 = cq ; proj2 = cr } )

record IsBooleanAlgebra ( L : Set n)
       ( b1 : L )
       ( b0 : L )
       ( -_ : L → L  )
       ( _+_ : L → L → L )
       ( _*_ : L → L → L ) : Set (suc n) where
   field
       +-assoc : {a b c : L } → a + ( b + c ) ≡ (a + b) + c
       *-assoc : {a b c : L } → a * ( b * c ) ≡ (a * b) * c
       +-sym : {a b : L } → a + b ≡ b + a
       -sym : {a b : L } → a * b  ≡ b * a
       -aab : {a b : L } → a + ( a * b ) ≡ a
       *-aab : {a b : L } → a * ( a + b ) ≡ a
       -dist : {a b c : L } → a + ( b * c ) ≡ ( a * b ) + ( a * c )
       *-dist : {a b c : L } → a * ( b + c ) ≡ ( a + b ) * ( a + c )
       a+0 : {a : L } → a + b0 ≡ a
       a*1 : {a : L } → a * b1 ≡ a
       a+-a1 : {a : L } → a + ( - a ) ≡ b1
       a*-a0 : {a : L } → a * ( - a ) ≡ b0

record BooleanAlgebra ( L : Set n) : Set (suc n) where
   field
       b1 : L
       b0 : L
       -_ : L → L 
       _++_ : L → L → L
       _**_ : L → L → L
       isBooleanAlgebra : IsBooleanAlgebra L b1 b0 -_ _++_ _**_
       
