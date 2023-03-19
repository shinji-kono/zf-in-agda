open import Level
open import Ordinals
module BAlgebra {n : Level } (O : Ordinals {n})   where

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

L＼L=0 : { L  : HOD  } → L ＼ L ≡ od∅ 
L＼L=0 {L} = ==→o≡ ( record { eq→ = lem0 ; eq← =  lem1 } ) where
    lem0 : {x : Ordinal} → odef (L ＼ L) x → odef od∅ x
    lem0 {x} ⟪ lx , ¬lx ⟫ = ⊥-elim (¬lx lx)
    lem1 : {x : Ordinal} → odef  od∅ x → odef (L ＼ L) x
    lem1 {x} lt = ⊥-elim ( ¬∅∋ (subst (λ k → odef od∅ k) (sym &iso) lt ))

L＼Lx=x : { L x : HOD  } → x ⊆ L   → L ＼ ( L ＼ x ) ≡ x
L＼Lx=x {L} {x} x⊆L = ==→o≡ ( record { eq→ = lem03 ; eq← = lem04 } ) where
    lem03 :  {z : Ordinal} → odef (L ＼ (L ＼ x)) z → odef x z 
    lem03 {z} ⟪ Lz , Lxz ⟫ with ODC.∋-p O x (* z)
    ... | yes y = subst (λ k → odef x k ) &iso y 
    ... | no n = ⊥-elim ( Lxz ⟪ Lz , ( subst (λ k → ¬ odef x k ) &iso n ) ⟫ )
    lem04 :  {z : Ordinal} → odef x z → odef (L ＼ (L ＼ x)) z 
    lem04 {z} xz with ODC.∋-p O L (* z)
    ... | yes y = ⟪ subst (λ k → odef L k ) &iso y  , ( λ p → proj2 p xz )  ⟫
    ... | no  n = ⊥-elim ( n (subst (λ k → odef L k ) (sym &iso) ( x⊆L xz) ))
     
L＼0=L : { L  : HOD  } → L ＼ od∅ ≡ L 
L＼0=L {L} = ==→o≡ ( record { eq→ = lem05 ; eq← = lem06 } ) where
    lem05 : {x : Ordinal} → odef (L ＼ od∅) x → odef L x
    lem05 {x} ⟪ Lx , _ ⟫ = Lx
    lem06 : {x : Ordinal} → odef L x → odef (L ＼ od∅) x
    lem06 {x} Lx = ⟪ Lx , (λ lt → ¬x<0 lt)  ⟫

∨L＼X : { L X : HOD } → {x : Ordinal } → odef L x → odef X x ∨ odef (L ＼ X) x
∨L＼X {L} {X} {x} Lx with ODC.∋-p O X (* x)
... | yes y = case1 ( subst (λ k → odef X k ) &iso y  )
... | no  n = case2 ⟪ Lx , subst (λ k → ¬ odef X k) &iso n ⟫

＼-⊆ : { P A B : HOD } →  A ⊆ P → ( A ⊆ B → ( P ＼ B ) ⊆ ( P ＼ A )) ∧ (( P ＼ B ) ⊆ ( P ＼ A ) → A ⊆ B ) 
＼-⊆ {P} {A} {B} A⊆P = ⟪ ( λ a<b {x} pbx → ⟪ proj1 pbx  , (λ ax → proj2 pbx (a<b ax))   ⟫ )  , lem07 ⟫ where
    lem07 : (P ＼ B) ⊆ (P ＼ A) → A ⊆ B
    lem07 pba {x} ax with ODC.p∨¬p O (odef B x)
    ... | case1 bx = bx
    ... | case2 ¬bx = ⊥-elim ( proj2 ( pba ⟪ A⊆P ax  , ¬bx ⟫ ) ax )

[a-b]∩b=0 : { A B : HOD } → (A ＼ B) ∩ B ≡ od∅
[a-b]∩b=0 {A} {B} = ==→o≡ record { eq← = λ lt → ⊥-elim ( ¬∅∋ (subst (λ k → odef od∅ k) (sym &iso) lt ))
     ; eq→ =  λ {x} lt → ⊥-elim (proj2 (proj1 lt ) (proj2 lt)) }

U-F=∅→F⊆U : {F U : HOD} →  ((x : Ordinal) →  ¬ ( odef F x ∧ ( ¬ odef U x ))) → F ⊆ U
U-F=∅→F⊆U {F} {U} not = gt02  where
    gt02 : { x : Ordinal } → odef F x → odef U x
    gt02 {x} fx with ODC.∋-p O U (* x)
    ... | yes y = subst (λ k → odef U k ) &iso y
    ... | no  n = ⊥-elim ( not x ⟪ fx , subst (λ k → ¬ odef U k ) &iso n ⟫ )

∪-Union : { A B : HOD } → Union (A , B) ≡ ( A ∪ B )
∪-Union {A} {B} = ==→o≡ ( record { eq→ =  lemma1 ; eq← = lemma2 } )  where
    lemma1 :  {x : Ordinal} → odef (Union (A , B)) x → odef (A ∪ B) x
    lemma1 {x} record { owner = owner ; ao = abo ; ox = ox } with pair=∨ (subst₂ (λ j k → odef (j , k ) owner) (sym *iso) (sym *iso) abo )
    ... | case1 a=o = case1 (subst (λ k → odef k x ) ( begin 
         * owner ≡⟨ cong (*) (sym a=o)  ⟩ 
         * (& A) ≡⟨ *iso ⟩ 
         A ∎ ) ox ) where open ≡-Reasoning
    ... | case2 b=o = case2 (subst (λ k → odef k x ) (trans (cong (*) (sym b=o)) *iso ) ox)
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
       
