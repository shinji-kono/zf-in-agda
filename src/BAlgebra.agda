{-# OPTIONS --allow-unsolved-metas #-}

open import Level
open import Ordinals
module BAlgebra {n : Level } (O : Ordinals {n})   where

-- open import zf
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

RC＼ : {L : HOD} → RCod (Power (Union L)) (λ z → L ＼ z )
RC＼ {L} = record { ≤COD = λ {x} lt z xz → lemm {x} lt z xz  } where
    lemm : {x : HOD} → (L ＼ x) ⊆ Power (Union L )
    lemm {x} ⟪ Ly , nxy ⟫ z xz = record { owner = _ ; ao = Ly ; ox = xz }


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
    lemma2 {x} (case1 A∋x) = subst (λ k → odef (Union (A , B)) k) &iso ( union→ (A , B) (* x) A
        ⟪ case1 refl , d→∋ A A∋x ⟫ )
    lemma2 {x} (case2 B∋x) = subst (λ k → odef (Union (A , B)) k) &iso ( union→ (A , B) (* x) B
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

record IsBooleanAlgebra {n : Level} ( L : Set n)
       ( _==_ : L → L → Set n )
       ( b1 : L )
       ( b0 : L )
       ( -_ : L → L  )
       ( _+_ : L → L → L )
       ( _x_ : L → L → L ) : Set (suc n) where
   field
       +-assoc : {a b c : L } → (a + ( b + c )) == ((a + b) + c)
       x-assoc : {a b c : L } → (a x ( b x c )) == ((a x b) x c)
       +-sym : {a b : L } → (a + b) == (b + a)
       x-sym : {a b : L } → (a x b)  == (b x a)
       +-aab : {a b : L } → (a + ( a x b )) == a
       x-aab : {a b : L } → (a x ( a + b )) == a
       +-dist : {a b c : L } → (a + ( b x c )) == (( a + b ) x ( a + c ))
       x-dist : {a b c : L } → (a x ( b + c )) == (( a x b ) + ( a x c ))
       a+0 : {a : L } → (a + b0) == a
       ax1 : {a : L } → (a x b1) == a
       a+-a1 : {a : L } → (a + ( - a )) == b1
       ax-a0 : {a : L } → (a x ( - a )) == b0

record BooleanAlgebra {n : Level} ( L : Set n) : Set (suc n) where
   field
       _=b=_ : L → L → Set n 
       b1 : L
       b0 : L
       -_ : L → L 
       _+_ : L → L → L
       _x_ : L → L → L
       isBooleanAlgebra : IsBooleanAlgebra L _=b=_ b1 b0 -_ _+_ _x_

record PowerP (P : HOD) : Set (suc n) where
    constructor ⟦_,_⟧
    field
       hod : HOD
       x⊆P : hod ⊆ P  

open PowerP

HODBA : (P : HOD) → BooleanAlgebra (PowerP P)
HODBA P = record { _=b=_ = λ x y → hod x ≡ hod y ; b1 = ⟦ P , (λ x → x) ⟧   ; b0 = ⟦ od∅ , (λ x →  ⊥-elim (¬x<0 x)) ⟧ 
  ; -_ = λ x → ⟦  P ＼ hod x , proj1 ⟧
  ; _+_ = λ x y → ⟦ hod x ∪ hod y , ba00 x y ⟧ ; _x_ = λ x y → ⟦ hod x ∩ hod y , (λ lt → x⊆P x (proj1 lt))  ⟧ 
   ; isBooleanAlgebra = record {
       +-assoc = λ {a} {b} {c} → ==→o≡ record { eq→ = ba01 a b c ; eq← = ba02 a b c  }
     ; x-assoc = λ {a} {b} {c} → ==→o≡ 
        record { eq→ = λ lt → ⟪ ⟪ proj1 lt  , proj1 (proj2 lt) ⟫ , proj2 (proj2 lt)  ⟫ 
               ; eq← = λ lt → ⟪ proj1 (proj1 lt) , ⟪ proj2 (proj1 lt)  , proj2 lt ⟫ ⟫ } 
     ; +-sym = λ {a} {b} → ==→o≡ record { eq→ = λ {x} lt → ba05 {hod a} {hod b} lt  ; eq← = ba05 {hod b} {hod a} }
     ; x-sym = λ {a} {b} → ==→o≡ record { eq→ = λ lt → ⟪ proj2 lt , proj1 lt ⟫ ; eq← = λ lt → ⟪ proj2 lt , proj1 lt ⟫  }
     ; +-aab = λ {a} {b} → ==→o≡ record { eq→ = ba03 a b ; eq← = case1  }
     ; x-aab = λ {a} {b} → ==→o≡ record { eq→ = proj1 ; eq← = λ ax →  ⟪ ax , case1 ax ⟫ }
     ; +-dist = dist-ord2
     ; x-dist = dist-ord
     ; a+0 = λ {a} → ==→o≡ record { eq→ = ba04 (hod a) ; eq← = case1 }
     ; ax1 = λ {a} → ==→o≡ record { eq→ = proj1 ; eq← = λ ax → ⟪ ax , x⊆P a ax ⟫ }
     ; a+-a1 = λ {a} → ==→o≡ record { eq→ = ba06 a ; eq← = ba07 a }
     ; ax-a0 =  λ {a} → ==→o≡ record { eq→ = ba08 a ; eq← = λ lt → ⊥-elim (¬x<0 lt) }
       } } where
     ba00 : (x y : PowerP P ) →  (hod x ∪ hod y) ⊆ P
     ba00 x y (case1 px) = x⊆P x px
     ba00 x y (case2 py) = x⊆P y py
     ba01 : (a b c : PowerP P) → {x : Ordinal} → odef (hod a) x ∨ odef (hod b ∪ hod c) x →
            odef (hod a ∪ hod b) x ∨ odef (hod c) x
     ba01 a b c {x} (case1 ax) = case1 (case1 ax)
     ba01 a b c {x} (case2 (case1 bx)) = case1 (case2 bx)
     ba01 a b c {x} (case2 (case2 cx)) = case2 cx
     ba02 : (a b c : PowerP P) → {x : Ordinal} → odef (hod a ∪ hod b) x ∨ odef (hod c) x
         → odef (hod a) x ∨ odef (hod b ∪ hod c) x 
     ba02 a b c {x} (case1 (case1 ax)) = case1 ax
     ba02 a b c {x} (case1 (case2 bx)) = case2 (case1 bx)
     ba02 a b c {x} (case2 cx) = case2 (case2 cx)
     ba03 : (a b : PowerP P) → {x : Ordinal} →
            odef (hod a) x ∨ odef (hod a ∩ hod b) x → OD.def (od (hod a)) x
     ba03 a b (case1 ax) = ax
     ba03 a b (case2 ab) = proj1 ab
     ba04 : (a : HOD) →  {x : Ordinal} → odef a x ∨ odef od∅ x → odef a x
     ba04 a (case1 ax) = ax
     ba04 a (case2 x) = ⊥-elim (¬x<0 x)
     ba05 : {a b : HOD} {x : Ordinal} →  odef a x ∨ odef b x → odef b x ∨ odef a x
     ba05 (case1 x) = case2 x
     ba05 (case2 x) = case1 x
     ba06 : (a : PowerP P ) → { x : Ordinal} → odef (hod a) x ∨ odef (P ＼ hod a) x → OD.def (od P) x
     ba06 a {x} (case1 ax) = x⊆P a ax
     ba06 a {x} (case2 nax) = proj1 nax
     ba07 : (a : PowerP P ) → { x : Ordinal} → OD.def (od P) x → odef (hod a) x ∨ odef (P ＼ hod a) x 
     ba07 a {x} px with ODC.∋-p O (hod a) (* x)
     ... | yes y = case1 (subst (λ k → odef (hod a) k) &iso y)
     ... | no n = case2 ⟪ px , subst (λ k → ¬ odef (hod a) k) &iso n ⟫
     ba08 : (a : PowerP P) → {x : Ordinal} → OD.def (od (hod a ∩ (P ＼ hod a))) x → OD.def (od od∅) x
     ba08 a {x} ⟪ ax , ⟪ px , nax ⟫ ⟫ = ⊥-elim ( nax ax )

