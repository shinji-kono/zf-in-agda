{-# OPTIONS --cubical-compatible --safe #-}
open import Level
open import Ordinals
import HODBase
import OD
open import Relation.Nullary
open import logic
module BAlgebra {n : Level } (O : Ordinals {n} ) (HODAxiom : HODBase.ODAxiom O)  (ho< : OD.ODAxiom-ho< O HODAxiom )
   (L : HODBase.HOD O) (∋-p : (P : HODBase.HOD O) → OD._⊆_ O HODAxiom P L → (x : HODBase.HOD O) → Dec0 ( OD._∈_ O HODAxiom x P )) where

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


L＼L=0 :  (L ＼ L) =h= od∅
L＼L=0 = record { eq→ = lem0 ; eq← =  lem1 }  where
    lem0 : {x : Ordinal} → odef (L ＼ L) x → odef od∅ x
    lem0 {x} ⟪ lx , ¬lx ⟫ = ⊥-elim (¬lx lx)
    lem1 : {x : Ordinal} → odef  od∅ x → odef (L ＼ L) x
    lem1 {x} lt = ⊥-elim ( ¬∅∋ (subst (λ k → odef od∅ k) (sym &iso) lt ))

＼-cong : (P R Q S : HOD) → P =h= R → Q =h= S →  (P ＼ Q) =h= (R ＼ S)
eq→ (＼-cong P R Q S p=r q=s) {x} ⟪ px , npq ⟫ = ⟪ eq→ p=r px , (λ lt → npq (eq← q=s lt) ) ⟫
eq← (＼-cong P R Q S p=r q=s ) {x} ⟪ rx , nrs ⟫ = ⟪ eq← p=r rx , (λ lt → nrs (eq→ q=s lt) ) ⟫

L＼Lx=x : {x : HOD} →  x ⊆ L   → (L ＼ ( L ＼ x )) =h= x
L＼Lx=x {x} x⊆L = record { eq→ = lem03 ; eq← = lem04 }  where
    lem03 :  {z : Ordinal} → odef (L ＼ (L ＼ x)) z → odef x z
    lem03 {z} ⟪ Lz , Lxz ⟫ with ∋-p x x⊆L (* z)
    ... | yes0 y = subst (λ k → odef x k ) &iso y
    ... | no0 n = ⊥-elim ( Lxz ⟪ Lz , ( subst (λ k → ¬ odef x k ) &iso n ) ⟫ )
    lem04 :  {z : Ordinal} → odef x z → odef (L ＼ (L ＼ x)) z
    lem04 {z} xz with ∋-p L  (λ x → x) (* z)
    ... | yes0 y = ⟪ subst (λ k → odef L k ) &iso y  , ( λ p → proj2 p xz )  ⟫
    ... | no0  n = ⊥-elim ( n (subst (λ k → odef L k ) (sym &iso) ( x⊆L xz) ))

L＼0=L :  (L ＼ od∅) =h= L
L＼0=L  = record { eq→ = lem05 ; eq← = lem06 }  where
    lem05 : {x : Ordinal} → odef (L ＼ od∅) x → odef L x
    lem05 {x} ⟪ Lx , _ ⟫ = Lx
    lem06 : {x : Ordinal} → odef L x → odef (L ＼ od∅) x
    lem06 {x} Lx = ⟪ Lx , (λ lt → ¬x<0 lt)  ⟫

∨L＼X : { X : HOD } → {x : Ordinal } → odef L x → odef X x ∨ odef (L ＼ X) x
∨L＼X {X} {x} Lx with ∋-p (X ∩ L) (λ lt → proj2 lt ) (* x)
... | yes0 y = case1 ( subst (λ k → odef X k ) &iso (proj1 y)  )
... | no0  n = case2 ⟪ Lx , subst (λ k → ¬ odef X k) &iso (λ lt → ⊥-elim ( n ⟪ lt , subst (λ k → odef L k) (sym &iso) Lx ⟫ ) )  ⟫

L＼lem00 : {x : HOD} →  x ⊆ L   → (L ＼ (* (& x ))) =h= (L ＼ x)
L＼lem00 {x} le = record { eq→ = lem00 ; eq← = lem01 }  where
    lem00 : {z : Ordinal} → odef (L ＼ (* (& x))) z → odef (L ＼ x) z
    lem00 {z} ⟪ Lz , nLx ⟫ = ⟪ Lz , (λ lt → nLx (eq← *iso lt))  ⟫ 
    lem01 : {z : Ordinal} → odef (L ＼ x) z → odef (L ＼ (* (& x))) z
    lem01 {z} ⟪ Lz , nx ⟫ = ⟪ Lz , (λ lt → nx (eq→ *iso lt))  ⟫

＼-⊆ : { A B : HOD } →  A ⊆ L → ( A ⊆ B → ( L ＼ B ) ⊆ ( L ＼ A )) ∧ (( L ＼ B ) ⊆ ( L ＼ A ) → A ⊆ B )
＼-⊆ {A} {B} A⊆L = ⟪ ( λ a<b {x} pbx → ⟪ proj1 pbx  , (λ ax → proj2 pbx (a<b ax))   ⟫ )  , lem07 ⟫ where
    lem07 : (L ＼ B) ⊆ (L ＼ A) → A ⊆ B
    lem07 pba {x} ax with ∋-p (B ∩ L) proj2 (* x)
    ... | yes0 bx = subst (λ k → odef B k ) &iso (proj1 bx)
    ... | no0 ¬bx = ⊥-elim ( proj2 ( pba ⟪ A⊆L ax  , (λ bx → ¬bx ⟪ d→∋ B bx , subst (λ k → odef L k) (sym &iso) ( A⊆L ax)  ⟫) ⟫ ) ax )

＼⊥ : {a : HOD} {z : Ordinal} → odef  (L ＼ a ) z → odef a z → ⊥
＼⊥ {a} {z} naz az = proj2 naz az

RC＼ :  RCod (Power (Union L)) (λ z → L ＼ z )
RC＼ = record { ≤COD = λ {x} lt z xz → lemm {x} lt z xz ; ψ-eq = λ {x} {y} → wdf {x} {y}  } where
    lemm : {x : HOD} → (L ＼ x) ⊆ Power (Union L )
    lemm {x} ⟪ Ly , nxy ⟫ z xz = record { owner = _ ; ao = Ly ; ox = xz }
    wdf : {x y : HOD} → x =h= y → (L ＼ x) =h= (L ＼ y)
    wdf {x} {y} x=y = record { eq→ = λ {p} lxp → ⟪ proj1 lxp , (λ yp → proj2 lxp (eq← x=y yp) ) ⟫
                             ; eq← = λ {p} lxp → ⟪ proj1 lxp , (λ yp → proj2 lxp (eq→ x=y yp) ) ⟫  }


[a-b]∩b=0 : { A B : HOD } → ((A ＼ B) ∩ B) =h= od∅
[a-b]∩b=0 {A} {B} = record { eq← = λ lt → ⊥-elim ( ¬∅∋ (subst (λ k → odef od∅ k) (sym &iso) lt ))
     ; eq→ =  λ {x} lt → ⊥-elim (proj2 (proj1 lt ) (proj2 lt)) }

U-F=∅→F⊆U : {F U : HOD} → U ⊆ L  →  ((x : Ordinal) →  ¬ ( odef F x ∧ ( ¬ odef U x ))) → F ⊆ U
U-F=∅→F⊆U {F} {U} U⊆L not = gt02  where
    gt02 : { x : Ordinal } → odef F x → odef U x
    gt02 {x} fx with ∋-p U  U⊆L (* x)
    ... | yes0 y = subst (λ k → odef U k ) &iso y
    ... | no0  n = ⊥-elim ( not x ⟪ fx , subst (λ k → ¬ odef U k ) &iso n ⟫ )

∪-Union : { A B : HOD } → Union (A , B) =h= ( A ∪ B )
∪-Union {A} {B} = ( record { eq→ =  lemma4 ; eq← = lemma2 } )  where
    lemma4 :  {x : Ordinal} → odef (Union (A , B)) x → odef (A ∪ B) x
    lemma4 {x} record { owner = owner ; ao = (case1 refl) ; ox = ox } = case1 (eq← (==-sym *iso) ox)
    lemma4 {x} record { owner = owner ; ao = (case2 refl) ; ox = ox } = case2 (eq← (==-sym *iso) ox)
    lemma2 :  {x : Ordinal} → odef (A ∪ B) x → odef (Union (A , B)) x
    lemma2 {x} (case1 A∋x) = subst (λ k → odef (Union (A , B)) k) &iso ( union→ (A , B) (* x) A
        ⟪ case1 refl , d→∋ A A∋x ⟫ )
    lemma2 {x} (case2 B∋x) = subst (λ k → odef (Union (A , B)) k) &iso ( union→ (A , B) (* x) B
        ⟪ case2 refl , d→∋ B B∋x ⟫ )

open import zf

pred-in : (A B : HOD ) → ZPred HOD _∋_ _=h=_ (λ x → (A ∋ x) ∧ (B ∋ x))
pred-in A B = record { ψ-cong = wdf } where
 wdf : (x y : HOD) → x =h= y → ((A ∋ x) ∧ (B ∋ x)) ⇔ ((A ∋ y) ∧ (B ∋ y))
 wdf = λ x y x=y
   → ⟪ (λ p → ⟪ subst (λ k → odef A k) (==→o≡ x=y)       (proj1 p)
              , subst (λ k → odef B k) (==→o≡ x=y)       (proj2 p)  ⟫ )
     , (λ p → ⟪ subst (λ k → odef A k) (sym (==→o≡ x=y)) (proj1 p)
              , subst (λ k → odef B k) (sym (==→o≡ x=y)) (proj2 p)  ⟫ ) ⟫

∩-Select : { A B : HOD } →  Select A (  λ x → ( A ∋ x ) ∧ ( B ∋ x )) (pred-in A B)  =h= ( A ∩ B )
∩-Select {A} {B} =  record { eq→ =  lemma1 ; eq← = lemma2 }  where
    lemma1 : {x : Ordinal} → odef (Select A (λ x₁ → (A ∋ x₁) ∧ (B ∋ x₁)) (pred-in A B) ) x → odef (A ∩ B) x
    lemma1 {x} lt = ⟪ proj1 lt , subst (λ k → odef B k ) &iso (proj2 (proj2 lt)) ⟫
    lemma2 : {x : Ordinal} → odef (A ∩ B) x → odef (Select A (λ x₁ → (A ∋ x₁) ∧ (B ∋ x₁)) (pred-in A B) ) x
    lemma2 {x} lt = ⟪ proj1 lt , ⟪ d→∋ A (proj1 lt) , d→∋ B (proj2 lt) ⟫ ⟫

dist-ord : {p q r : HOD } → (p ∩ ( q ∪ r )) =h=  ( ( p ∩ q ) ∪ ( p ∩ r ))
dist-ord {p} {q} {r} = record { eq→ = lemma1 ; eq← = lemma2 }  where
    lemma1 :  {x : Ordinal} → odef (p ∩ (q ∪ r)) x → odef ((p ∩ q) ∪ (p ∩ r)) x
    lemma1 {x} lt with proj2 lt
    lemma1 {x} lt | case1 q∋x = case1 ⟪ proj1 lt , q∋x ⟫
    lemma1 {x} lt | case2 r∋x = case2 ⟪ proj1 lt , r∋x ⟫
    lemma2  : {x : Ordinal} → odef ((p ∩ q) ∪ (p ∩ r)) x → odef (p ∩ (q ∪ r)) x
    lemma2 {x} (case1 p∩q) = ⟪ proj1 p∩q , case1 (proj2 p∩q ) ⟫
    lemma2 {x} (case2 p∩r) = ⟪ proj1 p∩r , case2 (proj2 p∩r ) ⟫

dist-ord2 : {p q r : HOD } → (p ∪ ( q ∩ r )) =h=  ( ( p ∪ q ) ∩ ( p ∪ r ))
dist-ord2 {p} {q} {r} = record { eq→ = lemma1 ; eq← = lemma2 }  where
    lemma1 : {x : Ordinal} → odef (p ∪ (q ∩ r)) x → odef ((p ∪ q) ∩ (p ∪ r)) x
    lemma1 {x} (case1 cp) = ⟪ case1 cp , case1 cp ⟫
    lemma1 {x} (case2 cqr) = ⟪ case2 (proj1 cqr) , case2 (proj2 cqr) ⟫
    lemma2 : {x : Ordinal} → odef ((p ∪ q) ∩ (p ∪ r)) x → odef (p ∪ (q ∩ r)) x
    lemma2 {x} lt with proj1 lt | proj2 lt
    lemma2 {x} lt | case1 cp | _ = case1 cp
    lemma2 {x} lt | _ | case1 cp = case1 cp
    lemma2 {x} lt | case2 cq | case2 cr = case2 ⟪ cq , cr ⟫

record PowerP (P : HOD) : Set (suc n) where
    constructor ⟦_,_⟧
    field
       hod : HOD
       x⊆P : hod ⊆ P

record UP (P : HOD) (s : PowerP P → Set n) (x : Ordinal) : Set n where
    field
       p : Ordinal
       x⊆P : (* p) ⊆ P
       is-s : s record { hod = * p ; x⊆P = x⊆P }
       p∋x : odef (* p) x
    P∋x : odef P x
    P∋x = x⊆P p∋x
    pp : PowerP P
    pp = record { hod = * p ; x⊆P = x⊆P }

UnionP : (P : HOD) → (s : PowerP P → Set n) → HOD
UnionP  P s = record { od = record { def = λ x → UP P s x } ; odmax = & P ; <odmax = λ {x} up → odef< (UP.P∋x up) }

UnionPW : (P : HOD) → (s : PowerP P → Set n) → PowerP P
UnionPW  P s = ⟦  UnionP P s , (λ lt → UP.P∋x lt) ⟧

open import BoolAlgebra


HODBA : (P : HODBase.HOD O)  (∋-p : (Q : HODBase.HOD O) → OD._⊆_ O HODAxiom  Q P → ( x : HODBase.HOD O ) → Dec0 ( OD._∈_ O HODAxiom x Q ))
     → BooleanAlgebra (PowerP P)
HODBA P ∋-p = record { _≈_ = λ x y → hod x =h= hod y ; b1 = ⟦ P , (λ x → x) ⟧   ; b0 = ⟦ od∅ , (λ x →  ⊥-elim (¬x<0 x)) ⟧
  ; -_ = λ x → ⟦  P ＼ hod x , proj1 ⟧
  ; _+_ = λ x y → ⟦ hod x ∪ hod y , ba00 x y ⟧ ; _x_ = λ x y → ⟦ hod x ∩ hod y , (λ lt → x⊆P x (proj1 lt))  ⟧
   ; isBooleanAlgebra = record {
     isEquivalence = record { refl = ==-refl ; sym = ==-sym ; trans = ==-trans }
     ; +-resp = λ {f} {g} {h} {i} f=g h=i → record { eq→ = λ lt → ba10 {f} {g} {h} {i} f=g h=i lt
         ; eq← = λ lt → ba10 {g} {f} {i} {h} (==-sym f=g) (==-sym h=i) lt }
     ; x-resp =  λ {f} {g} {i} f=g h=i → record { eq→ = λ lt → ⟪ eq→ h=i ( proj1 lt) , eq→ f=g (proj2 lt) ⟫
         ; eq← = λ lt → ⟪ eq← h=i ( proj1 lt) , eq← f=g (proj2 lt) ⟫  }
     ; neg-resp = λ {f} {g}  f=g → record { eq→ = λ lt → ⟪ proj1 lt , ( λ gx → proj2 lt (eq← f=g gx) )  ⟫
         ; eq← = λ lt → ⟪ proj1 lt , ( λ gx → proj2 lt (eq→  f=g gx) )  ⟫   }
     ; +-assoc = λ {a} {b} {c} →  record { eq→ = ba01 a b c ; eq← = ba02 a b c  }
     ; x-assoc = λ {a} {b} {c} →
        record { eq→ = λ lt → ⟪ ⟪ proj1 lt  , proj1 (proj2 lt) ⟫ , proj2 (proj2 lt)  ⟫
               ; eq← = λ lt → ⟪ proj1 (proj1 lt) , ⟪ proj2 (proj1 lt)  , proj2 lt ⟫ ⟫ }
     ; +-sym = λ {a} {b} →  record { eq→ = λ {x} lt → ba05 {hod a} {hod b} lt  ; eq← = ba05 {hod b} {hod a} }
     ; x-sym = λ {a} {b} →  record { eq→ = λ lt → ⟪ proj2 lt , proj1 lt ⟫ ; eq← = λ lt → ⟪ proj2 lt , proj1 lt ⟫  }
     ; +-aab = λ {a} {b} →  record { eq→ = ba03 a b ; eq← = case1  }
     ; x-aab = λ {a} {b} →  record { eq→ = proj1 ; eq← = λ ax →  ⟪ ax , case1 ax ⟫ }
     ; +-dist = λ {p} {q} {r} → dist-ord2 {hod p} {hod q} {hod r}
     ; x-dist = λ {p} {q} {r} → dist-ord {hod p} {hod q} {hod r}
     ; a+0 = λ {a} →  record { eq→ = ba04 (hod a) ; eq← = case1 }
     ; ax1 = λ {a} →  record { eq→ = proj1 ; eq← = λ ax → ⟪ ax , x⊆P a ax ⟫ }
     ; a+-a1 = λ {a} →  record { eq→ = ba06 a ; eq← = ba07 a }
     ; ax-a0 =  λ {a} →  record { eq→ = ba08 a ; eq← = λ lt → ⊥-elim (¬x<0 lt) }
       } } where
     open PowerP
     ba10 :  {f g h i : PowerP P} → (f=g : hod f =h= hod g )
         (h=i : hod h =h= hod i ) → {x : Ordinal} → odef (hod h ∪ hod f) x → odef (hod i ∪ hod g) x
     ba10 {i} {f} {g} f=g h=i {x} (case1 lt) = case1 (eq→ h=i lt)
     ba10 {i} {f} {g} f=g h=i {x} (case2 lt) = case2 (eq→ f=g lt)
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
            odef (hod a) x ∨ odef (hod a ∩ hod b) x → odef (hod a) x
     ba03 a b (case1 ax) = ax
     ba03 a b (case2 ab) = proj1 ab
     ba04 : (a : HOD) →  {x : Ordinal} → odef a x ∨ odef od∅ x → odef a x
     ba04 a (case1 ax) = ax
     ba04 a (case2 x) = ⊥-elim (¬x<0 x)
     ba05 : {a b : HOD} {x : Ordinal} →  odef a x ∨ odef b x → odef b x ∨ odef a x
     ba05 (case1 x) = case2 x
     ba05 (case2 x) = case1 x
     ba06 : (a : PowerP P ) → { x : Ordinal} → odef (hod a) x ∨ odef (P ＼ hod a) x → odef P x
     ba06 a {x} (case1 ax) = x⊆P a ax
     ba06 a {x} (case2 nax) = proj1 nax
     ba07 : (a : PowerP P ) → { x : Ordinal} → odef P x → odef (hod a) x ∨ odef (P ＼ hod a) x
     ba07 a {x} px with ∋-p (hod a) (x⊆P a) (* x)
     ... | yes0 y = case1 (subst (λ k → odef (hod a) k) &iso y)
     ... | no0 n = case2 ⟪ px , subst (λ k → ¬ odef (hod a) k) &iso n ⟫
     ba08 : (a : PowerP P) → {x : Ordinal} → odef (hod a ∩ (P ＼ hod a)) x → odef od∅ x
     ba08 a {x} ⟪ ax , ⟪ px , nax ⟫ ⟫ = ⊥-elim ( nax ax )

HODBA-comp : (P : HODBase.HOD O)  (∋-p : (Q : HODBase.HOD O) → Q ⊆ P → ( x : HODBase.HOD O ) → Dec0 ( OD._∈_ O HODAxiom x Q ))
     → IsCompleteBooleanAlgebra (PowerP P) (HODBA P ∋-p)
HODBA-comp P ∋-p = record { sup = λ s → UnionPW P (BPred.pred s)
     ; is-sup =  λ s x sx →  record { eq→ = λ {z} lt → proj1 lt ; eq← = λ {z} lt → ⟪ lt  , record { p = & (PowerP.hod x)
       ; x⊆P = λ {w} zw → PowerP.x⊆P x (eq→ *iso zw)
       ; is-s = lem00 s x sx  ; p∋x = eq← *iso lt  } ⟫ }
     ; is-minsup = lem04
      } where
         open BooleanAlgebra (HODBA P ∋-p) using (_≤_)
         lem00 : ( s : BPred (PowerP P) (HODBA P ∋-p)) → (x : PowerP P) → BPred.pred s x
             → BPred.pred s record { hod = * (& (PowerP.hod x)) ; x⊆P = λ {w} zw → PowerP.x⊆P x (eq→ *iso zw)  }
         lem00 s  x sx = proj1 (BPred.pcong s x record { hod = * (& (PowerP.hod x)) ; x⊆P = λ {w} zw → PowerP.x⊆P x (eq→ *iso zw)  } (==-sym *iso) ) sx
         lem02 : {x y : PowerP P} → x ≤ y → PowerP.hod x ⊆  PowerP.hod y
         lem02 {x} {y} lt {z} xz = proj2 (eq← lt {z} xz )
         lem04 :  (s : BPred (PowerP P) (HODBA P ∋-p)) {x : PowerP P} →
            ((y : PowerP P) → BPred.pred s y → y ≤ x) → (UnionPW P (BPred.pred s)) ≤ x
         lem04 s {x} fs = record { eq→ = λ {y} lt → proj1 lt ; eq← = λ {y} lt → ⟪ lt  , proj2 (eq←  (fs (UP.pp lt) ( UP.is-s lt)) ( UP.p∋x lt)) ⟫ }

--
-- clopen set assumption
--
record HBAR  ( L : HOD ) : Set (suc n) where
   field
       OS    : HOD
       OS⊆PL :  OS ⊆ Power L
       o∩ : { p q : HOD } → OS ∋ p →  OS ∋ q      → OS ∋ (p ∩ q)
       o∪ : { P : HOD }  →  P ⊆ OS                → OS ∋ Union P
       o- : { p : HOD }  →  OS ∋ p                → OS ∋ ( L ＼ p )
   o∪2 : { p q : HOD } → OS ∋ p →  OS ∋ q      → OS ∋ (p ∪ q)
   o∪2 {p} {q} op oq = subst (λ k → odef OS k) (==→o≡ ∪-Union) (o∪ lem00 ) where
      lem00 : {x : Ordinal} → odef (p , q) x → odef OS x
      lem00 {x} (case1 pp) = subst (λ k → odef OS k ) (sym pp) op
      lem00 {x} (case2 qq) = subst (λ k → odef OS k ) (sym qq) oq


open import ZEquiv  O HODAxiom ho<

open HODElement 
open HBAR 

HBA : (L : HODBase.HOD O)  (∋-p : (Q : HODBase.HOD O) → OD._⊆_ O HODAxiom  Q L → ( x : HODBase.HOD O ) → Dec0 ( OD._∈_ O HODAxiom x Q ))
     → (H : HBAR L)
     → BooleanAlgebra {n} {n} (HODElement (HBAR.OS H))
HBA L ∋-p H =  record { _≈_ = λ x y → (* (elt x)) =h= (* (elt y)) ; b1 = record { elt = & L ;  A∋elt =  ba02  } 
      ; b0 = record { elt =  o∅  ;  A∋elt =  ba00 }
  ; -_ = λ x → record { elt = & ( L ＼ (* (elt x))) ; A∋elt =  o- H (subst (λ k → odef (OS H) k ) (sym &iso) (A∋elt x) ) } 
  ; _+_ = λ x y → record { elt = & ( ( * (elt x)) ∪ (* (elt y))) 
       ; A∋elt = o∪2 H (subst (λ k → odef (OS H) k ) (sym &iso) (A∋elt x)) (subst (λ k → odef (OS H) k ) (sym &iso) (A∋elt y)) } 
  ; _x_ = λ x y → record { elt = & ( ( * (elt x)) ∩ (* (elt y))) 
       ; A∋elt =  o∩ H (subst (λ k → odef (OS H) k ) (sym &iso) (A∋elt x)) (subst (λ k → odef (OS H) k ) (sym &iso) (A∋elt y)) } 
   ; isBooleanAlgebra = record {
     isEquivalence = record { refl = ==-refl ; sym = ==-sym ; trans = ==-trans }
     ; x-resp = λ {f} {g} {h} {i} f=g h=i → ==-trans *iso ( ==-trans (ba08 {* (elt f)} {* (elt g)} {* (elt h)} {* (elt i)} f=g h=i ) (==-sym *iso))
     ; +-resp =  λ {f} {g} {h} {i} f=g h=i → ==-trans *iso (==-trans (ba09 {* (elt f)} {* (elt g)} {* (elt h)} {* (elt i)} f=g h=i) (==-sym *iso))
     ; neg-resp = λ {f} {g}  f=g → record { eq→ = λ lt → eq← *iso ⟪ proj1 ( eq→ *iso lt ) , (λ lt1 → proj2 (eq→ *iso lt) (eq← f=g lt1) ) ⟫
         ; eq← = λ lt → eq← *iso ⟪ proj1 ( eq→ *iso lt ) , (λ lt1 → proj2 (eq→ *iso lt) (eq→  f=g lt1) ) ⟫ }
     ; +-assoc = λ {a} {b} {c} →  record { eq→ = λ lt → eq← *iso (ba05 (eq→ *iso lt ))  ; eq← = λ lt → eq← *iso (ba06 (eq→  *iso lt)) }
     ; x-assoc = λ {a} {b} {c} →
        record { eq→ = λ lt → eq← *iso ⟪ eq← *iso ⟪ proj1 (eq→ *iso lt) , proj1 (eq→ *iso (proj2 (eq→ *iso lt) )) ⟫ , proj2 (eq→ *iso (proj2 (eq→ *iso lt) )) ⟫
               ; eq← = λ lt → eq←  *iso ⟪ proj1 ( eq→ *iso (proj1 (eq→ *iso lt) ))   , eq← *iso ⟪ proj2 (eq→ *iso (proj1 (eq→ *iso lt) ))  , proj2 (eq→ *iso lt)  ⟫  ⟫ }
     ; +-sym = λ {a} {b} →  record { eq→ = λ {x} lt → eq← *iso (ba07 {* (elt a)} {* (elt b)} (eq→ *iso lt) ) ; eq← = λ  lt → eq← *iso (ba07 {* (elt b)} {* (elt a)} (eq→ *iso lt))  }
     ; x-sym = λ {a} {b} →  record { eq→ = λ lt → eq← *iso ⟪ proj2 (eq→  *iso lt) , proj1 (eq→ *iso lt) ⟫  ; eq← = λ lt → eq← *iso ⟪ proj2 (eq→  *iso lt) ,  proj1 (eq→  *iso lt)  ⟫  }
     ; +-aab = λ {a} {b} →  record { eq→ = λ lt → ba10 _ _ (eq→ *iso lt) ; eq← = λ lt → eq← *iso ( case1 lt ) }
     ; x-aab = λ {a} {b} →  record { eq→ = λ lt → proj1 (eq→ *iso lt)  ; eq← = λ ax →  eq← *iso ⟪ ax , eq← *iso (case1 ax)  ⟫  }
     ; +-dist = λ {p} {q} {r} → ba12 {* (elt p)} {* (elt q)} {* (elt r)}
     ; x-dist = λ {p} {q} {r} → ba11 {* (elt p)} {* (elt q)} {* (elt r)}
     ; a+0 = λ {a} →  record { eq→ = λ lt → ba13 {* (elt a)} (eq→ *iso lt) ; eq← = λ lt → eq← *iso (case1 lt)  }
     ; ax1 = λ {a} →  record { eq→ = λ lt → proj1 ( eq→ *iso lt) ; eq← = λ ax → eq← *iso ⟪ ax , eq← *iso (OS⊆PL H (A∋elt a) _ ax)  ⟫  }
     ; a+-a1 = λ {a} →  record { eq→ = λ lt → eq← *iso (ba16 (* (elt a)) (λ {x} → OS⊆PL H (A∋elt a) x) (eq→ *iso lt ) )  
         ; eq← = λ lt → eq← *iso (ba17 (* (elt a)) (λ {x} → OS⊆PL H (A∋elt a) x) (eq→ *iso lt)  )   }
     ; ax-a0 =  λ {a} →  record { eq→ = λ lt → ⊥-elim ( proj2 (eq→   *iso (proj2 ( eq→  *iso lt))) (proj1 ( eq→ *iso lt)) ) 
           ; eq← = λ lt → ⊥-elim ( ¬x<0 ( eq→ o∅==od∅ lt )) }
       } }  where
     ba13 : {a : HOD} {x : Ordinal} → odef (a ∪ (* o∅)) x → odef a x
     ba13 {a} {x} (case1 lt) = lt
     ba13 {a} {x} (case2 lt) = ⊥-elim ( ¬x<0 ( eq→ o∅==od∅ lt ))
     ba04 : {p q p1 q1 : HOD} { x : Ordinal} → odef p x ∨ odef q x → p =h= p1 → q =h= q1 → odef p1 x ∨ odef q1 x 
     ba04 (case1 x) eq1 eq2 = case1 ( eq→  eq1 x )
     ba04 (case2 x) eq1 eq2 = case2 ( eq→  eq2 x )
     ba08 : {f g h i : HOD } → f =h= g → h =h= i →
                     (h ∩ f) =h= (i ∩ g)
     ba08 {f} {g} {h} {i} f=g h=i = record { eq→ = λ lt → ⟪ eq→  h=i (proj1 lt) ,  eq→  f=g (proj2 lt) ⟫
         ; eq← = λ lt → ⟪ eq←  h=i (proj1 lt) ,  eq←  f=g (proj2 lt) ⟫ }
     ba09 : {f g h i : HOD} → f =h= g → h =h= i →
                     (h ∪ f) =h= (i ∪  g)
     ba09 {f} {g} {h} {i} f=g h=i = record { eq→ = λ lt → ba04 {h} {f} {i} {g} lt  h=i f=g 
         ; eq← = λ lt → ba04 {i} {g} {h} {f} lt  (==-sym h=i) (==-sym f=g)  }
     ba07 : {a b : HOD} { x : Ordinal} → odef a x ∨ odef b x → odef b x  ∨ odef a x 
     ba07 (case1 x) = case2 x
     ba07 (case2 x) = case1 x
     ba10 : (a b : HOD) → {x : Ordinal} →
            odef a x ∨ odef (* (& (a ∩ b))) x → odef a x
     ba10 a b (case1 ax) = ax
     ba10 a b (case2 ab) = proj1 (eq→ *iso ab )
     ba05 : {a b c : HOD} { x : Ordinal} → odef a x ∨ odef (* (& (b ∪ c))) x → odef (* (& (a ∪ b))) x  ∨ odef c x 
     ba05 (case1 x) = case1 (eq← *iso (case1 x) )
     ba05 (case2 x) with eq→ *iso x
     ... | case1 x₁ = case1 (eq← *iso (case2 x₁) )
     ... | case2 x₁ = case2 x₁ 
     ba06 : {a b c : HOD} { x : Ordinal} → odef (* (& (a ∪ b))) x ∨ odef c x → odef a x ∨ odef (* (& (b ∪ c))) x 
     ba06 (case1 x) with eq→ *iso x 
     ... | case1 x₁ = case1 x₁
     ... | case2 x₁ = case2 (eq← *iso (case1 x₁) ) 
     ba06 (case2 x) = case2 (eq← *iso (case2 x) ) 
     ba01 : & ( Union od∅ ) ≡ o∅ 
     ba01 = =od∅→≡o∅ record { eq→ = λ {x} lt → ⊥-elim (¬x<0 (Own.ao lt) ) ; eq← = λ {x} lt → ⊥-elim (¬x<0 lt)   }
     ba00 : odef (OS H)  o∅ 
     ba00 = subst ( λ k → odef (OS H) k) ba01 (o∪ H ( λ x →  ⊥-elim (¬x<0 x) ))
     ba03 :  (L ＼ * o∅) =h=  L
     ba03 = record { eq→ = proj1 ; eq← =  λ lt →  ⟪ lt , (λ lt → ⊥-elim (¬x<0 (eq→ o∅==od∅ lt) ) ) ⟫ } 
     ba02 : odef (OS H) (& L) 
     ba02 = subst (λ k → odef (OS H) k ) (==→o≡ ba03) 
         ( o- H (subst (  λ k → odef (OS H) k ) (sym &iso) ba00 ))
     import Relation.Binary.Reasoning.Setoid as EqR
     ba11 : {p q r : HOD} →  (* (& (p ∩ (* (& (q ∪ r)))))) =h= (* (& (* (& (p ∩ q)) ∪ * (& (p ∩ r)))))
     ba11 {p} {q} {r} = begin
        (* (& (p ∩ (* (& (q ∪ r))))))   ≈⟨ *iso ⟩
        p ∩ (* (& (q ∪ r)))   ≈⟨ ba08 {(* (& (q ∪ r)))} {q ∪ r} {p} {p} *iso ==-refl  ⟩
        p ∩ (q ∪ r)   ≈⟨ dist-ord {p} {q} {r} ⟩
        (p ∩ q) ∪ (p ∩ r) ≈⟨ ba09 {(p ∩ r)} {* (& (p ∩ r))} {p ∩ q} {* (& (p ∩ q))} (==-sym *iso)  (==-sym *iso)  ⟩
        * (& (p ∩ q)) ∪ * (& (p ∩ r)) ≈⟨ ==-sym *iso ⟩
        (* (& (* (& (p ∩ q)) ∪ * (& (p ∩ r))))) ∎ where open EqR ==-Setoid
     ba12 : {p q r : HOD} →  (* (& (p ∪ (* (& (q ∩ r)))))) =h= (* (& (* (& (p ∪ q)) ∩ * (& (p ∪ r)))))
     ba12 {p} {q} {r} = begin
        (* (& (p ∪ (* (& (q ∩ r))))))   ≈⟨ *iso ⟩
        p ∪ (* (& (q ∩ r)))   ≈⟨ ba09 {(* (& (q ∩ r)))} {q ∩ r} {p} {p} *iso ==-refl  ⟩
        p ∪ (q ∩ r)   ≈⟨ dist-ord2 {p} {q} {r} ⟩
        (p ∪ q) ∩ (p ∪ r) ≈⟨ ba08 {(p ∪ r)} {* (& (p ∪ r))} {p ∪ q} {* (& (p ∪ q))} (==-sym *iso)  (==-sym *iso)  ⟩
        * (& (p ∪ q)) ∩ * (& (p ∪ r)) ≈⟨ ==-sym *iso ⟩
        (* (& (* (& (p ∪ q)) ∩ * (& (p ∪ r))))) ∎ where open EqR ==-Setoid
     ba16 : (a : HOD ) → a ⊆ L → { x : Ordinal} → odef a x ∨ odef (* (& ((L ＼ a)))) x → odef L x
     ba16 a a⊆L {x} (case1 ax) = a⊆L ax
     ba16 a a⊆L {x} (case2 nax) = proj1 (eq→ *iso nax)
     ba17 : (a : HOD ) → a ⊆ L → { x : Ordinal} → odef L x → odef a x ∨ odef (* ( & (L ＼ a))) x
     ba17 a a⊆L {x} px with ∋-p a a⊆L (* x)
     ... | yes0 y = case1 (subst (λ k → odef a k) &iso y)
     ... | no0 n = case2 (eq← *iso ⟪ px , subst (λ k → ¬ odef a k) &iso n ⟫ )

HBA-⊆ : (L : HOD)  (∋-p : (Q : HODBase.HOD O) → OD._⊆_ O HODAxiom  Q L → ( x : HODBase.HOD O ) → Dec0 ( OD._∈_ O HODAxiom x Q ))
     → (H : HBAR L) → (x y : HODElement (OS H))
     → ( (* (elt x)) ⊆ (* (elt y) )) ⇔ ( BooleanAlgebra._≤_ (HBA L ∋-p H) x  y ) 
HBA-⊆ L ∋-p H x y = record { proj1 = lem00 ; proj2 = lem01 } where
   open BooleanAlgebra (HBA L ∋-p H) 
   open IsBooleanAlgebra (BooleanAlgebra.isBooleanAlgebra (HBA L ∋-p H))
   lem00 : * (HODElement.elt x) ⊆ * (HODElement.elt y) → x ≤ y
   lem00 le = record { eq→ = λ {a} xya → proj1 (eq→ *iso xya) ; eq← = λ {a} ax → eq← *iso ⟪ ax , le ax ⟫ }
   lem01 : x ≤ y → * (HODElement.elt x) ⊆ * (HODElement.elt y)
   lem01 le {a} ax = proj2 (eq→ *iso (eq← le {a} ax))

record HBAUP (L : HOD) (H : HBAR L) (s : HODElement (OS H) → Set n) (x : Ordinal) : Set n where
    field
       op : odef (OS H) x
       is-s : s record { elt = x ; A∋elt = op }
    P∋x : odef (Power L) x
    P∋x = OS⊆PL H op 

UnionHBA : (L : HOD) (H : HBAR L) (s : HODElement (OS H) → Set n) → HOD
UnionHBA  L H s = record { od = record { def = λ x → HBAUP L H s x } ; odmax = & (Power L) ; <odmax = λ {x} up → odef< (HBAUP.P∋x up) }

HBAC : (L : HOD)  (∋-p : (Q : HODBase.HOD O) → OD._⊆_ O HODAxiom  Q L → ( x : HODBase.HOD O ) → Dec0 ( OD._∈_ O HODAxiom x Q ))
     → (H : HBAR L)
     → IsCompleteBooleanAlgebra (HODElement (HBAR.OS H)) (HBA L ∋-p H)
HBAC L ∋-p H = record { sup = λ s → record { elt = & ( Union ( UnionHBA L H (BPred.pred s))) ; A∋elt = o∪ H (lem03 s) } 
     ; is-sup =  λ s x sx →  record { eq→ = λ lt → proj1 ( eq→ *iso lt) 
        ; eq← = λ {z} lt → eq← *iso ⟪ lt , eq← *iso record { owner = _ ; ao = record { op = A∋elt x ; is-s = sx } ; ox = lt }  ⟫  }
     ; is-minsup = lem04
      } where
         open BooleanAlgebra (HBA L ∋-p H) using (_≤_)
         lem03 : (s :  BPred (HODElement (OS H)) (HBA L ∋-p H) ) → UnionHBA L H (BPred.pred s) ⊆ OS H
         lem03 s {x} lt = HBAUP.op lt
         lem02 : {x y : HODElement (HBAR.OS H) } → x ≤ y → * (elt x) ⊆  * (elt y )
         lem02 {x} {y} lt {z} xz = proj2 (eq→ *iso lem09) where
               lem09 :  odef (* (elt ((HBA L ∋-p H BooleanAlgebra.x x) y))) z
               lem09 = eq← lt {z} xz 
         lem04 : (s : BPred (HODElement (OS H)) (HBA L ∋-p H)) {x : HODElement (OS H)} 
            → ((x₁ : HODElement (OS H)) → BPred.pred s x₁ → x₁ ≤ x) 
                → record { elt = & (Union (UnionHBA L H (BPred.pred s))) ; A∋elt = o∪ H (lem03 s)  }  ≤ x
         lem04 s {z} fs = record { eq→ = λ lt → proj1 (eq→ *iso lt) ; eq← = λ {w} lt → eq← *iso ⟪ eq← *iso (eq→ *iso lt) , 
            lem02 {lem07 (eq→ *iso lt) } {z} (lem05 (eq→ *iso lt)) (lem08 (eq→ *iso lt))  ⟫  } where
               lem07 : {w : Ordinal} → odef (Union (UnionHBA L H (BPred.pred s))) w → HODElement (OS H)
               lem07 lt2 = record { elt = Own.owner lt2 ; A∋elt = HBAUP.op (Own.ao lt2) }
               lem08 : {w : Ordinal} → (lt2 : odef (Union (UnionHBA L H (BPred.pred s))) w) → odef (* (elt (lem07 lt2))) w
               lem08 lt2 = Own.ox lt2
               lem05 : {w : Ordinal} → (lt2 : odef (Union (UnionHBA L H (BPred.pred s))) w ) → lem07 lt2 ≤ z
               lem05 {w} lt2 = fs (lem07 lt2) (HBAUP.is-s (Own.ao lt2)) 

