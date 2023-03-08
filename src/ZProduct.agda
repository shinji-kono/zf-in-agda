{-# OPTIONS --allow-unsolved-metas #-}

open import Level
open import Ordinals
module ZProduct {n : Level } (O : Ordinals {n})   where

open import zf
open import logic
import OD 
import ODUtil
import OrdUtil

open import Relation.Nullary
open import Relation.Binary
open import Data.Empty
open import Relation.Binary
open import Relation.Binary.Core
open import  Relation.Binary.PropositionalEquality
open import Data.Nat renaming ( zero to Zero ; suc to Suc ;  ℕ to Nat ; _⊔_ to _n⊔_ ) 

open OD O
open OD.OD
open OD.HOD
open ODAxiom odAxiom

open Ordinals.Ordinals  O
open Ordinals.IsOrdinals isOrdinal
open Ordinals.IsNext isNext
open OrdUtil O
open ODUtil O

open _∧_
open _∨_
open Bool

open _==_

<_,_> : (x y : HOD) → HOD
< x , y > = (x , x ) , (x , y )

exg-pair : { x y : HOD } → (x , y ) =h= ( y , x )
exg-pair {x} {y} = record { eq→ = left ; eq← = right } where
    left : {z : Ordinal} → odef (x , y) z → odef (y , x) z 
    left (case1 t) = case2 t
    left (case2 t) = case1 t
    right : {z : Ordinal} → odef (y , x) z → odef (x , y) z 
    right (case1 t) = case2 t
    right (case2 t) = case1 t

ord≡→≡ : { x y : HOD } → & x ≡ & y → x ≡ y
ord≡→≡ eq = subst₂ (λ j k → j ≡ k ) *iso *iso ( cong ( λ k → * k ) eq )

od≡→≡ : { x y : Ordinal } → * x ≡ * y → x ≡ y
od≡→≡ eq = subst₂ (λ j k → j ≡ k ) &iso &iso ( cong ( λ k → & k ) eq )

eq-prod : { x x' y y' : HOD } → x ≡ x' → y ≡ y' → < x , y > ≡ < x' , y' >
eq-prod refl refl = refl

xx=zy→x=y : {x y z : HOD } → ( x , x ) =h= ( z , y ) → x ≡ y
xx=zy→x=y {x} {y} eq with trio< (& x) (& y) 
xx=zy→x=y {x} {y} eq | tri< a ¬b ¬c with eq← eq {& y} (case2 refl) 
xx=zy→x=y {x} {y} eq | tri< a ¬b ¬c | case1 s = ⊥-elim ( o<¬≡ (sym s) a )
xx=zy→x=y {x} {y} eq | tri< a ¬b ¬c | case2 s = ⊥-elim ( o<¬≡ (sym s) a )
xx=zy→x=y {x} {y} eq | tri≈ ¬a b ¬c = ord≡→≡ b
xx=zy→x=y {x} {y} eq | tri> ¬a ¬b c  with eq← eq {& y} (case2 refl) 
xx=zy→x=y {x} {y} eq | tri> ¬a ¬b c | case1 s = ⊥-elim ( o<¬≡ s c )
xx=zy→x=y {x} {y} eq | tri> ¬a ¬b c | case2 s = ⊥-elim ( o<¬≡ s c )

prod-eq : { x x' y y' : HOD } → < x , y > =h= < x' , y' > → (x ≡ x' ) ∧ ( y ≡ y' )
prod-eq {x} {x'} {y} {y'} eq = ⟪ lemmax , lemmay ⟫ where
    lemma2 : {x y z : HOD } → ( x , x ) =h= ( z , y ) → z ≡ y
    lemma2 {x} {y} {z} eq = trans (sym (xx=zy→x=y lemma3 )) ( xx=zy→x=y eq )  where
        lemma3 : ( x , x ) =h= ( y , z )
        lemma3 = ==-trans eq exg-pair
    lemma1 : {x y : HOD } → ( x , x ) =h= ( y , y ) → x ≡ y
    lemma1 {x} {y} eq with eq← eq {& y} (case2 refl)
    lemma1 {x} {y} eq | case1 s = ord≡→≡ (sym s)
    lemma1 {x} {y} eq | case2 s = ord≡→≡ (sym s)
    lemma4 : {x y z : HOD } → ( x , y ) =h= ( x , z ) → y ≡ z
    lemma4 {x} {y} {z} eq with eq← eq {& z} (case2 refl)
    lemma4 {x} {y} {z} eq | case1 s with ord≡→≡ s -- x ≡ z
    ... | refl with lemma2 (==-sym eq )
    ... | refl = refl
    lemma4 {x} {y} {z} eq | case2 s = ord≡→≡ (sym s) -- y ≡ z
    lemmax : x ≡ x'
    lemmax with eq→ eq {& (x , x)} (case1 refl) 
    lemmax | case1 s = lemma1 (ord→== s )  -- (x,x)≡(x',x')
    lemmax | case2 s with lemma2 (ord→== s ) -- (x,x)≡(x',y') with x'≡y'
    ... | refl = lemma1 (ord→== s )
    lemmay : y ≡ y'
    lemmay with lemmax
    ... | refl with lemma4 eq -- with (x,y)≡(x,y')
    ... | eq1 = lemma4 (ord→== (cong (λ  k → & k )  eq1 ))

prod-≡ : { x x' y y' : HOD } → < x , y > ≡ < x' , y' > → (x ≡ x' ) ∧ ( y ≡ y' )
prod-≡ eq = prod-eq (ord→== (cong (&) eq ))

--
-- unlike ordered pair, ZFPair is not a HOD

data ord-pair : (p : Ordinal) → Set n where
   pair : (x y : Ordinal ) → ord-pair ( & ( < * x , * y > ) )

ZFPair : OD
ZFPair = record { def = λ x → ord-pair x }

-- open import Relation.Binary.HeterogeneousEquality as HE using (_≅_ ) 
-- eq-pair : { x x' y y' : Ordinal } → x ≡ x' → y ≡ y' → pair x y ≅ pair x' y'
-- eq-pair refl refl = HE.refl

pi1 : { p : Ordinal } →   ord-pair p →  Ordinal
pi1 ( pair x y) = x

π1 : { p : HOD } → def ZFPair (& p) → HOD
π1 lt = * (pi1 lt )

pi2 : { p : Ordinal } →   ord-pair p →  Ordinal
pi2 ( pair x y ) = y

π2 : { p : HOD } → def ZFPair (& p) → HOD
π2 lt = * (pi2 lt )

op-cons :  ( ox oy  : Ordinal ) → def ZFPair (& ( < * ox , * oy >   ))
op-cons ox oy = pair ox oy

def-subst :  {Z : OD } {X : Ordinal  }{z : OD } {x : Ordinal  }→ def Z X → Z ≡ z  →  X ≡ x  →  def z x
def-subst df refl refl = df

p-cons :  ( x y  : HOD ) → def ZFPair (& ( < x , y >))
p-cons x y = def-subst {_} {_} {ZFPair} {& (< x , y >)} (pair (& x) ( & y )) refl (
   let open ≡-Reasoning in begin
       & < * (& x) , * (& y) >
   ≡⟨ cong₂ (λ j k → & < j , k >) *iso *iso ⟩
       & < x , y >
   ∎ ) 

op-iso :  { op : Ordinal } → (q : ord-pair op ) → & < * (pi1 q) , * (pi2 q) > ≡ op
op-iso (pair ox oy) = refl

p-iso :  { x  : HOD } → (p : def ZFPair (&  x) ) → < π1 p , π2 p > ≡ x
p-iso {x} p = ord≡→≡ (op-iso p) 

p-pi1 :  { x y : HOD } → (p : def ZFPair (&  < x , y >) ) →  π1 p ≡ x
p-pi1 {x} {y} p = proj1 ( prod-eq ( ord→== (op-iso p) ))

p-pi2 :  { x y : HOD } → (p : def ZFPair (&  < x , y >) ) →  π2 p ≡ y
p-pi2 {x} {y} p = proj2 ( prod-eq ( ord→== (op-iso p)))

_⊗_ : (A B : HOD) → HOD
A ⊗ B  = Union ( Replace B (λ b → Replace A (λ a → < a , b > ) ))

product→ : {A B a b : HOD} → A ∋ a → B ∋ b  → ( A ⊗ B ) ∋ < a , b >
product→ {A} {B} {a} {b} A∋a B∋b = record { owner = _ ; ao = lemma1 ; ox = subst (λ k → odef k _) (sym *iso) lemma2  } where
    lemma1 :  odef (Replace B (λ b₁ → Replace A (λ a₁ → < a₁ , b₁ >))) (& (Replace A (λ a₁ → < a₁ , b >)))
    lemma1 = replacement← B b B∋b
    lemma2 : odef (Replace A (λ a₁ → < a₁ , b >)) (& < a , b >)
    lemma2 = replacement← A a A∋a

data ZFProduct  (A B : HOD) : (p : Ordinal) → Set n where
    ab-pair : {a b : Ordinal } → odef A a → odef B b → ZFProduct A B ( & ( < * a , * b > ) )

ZFP  : (A B : HOD) → HOD
ZFP  A B = record { od = record { def = λ x → ZFProduct A B x  } 
        ; odmax = odmax ( A ⊗ B ) ; <odmax = λ {y} px → <odmax ( A ⊗ B ) (lemma0 px) }  
   where
        lemma0 :  {A B : HOD} {x : Ordinal} → ZFProduct A B x → odef (A ⊗ B) x
        lemma0 {A} {B} {px} ( ab-pair {a} {b} ax by ) = product→ (d→∋ A ax) (d→∋ B by)

ZFP→ : {A B a b : HOD} → A ∋ a → B ∋ b  → ZFP A B ∋ < a , b >
ZFP→ {A} {B} {a} {b} aa bb = subst (λ k → ZFProduct A B k ) (cong₂ (λ j k → & < j , k >) *iso *iso ) ( ab-pair aa bb ) 

zπ1 : {A B : HOD} → {x : Ordinal } → odef (ZFP A B) x → Ordinal
zπ1 {A} {B} {.(& < * _ , * _ >)} (ab-pair {a} {b} aa bb) = a

zp1 : {A B : HOD} → {x : Ordinal } → (zx : odef (ZFP A B) x) → odef A (zπ1 zx)
zp1 {A} {B} {.(& < * _ , * _ >)} (ab-pair {a} {b} aa bb ) = aa

zπ2 : {A B : HOD} → {x : Ordinal } → odef (ZFP A B) x → Ordinal
zπ2 (ab-pair {a} {b} aa bb) = b

zp2 : {A B : HOD} → {x : Ordinal } → (zx : odef (ZFP A B) x) → odef B (zπ2 zx)
zp2 {A} {B} {.(& < * _ , * _ >)} (ab-pair {a} {b} aa bb ) = bb

zp-iso :  { A B : HOD } → {x : Ordinal } → (p : odef (ZFP A B) x ) → & < * (zπ1 p) , * (zπ2 p) > ≡ x
zp-iso {A} {B} {_} (ab-pair {a} {b} aa bb)  = refl

zp-iso1 :  { A B : HOD } → {a b : Ordinal } → (p : odef (ZFP A B) (& < * a , * b > )) → (* (zπ1 p) ≡ (* a)) ∧ (* (zπ2 p) ≡ (* b))
zp-iso1 {A} {B} {a} {b} pab = prod-≡ (subst₂ (λ j k → j ≡ k ) *iso *iso (cong (*) zz11) ) where
      zz11 : & < * (zπ1 pab) , * (zπ2 pab) > ≡ & < * a , * b >
      zz11 = zp-iso pab

zp-iso0 :  { A B : HOD } → {a b : Ordinal } → (p : odef (ZFP A B) (& < * a , * b > )) → (zπ1 p ≡ a) ∧ (zπ2 p ≡ b)
zp-iso0 {A} {B} {a} {b} pab = ⟪ subst₂ (λ j k → j ≡ k ) &iso &iso (cong (&) (proj1 (zp-iso1 pab) ))  
                              , subst₂ (λ j k → j ≡ k ) &iso &iso (cong (&) (proj2 (zp-iso1 pab) ) )  ⟫

ZFP⊆⊗ :  {A B : HOD} {x : Ordinal} → odef (ZFP A B) x → odef (A ⊗ B) x
ZFP⊆⊗ {A} {B} {px} ( ab-pair {a} {b} ax by ) = product→ (d→∋ A ax) (d→∋ B by)

⊗⊆ZFPair : {A B x : HOD} → ( A ⊗ B ) ∋ x → def ZFPair (& x)
⊗⊆ZFPair {A} {B} {x} record { owner = owner ; ao = record { z = a ; az = aa ; x=ψz = x=ψa } ; ox = ox } = zfp01 where
       zfp02 : Replace A (λ z → < z , * a >) ≡ * owner
       zfp02 = subst₂ ( λ j k → j ≡ k ) *iso refl (sym (cong (*) x=ψa ))
       zfp01 : def ZFPair (& x)
       zfp01 with subst (λ k → odef k (& x) ) (sym zfp02) ox
       ... | record { z = b ; az = ab ; x=ψz = x=ψb } = subst (λ  k → def ZFPair  k) (cong (&) zfp00) (op-cons b a )  where
           zfp00 : < * b , * a > ≡ x
           zfp00 = sym ( subst₂ (λ j k → j ≡ k ) *iso *iso (cong (*) x=ψb) )

⊗⊆ZFP : {A B x : HOD} → ( A ⊗ B ) ∋ x → odef (ZFP A B) (& x)
⊗⊆ZFP {A} {B} {x} record { owner = owner ; ao = record { z = a ; az = ba ; x=ψz = x=ψa } ; ox = ox } = zfp01 where
       zfp02 : Replace A (λ z → < z , * a >) ≡ * owner
       zfp02 = subst₂ ( λ j k → j ≡ k ) *iso refl (sym (cong (*) x=ψa ))
       zfp01 : odef (ZFP A B) (& x)
       zfp01 with subst (λ k → odef k (& x) ) (sym zfp02) ox
       ... | record { z = b ; az = ab ; x=ψz = x=ψb } = subst (λ k → ZFProduct A B k ) (sym x=ψb) (ab-pair ab ba) 

ZFPproj1 : {A B X : HOD} → X ⊆ ZFP A B  → HOD
ZFPproj1 {A} {B} {X} X⊆P = Replace' X ( λ x px → * (zπ1 (X⊆P px) )) 

ZFPproj2 : {A B X : HOD} → X ⊆ ZFP A B  → HOD
ZFPproj2 {A} {B} {X} X⊆P = Replace' X ( λ x px → * (zπ2 (X⊆P px) )) 

ZFProj1-iso : {P Q : HOD} {a b x : Ordinal } ( p : ZFProduct P Q x ) → x ≡ & < * a , * b > → zπ1 p ≡ a
ZFProj1-iso {P} {Q} {a} {b} (ab-pair {c} {d} zp zq) eq with prod-≡ (subst₂ (λ j k → j ≡ k) *iso *iso (cong (*) eq))
... | ⟪ a=c , b=d ⟫ = subst₂ (λ j k → j ≡ k) &iso &iso (cong (&) a=c)

ZFProj2-iso : {P Q : HOD} {a b x : Ordinal } ( p : ZFProduct P Q x ) → x ≡ & < * a , * b > → zπ2 p ≡ b
ZFProj2-iso {P} {Q} {a} {b} (ab-pair {c} {d} zp zq) eq with prod-≡ (subst₂ (λ j k → j ≡ k) *iso *iso (cong (*) eq))
... | ⟪ a=c , b=d ⟫ = subst₂ (λ j k → j ≡ k) &iso &iso (cong (&) b=d)

ZFP∩  : {A B C : HOD} → ( ZFP (A ∩ B) C ≡ ZFP A C ∩ ZFP B C ) ∧ ( ZFP C (A ∩ B) ≡ ZFP C A  ∩ ZFP C B )
proj1 (ZFP∩ {A} {B} {C} ) = ==→o≡ record { eq→ = zfp00  ; eq← = zfp01 } where
   zfp00 : {x : Ordinal} → ZFProduct (A ∩ B) C x → odef (ZFP A C ∩ ZFP B C) x
   zfp00  (ab-pair ⟪ pa , pb ⟫ qx) = ⟪ ab-pair pa qx  , ab-pair pb qx  ⟫
   zfp01 : {x : Ordinal} → odef (ZFP A C ∩ ZFP B C) x → ZFProduct (A ∩ B) C x
   zfp01 {x} ⟪ p , q ⟫  = subst (λ k → ZFProduct (A ∩ B) C k) zfp07 ( ab-pair (zfp02 ⟪ p , q ⟫ ) (zfp04 q) ) where
       zfp05 : & < * (zπ1 p) , * (zπ2 p) > ≡ x
       zfp05 = zp-iso p
       zfp06 : & < * (zπ1 q) , * (zπ2 q) > ≡ x
       zfp06 = zp-iso q
       zfp07 : & < * (zπ1 p) , * (zπ2 q) > ≡ x
       zfp07 = trans (cong (λ k → & < k , * (zπ2 q)  >  ) 
           (proj1 (prod-≡ (subst₂ _≡_  *iso *iso (cong (*) (trans  zfp05 (sym (zfp06)))))))) zfp06
       zfp02 : {x  : Ordinal  } → (acx : odef (ZFP A C ∩ ZFP B C) x)   → odef (A ∩ B) (zπ1 (proj1 acx))
       zfp02 {.(& < * _ , * _ >)} ⟪ ab-pair {a} {b} ax bx , bcx ⟫ = ⟪ ax , zfp03 bcx refl ⟫ where
           zfp03 : {x : Ordinal } →  (bc : odef (ZFP B C) x) → x ≡ (& < * a , * b >)  → odef B (zπ1 (ab-pair {A} {C} ax bx))
           zfp03 (ab-pair {a1} {b1} x x₁) eq = subst (λ k → odef B k ) zfp08 x  where
              zfp08 : a1 ≡ a
              zfp08 = subst₂ _≡_ &iso &iso (cong (&) (proj1 (prod-≡ (subst₂  _≡_  *iso *iso (cong (*) eq)))))
       zfp04 : {x : Ordinal } (acx : odef (ZFP B C) x )→ odef C (zπ2 acx)
       zfp04 (ab-pair x x₁) = x₁ 
proj2 (ZFP∩ {A} {B} {C} ) = ==→o≡ record { eq→ = zfp00 ; eq← = zfp01  } where
   zfp00 : {x : Ordinal} → ZFProduct C (A ∩ B) x → odef (ZFP C A ∩ ZFP C B) x
   zfp00  (ab-pair qx ⟪ pa , pb ⟫ ) = ⟪ ab-pair qx pa  , ab-pair qx pb   ⟫
   zfp01 : {x : Ordinal} → odef (ZFP C A ∩ ZFP C B ) x → ZFProduct C (A ∩ B)  x
   zfp01 {x} ⟪ p , q ⟫  = subst (λ k → ZFProduct C (A ∩ B)  k) zfp07 ( ab-pair (zfp04 p) (zfp02 ⟪ p , q ⟫ )  ) where
       zfp05 : & < * (zπ1 p) , * (zπ2 p) > ≡ x
       zfp05 = zp-iso p
       zfp06 : & < * (zπ1 q) , * (zπ2 q) > ≡ x
       zfp06 = zp-iso q
       zfp07 : & < * (zπ1 p) , * (zπ2 q) > ≡ x
       zfp07 = trans (cong (λ k → & < * (zπ1 p) , k  >  ) 
           (sym (proj2 (prod-≡ (subst₂ _≡_  *iso *iso (cong (*) (trans  zfp05 (sym (zfp06))))))))) zfp05
       zfp02 : {x  : Ordinal  } → (acx : odef (ZFP C A ∩ ZFP C B ) x)   → odef (A ∩ B) (zπ2 (proj2 acx))
       zfp02 {.(& < * _ , * _ >)} ⟪ bcx , ab-pair {b} {a} ax bx  ⟫ = ⟪ zfp03 bcx refl , bx ⟫ where
           zfp03 : {x : Ordinal } →  (bc : odef (ZFP C A ) x) → x ≡ (& < * b , * a >)  → odef A (zπ2 (ab-pair {C} {B} ax bx ))
           zfp03 (ab-pair {b1} {a1} x x₁) eq = subst (λ k → odef A k ) zfp08 x₁ where
              zfp08 : a1 ≡ a
              zfp08 = subst₂ _≡_ &iso &iso (cong (&) (proj2 (prod-≡ (subst₂  _≡_  *iso *iso (cong (*) eq)))))
       zfp04 : {x : Ordinal } (acx : odef (ZFP C A ) x )→ odef C (zπ1 acx)
       zfp04 (ab-pair x x₁) = x 

open import BAlgebra O

ZFP\Q : {P Q p : HOD} → (( ZFP P Q ＼ ZFP p Q ) ≡ ZFP (P ＼ p) Q ) ∧ (( ZFP P Q ＼ ZFP P p ) ≡ ZFP P (Q ＼ p) )
ZFP\Q {P} {Q} {p} = ⟪ ==→o≡ record { eq→ = ty70 ; eq← = ty71 } , ==→o≡ record { eq→ = ty73 ; eq← = ty75 } ⟫ where
    ty70 : {x : Ordinal } → odef ( ZFP P Q ＼ ZFP p Q ) x →  odef (ZFP (P ＼ p) Q) x
    ty70 ⟪ ab-pair {a} {b} Pa pb  , npq ⟫ = ab-pair ty72 pb  where
       ty72 : odef (P ＼ p ) a
       ty72 = ⟪ Pa , (λ pa → npq (ab-pair pa pb ) ) ⟫
    ty71 : {x : Ordinal } → odef (ZFP (P ＼ p) Q) x → odef ( ZFP P Q ＼ ZFP p Q ) x 
    ty71 (ab-pair {a} {b} ⟪ Pa , npa ⟫ Qb) = ⟪ ab-pair Pa Qb 
        , (λ pab → npa (subst (λ k → odef p k) (proj1 (zp-iso0 pab)) (zp1 pab)) ) ⟫ 
    ty73 : {x : Ordinal } → odef ( ZFP P Q ＼ ZFP P p ) x →  odef (ZFP P (Q ＼ p) ) x
    ty73 ⟪ ab-pair {a} {b} pa Qb  , npq ⟫ = ab-pair pa ty72  where
       ty72 : odef (Q ＼ p ) b
       ty72 = ⟪ Qb , (λ qb → npq (ab-pair pa qb ) ) ⟫
    ty75 : {x : Ordinal } → odef (ZFP P (Q ＼ p) ) x → odef ( ZFP P Q ＼ ZFP P p ) x 
    ty75 (ab-pair {a} {b} Pa ⟪ Qb , nqb ⟫ ) = ⟪ ab-pair Pa Qb 
        , (λ pab → nqb (subst (λ k → odef p k) (proj2 (zp-iso0 pab)) (zp2 pab)) ) ⟫ 





