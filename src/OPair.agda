{-# OPTIONS --allow-unsolved-metas #-}

open import Level
open import Ordinals
module OPair {n : Level } (O : Ordinals {n})   where

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

x<nextA : {A x : HOD} → A ∋ x →  & x o< next (odmax A)
x<nextA {A} {x} A∋x = ordtrans (c<→o< {x} {A} A∋x) ho<

A<Bnext : {A B x : HOD} → & A o< & B → A ∋ x → & x o< next (odmax B)
A<Bnext {A} {B} {x} lt A∋x = osucprev (begin
          osuc (& x)  
       <⟨ osucc (c<→o< A∋x) ⟩
          osuc (& A)
       <⟨ osucc lt ⟩
          osuc (& B)
       <⟨ osuc<nx ho<  ⟩
          next (odmax B)
       ∎ ) where open o≤-Reasoning O

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

-- simple version 

record ZProj1 (L : HOD) (x : Ordinal) : Set n where 
    field
        pq : Ordinal
        opq : ord-pair pq
        Lpq : odef L pq    
        x=pi1 : x ≡ pi1 opq

-- LP' = Replace' L ( λ p lp → ZFPproj1 {P} {Q} {p} (λ {x} px → (LPQ lp _ (subst (λ k → odef k x) (sym *iso) px  ) )))           

Proj1 : (L P Q : HOD) → HOD
Proj1 L P Q = record { od = record { def = λ x → odef P x ∧ ZProj1 L x } ; odmax = & P ; <odmax = odef∧< }
   
record ZProj2 (L : HOD) (x : Ordinal) : Set n where 
    field
        pq : Ordinal
        opq : ord-pair pq
        Lpq : odef L pq    
        x=pi2 : x ≡ pi2 opq

Proj2 : (L P Q : HOD) → HOD
Proj2 L P Q = record { od = record { def = λ x → odef Q x ∧ ZProj2 L x } ; odmax = & Q ; <odmax = odef∧< }
   
