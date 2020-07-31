{-# OPTIONS --allow-unsolved-metas #-}

open import Level
open import Ordinals
module OPair {n : Level } (O : Ordinals {n})   where

open import zf
open import logic
import OD 

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
open OD.HOD
open ODAxiom odAxiom

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

ord≡→≡ : { x y : HOD } → od→ord x ≡ od→ord y → x ≡ y
ord≡→≡ eq = subst₂ (λ j k → j ≡ k ) oiso oiso ( cong ( λ k → ord→od k ) eq )

od≡→≡ : { x y : Ordinal } → ord→od x ≡ ord→od y → x ≡ y
od≡→≡ eq = subst₂ (λ j k → j ≡ k ) diso diso ( cong ( λ k → od→ord k ) eq )

eq-prod : { x x' y y' : HOD } → x ≡ x' → y ≡ y' → < x , y > ≡ < x' , y' >
eq-prod refl refl = refl

xx=zy→x=y : {x y z : HOD } → ( x , x ) =h= ( z , y ) → x ≡ y
xx=zy→x=y {x} {y} eq with trio< (od→ord x) (od→ord y) 
xx=zy→x=y {x} {y} eq | tri< a ¬b ¬c with eq← eq {od→ord y} (case2 refl) 
xx=zy→x=y {x} {y} eq | tri< a ¬b ¬c | case1 s = ⊥-elim ( o<¬≡ (sym s) a )
xx=zy→x=y {x} {y} eq | tri< a ¬b ¬c | case2 s = ⊥-elim ( o<¬≡ (sym s) a )
xx=zy→x=y {x} {y} eq | tri≈ ¬a b ¬c = ord≡→≡ b
xx=zy→x=y {x} {y} eq | tri> ¬a ¬b c  with eq← eq {od→ord y} (case2 refl) 
xx=zy→x=y {x} {y} eq | tri> ¬a ¬b c | case1 s = ⊥-elim ( o<¬≡ s c )
xx=zy→x=y {x} {y} eq | tri> ¬a ¬b c | case2 s = ⊥-elim ( o<¬≡ s c )

prod-eq : { x x' y y' : HOD } → < x , y > =h= < x' , y' > → (x ≡ x' ) ∧ ( y ≡ y' )
prod-eq {x} {x'} {y} {y'} eq = record { proj1 = lemmax ; proj2 = lemmay } where
    lemma2 : {x y z : HOD } → ( x , x ) =h= ( z , y ) → z ≡ y
    lemma2 {x} {y} {z} eq = trans (sym (xx=zy→x=y lemma3 )) ( xx=zy→x=y eq )  where
        lemma3 : ( x , x ) =h= ( y , z )
        lemma3 = ==-trans eq exg-pair
    lemma1 : {x y : HOD } → ( x , x ) =h= ( y , y ) → x ≡ y
    lemma1 {x} {y} eq with eq← eq {od→ord y} (case2 refl)
    lemma1 {x} {y} eq | case1 s = ord≡→≡ (sym s)
    lemma1 {x} {y} eq | case2 s = ord≡→≡ (sym s)
    lemma4 : {x y z : HOD } → ( x , y ) =h= ( x , z ) → y ≡ z
    lemma4 {x} {y} {z} eq with eq← eq {od→ord z} (case2 refl)
    lemma4 {x} {y} {z} eq | case1 s with ord≡→≡ s -- x ≡ z
    ... | refl with lemma2 (==-sym eq )
    ... | refl = refl
    lemma4 {x} {y} {z} eq | case2 s = ord≡→≡ (sym s) -- y ≡ z
    lemmax : x ≡ x'
    lemmax with eq→ eq {od→ord (x , x)} (case1 refl) 
    lemmax | case1 s = lemma1 (ord→== s )  -- (x,x)≡(x',x')
    lemmax | case2 s with lemma2 (ord→== s ) -- (x,x)≡(x',y') with x'≡y'
    ... | refl = lemma1 (ord→== s )
    lemmay : y ≡ y'
    lemmay with lemmax
    ... | refl with lemma4 eq -- with (x,y)≡(x,y')
    ... | eq1 = lemma4 (ord→== (cong (λ  k → od→ord k )  eq1 ))

--
-- unlike ordered pair, ZFProduct is not a HOD

data ord-pair : (p : Ordinal) → Set n where
   pair : (x y : Ordinal ) → ord-pair ( od→ord ( < ord→od x , ord→od y > ) )

ZFProduct : OD
ZFProduct = record { def = λ x → ord-pair x }

-- open import Relation.Binary.HeterogeneousEquality as HE using (_≅_ ) 
-- eq-pair : { x x' y y' : Ordinal } → x ≡ x' → y ≡ y' → pair x y ≅ pair x' y'
-- eq-pair refl refl = HE.refl

pi1 : { p : Ordinal } →   ord-pair p →  Ordinal
pi1 ( pair x y) = x

π1 : { p : HOD } → def ZFProduct (od→ord p) → HOD
π1 lt = ord→od (pi1 lt )

pi2 : { p : Ordinal } →   ord-pair p →  Ordinal
pi2 ( pair x y ) = y

π2 : { p : HOD } → def ZFProduct (od→ord p) → HOD
π2 lt = ord→od (pi2 lt )

op-cons :  { ox oy  : Ordinal } → def ZFProduct (od→ord ( < ord→od ox , ord→od oy >   ))
op-cons {ox} {oy} = pair ox oy

def-subst :  {Z : OD } {X : Ordinal  }{z : OD } {x : Ordinal  }→ def Z X → Z ≡ z  →  X ≡ x  →  def z x
def-subst df refl refl = df

p-cons :  ( x y  : HOD ) → def ZFProduct (od→ord ( < x , y >))
p-cons x y = def-subst {_} {_} {ZFProduct} {od→ord (< x , y >)} (pair (od→ord x) ( od→ord y )) refl (
   let open ≡-Reasoning in begin
       od→ord < ord→od (od→ord x) , ord→od (od→ord y) >
   ≡⟨ cong₂ (λ j k → od→ord < j , k >) oiso oiso ⟩
       od→ord < x , y >
   ∎ ) 

op-iso :  { op : Ordinal } → (q : ord-pair op ) → od→ord < ord→od (pi1 q) , ord→od (pi2 q) > ≡ op
op-iso (pair ox oy) = refl

p-iso :  { x  : HOD } → (p : def ZFProduct (od→ord  x) ) → < π1 p , π2 p > ≡ x
p-iso {x} p = ord≡→≡ (op-iso p) 

p-pi1 :  { x y : HOD } → (p : def ZFProduct (od→ord  < x , y >) ) →  π1 p ≡ x
p-pi1 {x} {y} p = proj1 ( prod-eq ( ord→== (op-iso p) ))

p-pi2 :  { x y : HOD } → (p : def ZFProduct (od→ord  < x , y >) ) →  π2 p ≡ y
p-pi2 {x} {y} p = proj2 ( prod-eq ( ord→== (op-iso p)))

ω-pair :  {x y : HOD} → {m : Ordinal} → od→ord x o< next m → od→ord y o< next m → od→ord (x , y) o< next m
ω-pair lx ly = next< (omax<nx lx ly ) ho<

ω-opair : {x y : HOD} → {m : Ordinal} → od→ord x o< next m → od→ord y o< next m → od→ord < x , y > o< next m
ω-opair {x} {y} {m} lx ly = lemma0 where
    lemma0 : od→ord < x , y > o< next m
    lemma0 = osucprev (begin
         osuc (od→ord < x , y >)
       <⟨ osuc<nx ho< ⟩
         next (omax (od→ord (x , x)) (od→ord (x , y)))
       ≡⟨ cong (λ k → next k) (sym ( omax≤ _ _ pair-xx<xy )) ⟩
         next (osuc (od→ord (x , y)))
       ≡⟨ sym (nexto≡) ⟩
         next (od→ord (x , y))
       ≤⟨ x<ny→≤next (ω-pair lx ly) ⟩
         next m
       ∎ ) where
          open o≤-Reasoning O

_⊗_ : (A B : HOD) → HOD
A ⊗ B  = Union ( Replace B (λ b → Replace A (λ a → < a , b > ) ))

product→ : {A B a b : HOD} → A ∋ a → B ∋ b  → ( A ⊗ B ) ∋ < a , b >
product→ {A} {B} {a} {b} A∋a B∋b = λ t → t (od→ord (Replace A (λ a → < a , b >)))
             record { proj1 = lemma1 ; proj2 = subst (λ k → odef k (od→ord < a , b >)) (sym oiso) lemma2 } where
    lemma1 :  odef (Replace B (λ b₁ → Replace A (λ a₁ → < a₁ , b₁ >))) (od→ord (Replace A (λ a₁ → < a₁ , b >)))
    lemma1 = replacement← B b B∋b
    lemma2 : odef (Replace A (λ a₁ → < a₁ , b >)) (od→ord < a , b >)
    lemma2 = replacement← A a A∋a

x<nextA : {A x : HOD} → A ∋ x →  od→ord x o< next (odmax A)
x<nextA {A} {x} A∋x = ordtrans (c<→o< {x} {A} A∋x) ho<

A<Bnext : {A B x : HOD} → od→ord A o< od→ord B → A ∋ x → od→ord x o< next (odmax B)
A<Bnext {A} {B} {x} lt A∋x = osucprev (begin
          osuc (od→ord x)  
       <⟨ osucc (c<→o< A∋x) ⟩
          osuc (od→ord A)
       <⟨ osucc lt ⟩
          osuc (od→ord B)
       <⟨ osuc<nx ho<  ⟩
          next (odmax B)
       ∎ ) where open o≤-Reasoning O

ZFP  : (A B : HOD) → HOD
ZFP  A B = record { od = record { def = λ x → ord-pair x ∧ ((p : ord-pair x ) → odef A (pi1 p) ∧ odef B (pi2 p) )} ;
        odmax = omax (next (odmax A)) (next (odmax B)) ; <odmax = λ {y} px → lemma y px } 
   where
       lemma : (y : Ordinal) → ( ord-pair y ∧ ((p : ord-pair y) → odef A (pi1 p) ∧ odef B (pi2 p))) → y o< omax (next (odmax A)) (next (odmax B))
       lemma y lt with proj1 lt
       lemma p lt | pair x y with trio< (od→ord A) (od→ord B) 
       lemma p lt | pair x y | tri< a ¬b ¬c = ordtrans (ω-opair (A<Bnext a (subst (λ k → odef A k ) (sym diso)
           (proj1 (proj2 lt (pair x y))))) (lemma1 (proj2 (proj2 lt (pair x y))))) (omax-y _ _ ) where
               lemma1 : odef B y → od→ord (ord→od y) o< next (HOD.odmax B)
               lemma1 lt = x<nextA {B} (d→∋ B lt)
       lemma p lt | pair x y | tri≈ ¬a b ¬c = ordtrans (ω-opair (x<nextA {A} (d→∋ A ((proj1 (proj2 lt (pair x y)))))) lemma2 ) (omax-x _ _ ) where
                lemma2 :  od→ord (ord→od y) o< next (HOD.odmax A)
                lemma2 = ordtrans ( subst (λ k → od→ord (ord→od y) o< k ) (sym b) (c<→o< (d→∋ B ((proj2 (proj2 lt (pair x y))))))) ho<
       lemma p lt | pair x y | tri> ¬a ¬b c = ordtrans (ω-opair  (x<nextA {A} (d→∋ A ((proj1 (proj2 lt (pair x y))))))
           (A<Bnext c (subst (λ k → odef B k ) (sym diso) (proj2 (proj2 lt (pair x y)))))) (omax-x _ _ ) 

ZFP⊆⊗ :  {A B : HOD} {x : Ordinal} → odef (ZFP A B) x → odef (A ⊗ B) x
ZFP⊆⊗ {A} {B} {px} record { proj1 = (pair x y) ; proj2 = p2 } = product→ (d→∋ A (proj1 (p2 (pair x y) ))) (d→∋ B (proj2 (p2 (pair x y) )))

-- axiom of choice required
-- ⊗⊆ZFP : {A B x : HOD} → ( A ⊗ B ) ∋ x → def ZFProduct (od→ord x)
-- ⊗⊆ZFP {A} {B} {x} lt = subst (λ k → ord-pair (od→ord k )) {!!} op-cons

