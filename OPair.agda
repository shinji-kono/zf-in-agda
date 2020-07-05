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

_=h=_ : (x y : HOD) → Set n
x =h= y  = od x == od y

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

prod-eq : { x x' y y' : HOD } → < x , y > =h= < x' , y' > → (x ≡ x' ) ∧ ( y ≡ y' )
prod-eq {x} {x'} {y} {y'} eq = record { proj1 = lemmax ; proj2 = lemmay } where
    lemma0 : {x y z : HOD } → ( x , x ) =h= ( z , y ) → x ≡ y
    lemma0 {x} {y} eq with trio< (od→ord x) (od→ord y) 
    lemma0 {x} {y} eq | tri< a ¬b ¬c with eq← eq {od→ord y} (case2 refl) 
    lemma0 {x} {y} eq | tri< a ¬b ¬c | case1 s = ⊥-elim ( o<¬≡ (sym s) a )
    lemma0 {x} {y} eq | tri< a ¬b ¬c | case2 s = ⊥-elim ( o<¬≡ (sym s) a )
    lemma0 {x} {y} eq | tri≈ ¬a b ¬c = ord≡→≡ b
    lemma0 {x} {y} eq | tri> ¬a ¬b c  with eq← eq {od→ord y} (case2 refl) 
    lemma0 {x} {y} eq | tri> ¬a ¬b c | case1 s = ⊥-elim ( o<¬≡ s c )
    lemma0 {x} {y} eq | tri> ¬a ¬b c | case2 s = ⊥-elim ( o<¬≡ s c )
    lemma2 : {x y z : HOD } → ( x , x ) =h= ( z , y ) → z ≡ y
    lemma2 {x} {y} {z} eq = trans (sym (lemma0 lemma3 )) ( lemma0 eq )  where
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

