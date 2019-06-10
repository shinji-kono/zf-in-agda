{-# OPTIONS --allow-unsolved-metas #-}
open import Level
module ordinal where

open import zf

open import Data.Nat renaming ( zero to Zero ; suc to Suc ;  ℕ to Nat ; _⊔_ to _n⊔_ ) 
open import Data.Empty
open import  Relation.Binary.PropositionalEquality

data OrdinalD {n : Level} :  (lv : Nat) → Set n where
   Φ : (lv : Nat) → OrdinalD  lv
   OSuc : (lv : Nat) → OrdinalD {n} lv → OrdinalD lv

record Ordinal {n : Level} : Set n where
   field
     lv : Nat
     ord : OrdinalD {n} lv

--
--    Φ (Suc lv) < ℵ lv < OSuc (Suc lv) (ℵ lv) < OSuc ... < OSuc (Suc lv) (Φ (Suc lv)) < OSuc ...  < ℵ (Suc lv)
--
data _d<_ {n : Level} :   {lx ly : Nat} → OrdinalD {n} lx  →  OrdinalD {n} ly  → Set n where
   Φ<  : {lx : Nat} → {x : OrdinalD {n} lx}  →  Φ lx d< OSuc lx x
   s<  : {lx : Nat} → {x y : OrdinalD {n} lx}  →  x d< y  → OSuc  lx x d< OSuc  lx y

open Ordinal

_o<_ : {n : Level} ( x y : Ordinal ) → Set n
_o<_ x y =  (lv x < lv y )  ∨ ( ord x d< ord y )

s<refl : {n : Level } {lx : Nat } { x : OrdinalD {n} lx } → x d< OSuc lx x
s<refl {n} {lv} {Φ lv}  = Φ<
s<refl {n} {lv} {OSuc lv x}  = s< s<refl 

trio<> : {n : Level} →  {lx : Nat} {x  : OrdinalD {n} lx } { y : OrdinalD  lx }  →  y d< x → x d< y → ⊥
trio<>  {n} {lx} {.(OSuc lx _)} {.(OSuc lx _)} (s< s) (s< t) = trio<> s t
trio<> {n} {lx} {.(OSuc lx _)} {.(Φ lx)} Φ< ()

d<→lv : {n : Level} {x y  : Ordinal {n}}   → ord x d< ord y → lv x ≡ lv y
d<→lv Φ< = refl
d<→lv (s< lt) = refl

o<-subst : {n : Level } {Z X z x : Ordinal {n}}  → Z o< X → Z ≡ z  →  X ≡ x  →  z o< x
o<-subst df refl refl = df

open import Data.Nat.Properties 
open import Data.Unit using ( ⊤ )
open import Relation.Nullary

open import Relation.Binary
open import Relation.Binary.Core

o∅ : {n : Level} → Ordinal {n}
o∅  = record { lv = Zero ; ord = Φ Zero }

open import Relation.Binary.HeterogeneousEquality using (_≅_;refl)

ordinal-cong : {n : Level} {x y : Ordinal {n}}  →
      lv x  ≡ lv y → ord x ≅ ord y →  x ≡ y
ordinal-cong refl refl = refl

ordinal-lv : {n : Level} {x y : Ordinal {n}}  → x ≡ y → lv x  ≡ lv y 
ordinal-lv refl = refl

ordinal-d : {n : Level} {x y : Ordinal {n}}  → x ≡ y → ord x  ≅ ord y 
ordinal-d refl = refl

≡→¬d< : {n : Level} →  {lv : Nat} → {x  : OrdinalD {n}  lv }  → x d< x → ⊥
≡→¬d<  {n} {lx} {OSuc lx y} (s< t) = ≡→¬d< t

trio<≡ : {n : Level} →  {lx : Nat} {x  : OrdinalD {n} lx } { y : OrdinalD  lx }  → x ≡ y  → x d< y → ⊥
trio<≡ refl = ≡→¬d<

trio>≡ : {n : Level} →  {lx : Nat} {x  : OrdinalD {n} lx } { y : OrdinalD  lx }  → x ≡ y  → y d< x → ⊥
trio>≡ refl = ≡→¬d<

triO : {n : Level} →  {lx ly : Nat} → OrdinalD {n} lx  →  OrdinalD {n} ly  → Tri (lx < ly) ( lx ≡ ly ) ( lx > ly )
triO  {n} {lx} {ly} x y = <-cmp lx ly

triOrdd : {n : Level} →  {lx : Nat}   → Trichotomous  _≡_ ( _d<_  {n} {lx} {lx} )
triOrdd  {_} {lv} (Φ lv) (Φ lv) = tri≈ ≡→¬d< refl ≡→¬d<
triOrdd  {_} {lv} (Φ lv) (OSuc lv y) = tri< Φ< (λ ()) ( λ lt → trio<> lt Φ< )
triOrdd  {_} {lv} (OSuc lv x) (Φ lv) = tri> (λ lt → trio<> lt Φ<) (λ ()) Φ<
triOrdd  {_} {lv} (OSuc lv x) (OSuc lv y) with triOrdd x y
triOrdd  {_} {lv} (OSuc lv x) (OSuc lv y) | tri< a ¬b ¬c = tri< (s< a) (λ tx=ty → trio<≡ tx=ty (s< a) )  (  λ lt → trio<> lt (s< a) )
triOrdd  {_} {lv} (OSuc lv x) (OSuc lv x) | tri≈ ¬a refl ¬c = tri≈ ≡→¬d< refl ≡→¬d<
triOrdd  {_} {lv} (OSuc lv x) (OSuc lv y) | tri> ¬a ¬b c = tri> (  λ lt → trio<> lt (s< c) ) (λ tx=ty → trio>≡ tx=ty (s< c) ) (s< c)

osuc : {n : Level} ( x : Ordinal {n} ) → Ordinal {n}
osuc record { lv = lx ; ord = ox } = record { lv = lx ; ord = OSuc lx ox }

<-osuc : {n : Level} { x : Ordinal {n} } → x o< osuc x
<-osuc {n} {record { lv = lx ; ord = Φ .lx }} =  case2 Φ<
<-osuc {n} {record { lv = lx ; ord = OSuc .lx ox }} = case2 ( s< s<refl )

osuc-lveq : {n : Level} { x : Ordinal {n} } → lv x ≡ lv ( osuc x )
osuc-lveq {n} = refl

nat-<> : { x y : Nat } → x < y → y < x → ⊥
nat-<>  (s≤s x<y) (s≤s y<x) = nat-<> x<y y<x

nat-<≡ : { x : Nat } → x < x → ⊥
nat-<≡  (s≤s lt) = nat-<≡ lt

nat-≡< : { x y : Nat } → x ≡ y → x < y → ⊥
nat-≡< refl lt = nat-<≡ lt

¬a≤a : {la : Nat} → Suc la ≤ la → ⊥
¬a≤a  (s≤s lt) = ¬a≤a  lt

=→¬< : {x : Nat  } → ¬ ( x < x )
=→¬< {Zero} ()
=→¬< {Suc x} (s≤s lt) = =→¬< lt

o<¬≡ : {n : Level } ( ox oy : Ordinal {n}) → ox ≡ oy  → ox o< oy  → ⊥
o<¬≡ ox ox refl (case1 lt) =  =→¬< lt
o<¬≡ ox ox refl (case2 (s< lt)) = trio<≡ refl lt

¬x<0 : {n : Level} →  { x  : Ordinal {suc n} } → ¬ ( x o< o∅ {suc n} )
¬x<0 {n} {x} (case1 ())
¬x<0 {n} {x} (case2 ())

o<> : {n : Level} →  {x y : Ordinal {n}  }  →  y o< x → x o< y → ⊥
o<> {n} {x} {y} (case1 x₁) (case1 x₂) = nat-<>  x₁ x₂
o<> {n} {x} {y} (case1 x₁) (case2 x₂) = nat-≡< (sym (d<→lv x₂)) x₁
o<> {n} {x} {y} (case2 x₁) (case1 x₂) = nat-≡< (sym (d<→lv x₁)) x₂
o<> {n} {record { lv = lv₁ ; ord = .(OSuc lv₁ _) }} {record { lv = .lv₁ ; ord = .(Φ lv₁) }} (case2 Φ<) (case2 ())
o<> {n} {record { lv = lv₁ ; ord = .(OSuc lv₁ _) }} {record { lv = .lv₁ ; ord = .(OSuc lv₁ _) }} (case2 (s< y<x)) (case2 (s< x<y)) = 
   o<> (case2 y<x) (case2 x<y)

orddtrans : {n : Level} {lx : Nat} {x y z : OrdinalD {n}  lx }   → x d< y → y d< z → x d< z
orddtrans {_} {lx} {.(Φ lx)} {.(OSuc lx _)} {.(OSuc lx _)} Φ< (s< y<z) = Φ< 
orddtrans {_} {lx} {.(OSuc lx _)} {.(OSuc lx _)} {.(OSuc lx _)} (s< x<y) (s< y<z) = s< ( orddtrans x<y y<z )

osuc-≡< : {n : Level} { a x : Ordinal {n} } → x o< osuc a  →  (x ≡ a ) ∨ (x o< a)  
osuc-≡< {n} {a} {x} (case1 lt) = case2 (case1 lt)
osuc-≡< {n} {record { lv = lv₁ ; ord = Φ .lv₁ }} {record { lv = .lv₁ ; ord = .(Φ lv₁) }} (case2 Φ<) = case1 refl
osuc-≡< {n} {record { lv = lv₁ ; ord = OSuc .lv₁ ord₁ }} {record { lv = .lv₁ ; ord = .(Φ lv₁) }} (case2 Φ<) = case2 (case2 Φ<)
osuc-≡< {n} {record { lv = lv₁ ; ord = Φ .lv₁ }} {record { lv = .lv₁ ; ord = .(OSuc lv₁ _) }} (case2 (s< ()))
osuc-≡< {n} {record { lv = la ; ord = OSuc la oa }} {record { lv = la ; ord = (OSuc la ox) }} (case2 (s< lt)) with
      osuc-≡< {n} {record { lv = la ; ord = oa }} {record { lv = la ; ord = ox }} (case2 lt )
... | case1 refl = case1 refl
... | case2 (case2 x) = case2 (case2( s< x) )
... | case2 (case1 x) = ⊥-elim (¬a≤a  x) where

osuc-< : {n : Level} { x y : Ordinal {n} } → y o< osuc x  → x o< y → ⊥
osuc-< {n} {x} {y} y<ox x<y with osuc-≡< y<ox
osuc-< {n} {x} {x} y<ox (case1 x₁) | case1 refl = ⊥-elim (¬a≤a x₁)
osuc-< {n} {x} {x} (case1 x₂) (case2 x₁) | case1 refl = ⊥-elim (¬a≤a x₂)
osuc-< {n} {x} {x} (case2 x₂) (case2 x₁) | case1 refl = ≡→¬d<  x₁
osuc-< {n} {x} {y} y<ox (case1 x₂) | case2 (case1 x₁) = nat-<> x₂ x₁
osuc-< {n} {x} {y} y<ox (case1 x₂) | case2 (case2 x₁) = nat-≡< (sym (d<→lv x₁)) x₂
osuc-< {n} {x} {y} y<ox (case2 x<y) | case2 y<x = o<> (case2 x<y) y<x

max : (x y : Nat) → Nat
max Zero Zero = Zero
max Zero (Suc x) = (Suc x)
max (Suc x) Zero = (Suc x)
max (Suc x) (Suc y) = Suc ( max x y )

maxαd : {n : Level} → { lx : Nat } → OrdinalD {n} lx  →  OrdinalD  lx  →  OrdinalD  lx
maxαd x y with triOrdd x y
maxαd x y | tri< a ¬b ¬c = y
maxαd x y | tri≈ ¬a b ¬c = x
maxαd x y | tri> ¬a ¬b c = x

_o≤_ : {n : Level} → Ordinal → Ordinal → Set (suc n)
a o≤ b  = (a ≡ b)  ∨ ( a o< b )

ordtrans : {n : Level} {x y z : Ordinal {n} }   → x o< y → y o< z → x o< z
ordtrans {n} {x} {y} {z} (case1 x₁) (case1 x₂) = case1 ( <-trans x₁ x₂ )
ordtrans {n} {x} {y} {z} (case1 x₁) (case2 x₂) with  d<→lv x₂
... | refl = case1 x₁
ordtrans {n} {x} {y} {z} (case2 x₁) (case1 x₂)  with  d<→lv x₁
... | refl = case1 x₂
ordtrans {n} {x} {y} {z} (case2 x₁) (case2 x₂) with d<→lv x₁ | d<→lv x₂
... | refl | refl = case2 ( orddtrans x₁ x₂ )

trio< : {n : Level } → Trichotomous {suc n} _≡_  _o<_ 
trio< a b with <-cmp (lv a) (lv b)
trio< a b | tri< a₁ ¬b ¬c = tri< (case1  a₁) (λ refl → ¬b (cong ( λ x → lv x ) refl ) ) lemma1 where
   lemma1 : ¬ (Suc (lv b) ≤ lv a) ∨ (ord b d< ord a)
   lemma1 (case1 x) = ¬c x
   lemma1 (case2 x) = ⊥-elim (nat-≡< (sym ( d<→lv x )) a₁  )
trio< a b | tri> ¬a ¬b c = tri> lemma1 (λ refl → ¬b (cong ( λ x → lv x ) refl ) ) (case1 c) where
   lemma1 : ¬ (Suc (lv a) ≤ lv b) ∨ (ord a d< ord b)
   lemma1 (case1 x) = ¬a x
   lemma1 (case2 x) = ⊥-elim (nat-≡< (sym ( d<→lv x )) c  )
trio< a b | tri≈ ¬a refl ¬c with triOrdd ( ord a ) ( ord b )
trio< record { lv = .(lv b) ; ord = x } b | tri≈ ¬a refl ¬c | tri< a ¬b ¬c₁ = tri< (case2 a) (λ refl → ¬b (lemma1 refl )) lemma2 where
   lemma1 :  (record { lv = _ ; ord = x }) ≡ b →  x ≡ ord b
   lemma1 refl = refl
   lemma2 : ¬ (Suc (lv b) ≤ lv b) ∨ (ord b d< x)
   lemma2 (case1 x) = ¬a x
   lemma2 (case2 x) = trio<> x a
trio< record { lv = .(lv b) ; ord = x } b | tri≈ ¬a refl ¬c | tri> ¬a₁ ¬b c = tri> lemma2 (λ refl → ¬b (lemma1 refl )) (case2 c) where
   lemma1 :  (record { lv = _ ; ord = x }) ≡ b →  x ≡ ord b
   lemma1 refl = refl
   lemma2 : ¬ (Suc (lv b) ≤ lv b) ∨ (x d< ord b)
   lemma2 (case1 x) = ¬a x
   lemma2 (case2 x) = trio<> x c
trio< record { lv = .(lv b) ; ord = x } b | tri≈ ¬a refl ¬c | tri≈ ¬a₁ refl ¬c₁ = tri≈ lemma1 refl lemma1 where
   lemma1 : ¬ (Suc (lv b) ≤ lv b) ∨ (ord b d< ord b)
   lemma1 (case1 x) = ¬a x
   lemma1 (case2 x) = ≡→¬d< x

maxα : {n : Level} →  Ordinal {n} →  Ordinal  → Ordinal
maxα x y with <-cmp (lv x) (lv y)
maxα x y | tri< a ¬b ¬c = x
maxα x y | tri> ¬a ¬b c = y
maxα x y | tri≈ ¬a refl ¬c = record { lv = lv x ; ord = maxαd (ord x) (ord y) }

--
--  max ( osuc x , osuc y )
--

omax : {n : Level} ( x y : Ordinal {suc n} ) → Ordinal {suc n}
omax {n} x y with trio< x y
omax {n} x y | tri< a ¬b ¬c = osuc y
omax {n} x y | tri> ¬a ¬b c = osuc x
omax {n} x y | tri≈ ¬a refl ¬c  = osuc x

omax< : {n : Level} ( x y : Ordinal {suc n} ) → x o< y → osuc y ≡ omax x y
omax< {n} x y lt with trio< x y
omax< {n} x y lt | tri< a ¬b ¬c = refl
omax< {n} x y lt | tri≈ ¬a b ¬c = ⊥-elim (¬a lt )
omax< {n} x y lt | tri> ¬a ¬b c = ⊥-elim (¬a lt )

omax≡ : {n : Level} ( x y : Ordinal {suc n} ) → x ≡ y → osuc y ≡ omax x y
omax≡ {n} x y eq with trio< x y
omax≡ {n} x y eq | tri< a ¬b ¬c = ⊥-elim (¬b eq )
omax≡ {n} x y eq | tri≈ ¬a refl ¬c = refl
omax≡ {n} x y eq | tri> ¬a ¬b c = ⊥-elim (¬b eq )

omax-x : {n : Level} ( x y : Ordinal {suc n} ) → x o< omax x y
omax-x {n} x y with trio< x y
omax-x {n} x y | tri< a ¬b ¬c = ordtrans a <-osuc
omax-x {n} x y | tri> ¬a ¬b c = <-osuc
omax-x {n} x y | tri≈ ¬a refl ¬c = <-osuc

omax-y : {n : Level} ( x y : Ordinal {suc n} ) → y o< omax x y
omax-y {n} x y with  trio< x y
omax-y {n} x y | tri< a ¬b ¬c = <-osuc
omax-y {n} x y | tri> ¬a ¬b c = ordtrans c <-osuc
omax-y {n} x y | tri≈ ¬a refl ¬c = <-osuc

omxx : {n : Level} ( x : Ordinal {suc n} ) → omax x x ≡ osuc x
omxx {n} x with  trio< x x
omxx {n} x | tri< a ¬b ¬c = ⊥-elim (¬b refl )
omxx {n} x | tri> ¬a ¬b c = ⊥-elim (¬b refl )
omxx {n} x | tri≈ ¬a refl ¬c = refl

omxxx : {n : Level} ( x : Ordinal {suc n} ) → omax x (omax x x ) ≡ osuc (osuc x)
omxxx {n} x = trans ( cong ( λ k → omax x k ) (omxx x )) (sym ( omax< x (osuc x) <-osuc ))

open _∧_

osuc2 : {n : Level} ( x y : Ordinal {suc n} ) → ( osuc x o< osuc (osuc y )) ⇔ (x o< osuc y)
proj1 (osuc2 {n} x y) (case1 lt) = case1 lt
proj1 (osuc2 {n} x y) (case2 (s< lt)) = case2 lt
proj2 (osuc2 {n} x y) (case1 lt) = case1 lt
proj2 (osuc2 {n} x y) (case2 lt) with d<→lv lt
... | refl = case2 (s< lt)

-- omax≡ (omax x x ) (osuc x) (omxx x)

OrdTrans : {n : Level} → Transitive {suc n} _o≤_
OrdTrans (case1 refl) (case1 refl) = case1 refl
OrdTrans (case1 refl) (case2 lt2) = case2 lt2
OrdTrans (case2 lt1) (case1 refl) = case2 lt1
OrdTrans (case2 x) (case2 y) = case2 (ordtrans x y)

OrdPreorder : {n : Level} → Preorder (suc n) (suc n) (suc n)
OrdPreorder {n} = record { Carrier = Ordinal
   ; _≈_  = _≡_ 
   ; _∼_   = _o≤_
   ; isPreorder   = record {
        isEquivalence = record { refl = refl  ; sym = sym ; trans = trans }
        ; reflexive     = case1 
        ; trans         = OrdTrans 
     }
 }

TransFinite : {n : Level} → { ψ : Ordinal {n} → Set n }
  → ( ∀ (lx : Nat ) → ψ ( record { lv = lx ; ord = Φ lx } ) )
  → ( ∀ (lx : Nat ) → (x : OrdinalD lx )  → ψ ( record { lv = lx ; ord = x } ) → ψ ( record { lv = lx ; ord = OSuc lx x } ) )
  →  ∀ (x : Ordinal)  → ψ x
TransFinite caseΦ caseOSuc record { lv = lv ; ord = (Φ (lv)) } = caseΦ lv
TransFinite caseΦ caseOSuc record { lv = lx ; ord = (OSuc lx ox) } = 
      caseOSuc lx ox (TransFinite caseΦ caseOSuc  record { lv = lx ; ord = ox })

