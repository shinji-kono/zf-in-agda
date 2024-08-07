{-# OPTIONS --cubical-compatible --safe #-}

open import Level
open import Ordinals
module OrdUtil {n : Level} (O : Ordinals {n} ) where

open import logic
open import nat
open import Data.Nat renaming ( zero to Zero ; suc to Suc ;  ℕ to Nat ; _⊔_ to _n⊔_ )
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Binary hiding (_⇔_)

open Ordinals.Ordinals  O
open Ordinals.IsOrdinals isOrdinal
-- open Ordinals.IsNext isNext

o<-dom :   { x y : Ordinal } → x o< y → Ordinal
o<-dom  {x} _ = x

o<-cod :   { x y : Ordinal } → x o< y → Ordinal
o<-cod  {_} {y} _ = y

o<-subst : {Z X z x : Ordinal }  → Z o< X → Z ≡ z  →  X ≡ x  →  z o< x
o<-subst df refl refl = df

o<¬≡ :  { ox oy : Ordinal } → ox ≡ oy  → ox o< oy  → ⊥
o<¬≡ {ox} {oy} eq lt with trio< ox oy
o<¬≡ {ox} {oy} eq lt | tri< a ¬b ¬c = ¬b eq
o<¬≡ {ox} {oy} eq lt | tri≈ ¬a b ¬c = ¬a lt
o<¬≡ {ox} {oy} eq lt | tri> ¬a ¬b c = ¬b eq

o<> :   {x y : Ordinal   }  →  y o< x → x o< y → ⊥
o<> {ox} {oy} lt tl with trio< ox oy
o<> {ox} {oy} lt tl | tri< a ¬b ¬c = ¬c lt
o<> {ox} {oy} lt tl | tri≈ ¬a b ¬c = ¬a tl
o<> {ox} {oy} lt tl | tri> ¬a ¬b c = ¬a tl

o≤> :  { x y : Ordinal  } → y o< osuc x  → x o< y → ⊥
o≤> {x} {y} y<ox x<y with osuc-≡< y<ox
o≤> {x} {y} y<ox x<y | case1 refl = o<¬≡ refl x<y
o≤> {x} {y} y<ox x<y | case2 y<x = o<> x<y y<x

open _∧_

¬p<x<op : { p b : Ordinal } → ¬ ( (p o< b ) ∧ (b o< osuc p ) )
¬p<x<op {p} {b} P with osuc-≡< (proj2 P)
... | case1 eq = o<¬≡ (sym eq) (proj1 P)
... | case2 lt = o<> lt (proj1 P)

b<x→0<x : { p b : Ordinal } → p o< b →  o∅  o< b
b<x→0<x {p} {b} p<b with trio< o∅ b
... | tri< a ¬b ¬c = a
... | tri≈ ¬a 0=b ¬c = ⊥-elim ( ¬x<0 ( subst (λ k → p o< k) (sym 0=b) p<b ) )
... | tri> ¬a ¬b c = ⊥-elim ( ¬x<0 c )

ob<x : {b x : Ordinal} (lim : ¬ (Oprev Ordinal osuc x ) ) (b<x : b o< x ) → osuc b o< x
ob<x {b} {x} lim b<x with trio< (osuc b) x
... | tri< a ¬b ¬c = a
... | tri≈ ¬a ob=x ¬c = ⊥-elim ( lim record { oprev = b ; oprev=x = ob=x }  )
... | tri> ¬a ¬b c = ⊥-elim ( ¬p<x<op ⟪ b<x , c ⟫ )


pxo<x : {x : Ordinal} (op : Oprev Ordinal osuc x)  → Oprev.oprev op o< x
pxo<x {x} op with trio< (Oprev.oprev op) x
... | tri< a ¬b ¬c = a
... | tri≈ ¬a b ¬c = ⊥-elim ( o<¬≡ (trans b (sym (Oprev.oprev=x op))) <-osuc )
... | tri> ¬a ¬b c = ⊥-elim ( o<> c (subst₂ (λ j k → j o< k ) refl (Oprev.oprev=x op) <-osuc ) )

pxo≤x : {x : Ordinal} (op : Oprev Ordinal osuc x)  → Oprev.oprev op o< osuc x
pxo≤x {x} op = ordtrans (pxo<x {x} op ) <-osuc


osucc :  {ox oy : Ordinal } → oy o< ox  → osuc oy o< osuc ox
osucc {ox} {oy} oy<ox with trio< (osuc oy) ox
osucc {ox} {oy} oy<ox | tri< a ¬b ¬c = ordtrans a <-osuc
osucc {ox} {oy} oy<ox | tri≈ ¬a refl ¬c = <-osuc
osucc {ox} {oy} oy<ox | tri> ¬a ¬b c with  osuc-≡< c
osucc {ox} {oy} oy<ox | tri> ¬a ¬b c | case1 eq = ⊥-elim (o<¬≡ (sym eq) oy<ox)
osucc {ox} {oy} oy<ox | tri> ¬a ¬b c | case2 lt = ⊥-elim (o<> lt oy<ox)

osucprev :  {ox oy : Ordinal } → osuc oy o< osuc ox  → oy o< ox
osucprev {ox} {oy} oy<ox with trio< oy ox
osucprev {ox} {oy} oy<ox | tri< a ¬b ¬c = a
osucprev {ox} {oy} oy<ox | tri≈ ¬a b ¬c = ⊥-elim (o<¬≡ (cong (λ k → osuc k) b) oy<ox )
osucprev {ox} {oy} oy<ox | tri> ¬a ¬b c = ⊥-elim (o<> (osucc c) oy<ox )

ordtrans≤-< :  {ox oy oz : Ordinal } → ox o< osuc oy  → oy o< oz  → ox o< oz
ordtrans≤-< {ox} {oy} {oz} x≤y y<z with  osuc-≡< x≤y
... | case1 x=y = subst ( λ k → k o< oz ) (sym x=y) y<z
... | case2 x<y = ordtrans x<y y<z

ordtrans<-≤ :  {ox oy oz : Ordinal } → ox o< oy  → oy o< osuc oz  → ox o< oz
ordtrans<-≤ {ox} {oy} {oz} x<y y≤z with  osuc-≡< y≤z
... | case1 x=y = subst ( λ k → ox o< k ) (x=y) x<y
... | case2 y<z = ordtrans x<y y<z

o∅≤z : {z : Ordinal } → o∅ o< (osuc z)
o∅≤z {z} = b<x→0<x ( <-osuc )

osuc2 :  ( x y : Ordinal  ) → ( osuc x o< osuc (osuc y )) ⇔ (x o< osuc y)
proj2 (osuc2 x y) lt = osucc lt
proj1 (osuc2 x y) ox<ooy with osuc-≡< ox<ooy
proj1 (osuc2 x y) ox<ooy | case1 ox=oy = o<-subst <-osuc refl ox=oy
proj1 (osuc2 x y) ox<ooy | case2 ox<oy = ordtrans <-osuc ox<oy

o≡? : (x y : Ordinal) → Dec0 ( x ≡ y )
o≡? x y with trio< x y
... | tri< a ¬b ¬c = no0 ¬b
... | tri≈ ¬a b ¬c = yes0 b
... | tri> ¬a ¬b c = no0 ¬b

_o≤_ :  Ordinal → Ordinal → Set  n
a o≤ b  = a o< osuc b -- (a ≡ b)  ∨ ( a o< b )

o<→≤ : {a b : Ordinal} → a o< b → a o≤ b
o<→≤ {a} {b} lt with trio< a (osuc b)
... | tri< a₁ ¬b ¬c = a₁
... | tri≈ ¬a b₁ ¬c = ⊥-elim (¬a (ordtrans lt <-osuc ) )
... | tri> ¬a ¬b c  = ⊥-elim (¬a (ordtrans lt <-osuc ) )

-- o<-irr : { x y : Ordinal } → { lt lt1 : x o< y } → lt ≡ lt1

xo<ab :  {oa ob : Ordinal } → ( {ox : Ordinal } → ox o< oa  → ox o< ob ) → oa o< osuc ob
xo<ab   {oa} {ob} a→b with trio< oa ob
xo<ab   {oa} {ob} a→b | tri< a ¬b ¬c = ordtrans a <-osuc
xo<ab   {oa} {ob} a→b | tri≈ ¬a refl ¬c = <-osuc
xo<ab   {oa} {ob} a→b | tri> ¬a ¬b c = ⊥-elim ( o<¬≡ refl (a→b c )  )

maxα :   Ordinal  →  Ordinal  → Ordinal
maxα x y with trio< x y
maxα x y | tri< a ¬b ¬c = y
maxα x y | tri> ¬a ¬b c = x
maxα x y | tri≈ ¬a refl ¬c = x

omin :    Ordinal  →  Ordinal  → Ordinal
omin  x y with trio<  x  y
omin x y | tri< a ¬b ¬c = x
omin x y | tri> ¬a ¬b c = y
omin x y | tri≈ ¬a refl ¬c = x

min1 :   {x y z : Ordinal  } → z o< x → z o< y → z o< omin x y
min1  {x} {y} {z} z<x z<y with trio<  x y
min1  {x} {y} {z} z<x z<y | tri< a ¬b ¬c = z<x
min1  {x} {y} {z} z<x z<y | tri≈ ¬a refl ¬c = z<x
min1  {x} {y} {z} z<x z<y | tri> ¬a ¬b c = z<y

--
--  max ( osuc x , osuc y )
--

omax :  ( x y : Ordinal  ) → Ordinal
omax  x y with trio< x y
omax  x y | tri< a ¬b ¬c = osuc y
omax  x y | tri> ¬a ¬b c = osuc x
omax  x y | tri≈ ¬a b ¬c  = osuc x

omax< :  ( x y : Ordinal  ) → x o< y → osuc y ≡ omax x y
omax<  x y lt with trio< x y
omax<  x y lt | tri< a ¬b ¬c = refl
omax<  x y lt | tri≈ ¬a b ¬c = ⊥-elim (¬a lt )
omax<  x y lt | tri> ¬a ¬b c = ⊥-elim (¬a lt )

omax≤ :  ( x y : Ordinal  ) → x o≤ y → osuc y ≡ omax x y
omax≤  x y le with trio< x y
omax≤  x y le | tri< a ¬b ¬c = refl
omax≤  x y le | tri≈ ¬a refl ¬c = refl
omax≤  x y le | tri> ¬a ¬b c with osuc-≡< le
omax≤ x y le | tri> ¬a ¬b c | case1 eq = ⊥-elim (¬b eq)
omax≤ x y le | tri> ¬a ¬b c | case2 x<y = ⊥-elim (¬a x<y)

omax≡ :  ( x y : Ordinal  ) → x ≡ y → osuc y ≡ omax x y
omax≡  x y eq with trio< x y
omax≡  x y eq | tri< a ¬b ¬c = ⊥-elim (¬b eq )
omax≡  x y eq | tri≈ ¬a refl ¬c = refl
omax≡  x y eq | tri> ¬a ¬b c = ⊥-elim (¬b eq )

omax-x :  ( x y : Ordinal  ) → x o< omax x y
omax-x  x y with trio< x y
omax-x  x y | tri< a ¬b ¬c = ordtrans a <-osuc
omax-x  x y | tri> ¬a ¬b c = <-osuc
omax-x  x y | tri≈ ¬a refl ¬c = <-osuc

omax-y :  ( x y : Ordinal  ) → y o< omax x y
omax-y  x y with  trio< x y
omax-y  x y | tri< a ¬b ¬c = <-osuc
omax-y  x y | tri> ¬a ¬b c = ordtrans c <-osuc
omax-y  x y | tri≈ ¬a refl ¬c = <-osuc

omxx :  ( x : Ordinal  ) → omax x x ≡ osuc x
omxx  x with  trio< x x
omxx  x | tri< a ¬b ¬c = ⊥-elim (¬b refl )
omxx  x | tri> ¬a ¬b c = ⊥-elim (¬b refl )
omxx  x | tri≈ ¬a b ¬c =  refl

omxxx :  ( x : Ordinal  ) → omax x (omax x x ) ≡ osuc (osuc x)
omxxx  x = trans ( cong ( λ k → omax x k ) (omxx x )) (sym ( omax< x (osuc x) <-osuc ))

open _∧_

o≤-refl0 :  { i  j : Ordinal } → i ≡ j → i o≤ j
o≤-refl0 {i} {j} eq = subst (λ k → i o< osuc k ) eq <-osuc

o≤-refl :  { i : Ordinal } → i o≤ i
o≤-refl {i} = subst (λ k → i o< osuc k ) refl <-osuc

o≤? : (x y : Ordinal) → Dec0 ( x o≤ y )
o≤? x y with trio< x y
... | tri< a ¬b ¬c = yes0 (ordtrans a <-osuc)
... | tri≈ ¬a b ¬c = yes0 (o≤-refl0 b)
... | tri> ¬a ¬b c = no0 (λ n → o≤> n c )

o¬≤→< : {x z : Ordinal} →  ¬ (x o< osuc z) → z o< x
o¬≤→< {x} {z} not with trio< z x
... | tri< a ¬b ¬c = a
... | tri≈ ¬a b ¬c = ⊥-elim (not (o≤-refl0 (sym b)))
... | tri> ¬a ¬b c = ⊥-elim (not (o<→≤ c ))

b≤px∨b=x : {b x  : Ordinal } → (op : Oprev Ordinal osuc x ) → b o≤ x  →   (b o≤ (Oprev.oprev op) ) ∨ (b ≡ x )
b≤px∨b=x {b} {x} op b≤x with trio< b (Oprev.oprev op) 
... | tri< a ¬b ¬c = case1 (o<→≤ a)
... | tri≈ ¬a b ¬c = case1 (o≤-refl0 b)
... | tri> ¬a ¬b px<b with osuc-≡< b≤x
... | case1 eq = case2 eq
... | case2 b<x = ⊥-elim ( ¬p<x<op ⟪ px<b , subst (λ k → b o< k ) (sym (Oprev.oprev=x op)) b<x  ⟫ ) 

x<y∨y≤x : (x sp1 : Ordinal ) → ( x o< sp1 ) ∨ ( sp1 o≤ x )
x<y∨y≤x x sp1 with trio< x sp1
... | tri< a ¬b ¬c = case1 a
... | tri≈ ¬a b ¬c = case2 (o≤-refl0 (sym b))
... | tri> ¬a ¬b c = case2 (o<→≤ c)

OrdTrans :  Transitive  _o≤_
OrdTrans a≤b b≤c with osuc-≡< a≤b | osuc-≡< b≤c
OrdTrans a≤b b≤c | case1 refl | case1 refl = <-osuc
OrdTrans a≤b b≤c | case1 refl | case2 a≤c = ordtrans a≤c <-osuc
OrdTrans a≤b b≤c | case2 a≤c | case1 refl = ordtrans a≤c <-osuc
OrdTrans a≤b b≤c | case2 a<b | case2 b<c = ordtrans (ordtrans a<b  b<c) <-osuc

OrdPreorder :   Preorder n n n
OrdPreorder  = record { Carrier = Ordinal
   ; _≈_  = _≡_
   ; _≲_ = _o≤_  -- _∼_   = _o≤_
   ; isPreorder   = record {
        isEquivalence = record { refl = refl  ; sym = sym ; trans = trans }
        ; reflexive     = o≤-refl0
        ; trans         = OrdTrans
     }
 }

FExists : {m l : Level} → ( ψ : Ordinal  → Set m )
  → {p : Set l} ( P : { y : Ordinal  } →  ψ y → ¬ p )
  → (exists : ¬ (∀ y → ¬ ( ψ y ) ))
  → ¬ p
FExists  {m} {l} ψ {p} P = contra-position ( λ p y ψy → P {y} ψy p )

osuc< : {x y : Ordinal} → osuc x ≡ y → x o< y
osuc< {x} {y} refl = <-osuc

record OrdinalSubset (maxordinal : Ordinal) : Set (suc n) where
  field
    os→ : (x : Ordinal) → x o< maxordinal → Ordinal
    os← : Ordinal → Ordinal
    os←limit : (x : Ordinal) → os← x o< maxordinal
    os-iso← : {x : Ordinal} →  os→  (os← x) (os←limit x) ≡ x
    os-iso→ : {x : Ordinal} → (lt : x o< maxordinal ) →  os← (os→ x lt) ≡ x

open import Relation.Binary.Reasoning.Syntax

module o≤-Reasoning  where

    -- open inOrdinal O

    resp-o< : _o<_ Respects₂ _≡_
    resp-o< =  resp₂ _o<_

    trans1 : {i j k : Ordinal} → i o< j → j o< osuc  k → i o< k
    trans1 {i} {j} {k} i<j j<ok with osuc-≡< j<ok
    trans1 {i} {j} {k} i<j j<ok | case1 refl = i<j
    trans1 {i} {j} {k} i<j j<ok | case2 j<k = ordtrans i<j j<k

    trans2 : {i j k : Ordinal} → i o< osuc j → j o<  k → i o< k
    trans2 {i} {j} {k} i<oj j<k with osuc-≡< i<oj
    trans2 {i} {j} {k} i<oj j<k | case1 refl = j<k
    trans2 {i} {j} {k} i<oj j<k | case2 i<j = ordtrans i<j j<k

    open import Relation.Binary.Reasoning.Base.Triple
        (Preorder.isPreorder OrdPreorder)
        (λ {x} {y} x<y y<x → o<> x<y y<x )
        ordtrans 
        (resp₂ _o<_) 
        (λ x → ordtrans x <-osuc ) 
        trans1 
        trans2
        public
        hiding (step-≈; step-≈˘; step-≈-⟩; step-≈-⟨)
        
