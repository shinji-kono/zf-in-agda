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
open Ordinals.IsNext isNext 

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

osuc-< :  { x y : Ordinal  } → y o< osuc x  → x o< y → ⊥
osuc-< {x} {y} y<ox x<y with osuc-≡< y<ox
osuc-< {x} {y} y<ox x<y | case1 refl = o<¬≡ refl x<y
osuc-< {x} {y} y<ox x<y | case2 y<x = o<> x<y y<x

osucc :  {ox oy : Ordinal } → oy o< ox  → osuc oy o< osuc ox  
----   y < osuc y < x < osuc x
----   y < osuc y = x < osuc x
----   y < osuc y > x < osuc x   -> y = x ∨ x < y → ⊥
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

open _∧_

osuc2 :  ( x y : Ordinal  ) → ( osuc x o< osuc (osuc y )) ⇔ (x o< osuc y)
proj2 (osuc2 x y) lt = osucc lt
proj1 (osuc2 x y) ox<ooy with osuc-≡< ox<ooy
proj1 (osuc2 x y) ox<ooy | case1 ox=oy = o<-subst <-osuc refl ox=oy
proj1 (osuc2 x y) ox<ooy | case2 ox<oy = ordtrans <-osuc ox<oy 

_o≤_ :  Ordinal → Ordinal → Set  n
a o≤ b  = a o< osuc b -- (a ≡ b)  ∨ ( a o< b )


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
omax  x y | tri≈ ¬a refl ¬c  = osuc x

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
omxx  x | tri≈ ¬a refl ¬c = refl

omxxx :  ( x : Ordinal  ) → omax x (omax x x ) ≡ osuc (osuc x)
omxxx  x = trans ( cong ( λ k → omax x k ) (omxx x )) (sym ( omax< x (osuc x) <-osuc ))

open _∧_

o≤-refl :  { i  j : Ordinal } → i ≡ j → i o≤ j
o≤-refl {i} {j} eq = subst (λ k → i o< osuc k ) eq <-osuc
OrdTrans :  Transitive  _o≤_
OrdTrans a≤b b≤c with osuc-≡< a≤b | osuc-≡< b≤c
OrdTrans a≤b b≤c | case1 refl | case1 refl = <-osuc
OrdTrans a≤b b≤c | case1 refl | case2 a≤c = ordtrans a≤c <-osuc
OrdTrans a≤b b≤c | case2 a≤c | case1 refl = ordtrans a≤c <-osuc
OrdTrans a≤b b≤c | case2 a<b | case2 b<c = ordtrans (ordtrans a<b  b<c) <-osuc

OrdPreorder :   Preorder n n n
OrdPreorder  = record { Carrier = Ordinal
   ; _≈_  = _≡_ 
   ; _∼_   = _o≤_
   ; isPreorder   = record {
        isEquivalence = record { refl = refl  ; sym = sym ; trans = trans }
        ; reflexive     = o≤-refl
        ; trans         = OrdTrans 
     }
 }

FExists : {m l : Level} → ( ψ : Ordinal  → Set m ) 
  → {p : Set l} ( P : { y : Ordinal  } →  ψ y → ¬ p )
  → (exists : ¬ (∀ y → ¬ ( ψ y ) ))
  → ¬ p
FExists  {m} {l} ψ {p} P = contra-position ( λ p y ψy → P {y} ψy p ) 

nexto∅ : {x : Ordinal} → o∅ o< next x
nexto∅ {x} with trio< o∅ x
nexto∅ {x} | tri< a ¬b ¬c = ordtrans a x<nx
nexto∅ {x} | tri≈ ¬a b ¬c = subst (λ k → k o< next x) (sym b) x<nx
nexto∅ {x} | tri> ¬a ¬b c = ⊥-elim ( ¬x<0 c )

next< : {x y z : Ordinal} → x o< next z  → y o< next x → y o< next z
next< {x} {y} {z} x<nz y<nx with trio< y (next z)
next< {x} {y} {z} x<nz y<nx | tri< a ¬b ¬c = a
next< {x} {y} {z} x<nz y<nx | tri≈ ¬a b ¬c = ⊥-elim (¬nx<nx x<nz (subst (λ k → k o< next x) b y<nx)
   (λ w nz=ow → o<¬≡ nz=ow (subst₂ (λ j k → j o< k ) (sym nz=ow) nz=ow (osuc<nx (subst (λ k → w o< k ) (sym nz=ow) <-osuc) ))))
next< {x} {y} {z} x<nz y<nx | tri> ¬a ¬b c = ⊥-elim (¬nx<nx x<nz (ordtrans c y<nx )
   (λ w nz=ow → o<¬≡ (sym nz=ow) (osuc<nx (subst (λ k → w o< k ) (sym nz=ow) <-osuc ))))

osuc< : {x y : Ordinal} → osuc x ≡ y → x o< y
osuc< {x} {y} refl = <-osuc 

nexto=n : {x y : Ordinal} → x o< next (osuc y)  → x o< next y 
nexto=n {x} {y} x<noy = next< (osuc<nx x<nx) x<noy

nexto≡ : {x : Ordinal} → next x ≡ next (osuc x)  
nexto≡ {x} with trio< (next x) (next (osuc x) ) 
--    next x o< next (osuc x ) ->  osuc x o< next x o< next (osuc x) -> next x ≡ osuc z -> z o o< next x -> osuc z o< next x -> next x o< next x
nexto≡ {x} | tri< a ¬b ¬c = ⊥-elim (¬nx<nx (osuc<nx  x<nx ) a
   (λ z eq → o<¬≡ (sym eq) (osuc<nx  (osuc< (sym eq)))))
nexto≡ {x} | tri≈ ¬a b ¬c = b
--    next (osuc x) o< next x ->  osuc x o< next (osuc x) o< next x -> next (osuc x) ≡ osuc z -> z o o< next (osuc x) ...
nexto≡ {x} | tri> ¬a ¬b c = ⊥-elim (¬nx<nx (ordtrans <-osuc x<nx) c
   (λ z eq → o<¬≡ (sym eq) (osuc<nx  (osuc< (sym eq)))))

next-is-limit : {x y : Ordinal} → ¬ (next x ≡ osuc y)
next-is-limit {x} {y} eq = o<¬≡ (sym eq) (osuc<nx y<nx) where
    y<nx : y o< next x
    y<nx = osuc< (sym eq)

omax<next : {x y : Ordinal} → x o< y → omax x y o< next y
omax<next {x} {y} x<y = subst (λ k → k o< next y ) (omax< _ _ x<y ) (osuc<nx x<nx)

x<ny→≡next : {x y : Ordinal} → x o< y → y o< next x → next x ≡ next y
x<ny→≡next {x} {y} x<y y<nx with trio< (next x) (next y)    
x<ny→≡next {x} {y} x<y y<nx | tri< a ¬b ¬c =          -- x < y < next x <  next y ∧ next x = osuc z
     ⊥-elim ( ¬nx<nx y<nx a (λ z eq →  o<¬≡ (sym eq) (osuc<nx (subst (λ k → z o< k ) (sym eq) <-osuc )))) 
x<ny→≡next {x} {y} x<y y<nx | tri≈ ¬a b ¬c = b
x<ny→≡next {x} {y} x<y y<nx | tri> ¬a ¬b c =          -- x < y < next y < next x
     ⊥-elim ( ¬nx<nx (ordtrans x<y x<nx) c (λ z eq →  o<¬≡ (sym eq) (osuc<nx (subst (λ k → z o< k ) (sym eq) <-osuc )))) 

≤next : {x y : Ordinal} → x o≤ y → next x o≤ next y
≤next {x} {y} x≤y with trio< (next x) y
≤next {x} {y} x≤y | tri< a ¬b ¬c = ordtrans a (ordtrans x<nx <-osuc )
≤next {x} {y} x≤y | tri≈ ¬a refl ¬c = (ordtrans x<nx <-osuc )
≤next {x} {y} x≤y | tri> ¬a ¬b c with osuc-≡< x≤y
≤next {x} {y} x≤y | tri> ¬a ¬b c | case1 refl = o≤-refl refl   -- x = y < next x
≤next {x} {y} x≤y | tri> ¬a ¬b c | case2 x<y = o≤-refl (x<ny→≡next x<y c) -- x ≤ y < next x 

x<ny→≤next : {x y : Ordinal} → x o< next y → next x o≤ next y
x<ny→≤next {x} {y} x<ny with trio< x y
x<ny→≤next {x} {y} x<ny | tri< a ¬b ¬c =  ≤next (ordtrans a <-osuc )
x<ny→≤next {x} {y} x<ny | tri≈ ¬a refl ¬c =  o≤-refl refl
x<ny→≤next {x} {y} x<ny | tri> ¬a ¬b c = o≤-refl (sym ( x<ny→≡next c x<ny ))

omax<nomax : {x y : Ordinal} → omax x y o< next (omax x y )
omax<nomax {x} {y} with trio< x y
omax<nomax {x} {y} | tri< a ¬b ¬c    = subst (λ k → osuc y o< k ) nexto≡ (osuc<nx x<nx )
omax<nomax {x} {y} | tri≈ ¬a refl ¬c = subst (λ k → osuc x o< k ) nexto≡ (osuc<nx x<nx )
omax<nomax {x} {y} | tri> ¬a ¬b c    = subst (λ k → osuc x o< k ) nexto≡ (osuc<nx x<nx )

omax<nx : {x y z : Ordinal} → x o< next z → y o< next z → omax x y o< next z
omax<nx {x} {y} {z} x<nz y<nz with trio< x y
omax<nx {x} {y} {z} x<nz y<nz | tri< a ¬b ¬c = osuc<nx y<nz
omax<nx {x} {y} {z} x<nz y<nz | tri≈ ¬a refl ¬c = osuc<nx y<nz
omax<nx {x} {y} {z} x<nz y<nz | tri> ¬a ¬b c = osuc<nx x<nz

nn<omax : {x nx ny : Ordinal} → x o< next nx → x o< next ny → x o< next (omax nx ny)
nn<omax {x} {nx} {ny} xnx xny with trio< nx ny
nn<omax {x} {nx} {ny} xnx xny | tri< a ¬b ¬c = subst (λ k → x o< k ) nexto≡ xny
nn<omax {x} {nx} {ny} xnx xny | tri≈ ¬a refl ¬c = subst (λ k → x o< k ) nexto≡ xny
nn<omax {x} {nx} {ny} xnx xny | tri> ¬a ¬b c = subst (λ k → x o< k ) nexto≡ xnx

record OrdinalSubset (maxordinal : Ordinal) : Set (suc n) where
  field
    os→ : (x : Ordinal) → x o< maxordinal → Ordinal
    os← : Ordinal → Ordinal
    os←limit : (x : Ordinal) → os← x o< maxordinal
    os-iso← : {x : Ordinal} →  os→  (os← x) (os←limit x) ≡ x
    os-iso→ : {x : Ordinal} → (lt : x o< maxordinal ) →  os← (os→ x lt) ≡ x

module o≤-Reasoning {n : Level}  (O : Ordinals {n} )  where

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
         ordtrans --<-trans
         (resp₂ _o<_) --(resp₂ _<_)
         (λ x → ordtrans x <-osuc ) --<⇒≤
         trans1 --<-transˡ
         trans2 --<-transʳ
         public
         -- hiding (_≈⟨_⟩_)

