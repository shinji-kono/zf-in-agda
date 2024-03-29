open import Level 
module ordinal where

open import logic
open import nat
open import Data.Nat renaming ( zero to Zero ; suc to Suc ; _⊔_ to _n⊔_ ) 
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Definitions
open import Data.Nat.Properties as NP
open import Relation.Nullary
open import Relation.Binary.Core

----
--
-- Countable Ordinals
--

data OrdinalD {n : Level} :  (lv : ℕ) → Set n where
   Φ : (lv : ℕ) → OrdinalD  lv
   OSuc : (lv : ℕ) → OrdinalD {n} lv → OrdinalD lv

record Ordinal {n : Level} : Set n where
   constructor ordinal  
   field
     lv : ℕ
     ord : OrdinalD {n} lv

data _d<_ {n : Level} :   {lx ly : ℕ} → OrdinalD {n} lx  →  OrdinalD {n} ly  → Set n where
   Φ<  : {lx : ℕ} → {x : OrdinalD {n} lx}  →  Φ lx d< OSuc lx x
   s<  : {lx : ℕ} → {x y : OrdinalD {n} lx}  →  x d< y  → OSuc  lx x d< OSuc  lx y

open Ordinal

_o<_ : {n : Level} ( x y : Ordinal ) → Set n
_o<_ x y =  (lv x < lv y )  ∨ ( ord x d< ord y )

s<refl : {n : Level } {lx : ℕ } { x : OrdinalD {n} lx } → x d< OSuc lx x
s<refl {n} {lv} {Φ lv}  = Φ<
s<refl {n} {lv} {OSuc lv x}  = s< s<refl 

trio<> : {n : Level} →  {lx : ℕ} {x  : OrdinalD {n} lx } { y : OrdinalD  lx }  →  y d< x → x d< y → ⊥
trio<>  {n} {lx} {.(OSuc lx _)} {.(OSuc lx _)} (s< s) (s< t) = trio<> s t
trio<> {n} {lx} {.(OSuc lx _)} {.(Φ lx)} Φ< ()

d<→lv : {n : Level} {x y  : Ordinal {n}}   → ord x d< ord y → lv x ≡ lv y
d<→lv Φ< = refl
d<→lv (s< lt) = refl

o∅ : {n : Level} → Ordinal {n}
o∅  = record { lv = Zero ; ord = Φ Zero }

open import Relation.Binary.HeterogeneousEquality using (_≅_;refl)

ordinal-cong : {n : Level} {x y : Ordinal {n}}  →
      lv x  ≡ lv y → ord x ≅ ord y →  x ≡ y
ordinal-cong refl refl = refl

≡→¬d< : {n : Level} →  {lv : ℕ} → {x  : OrdinalD {n}  lv }  → x d< x → ⊥
≡→¬d<  {n} {lx} {OSuc lx y} (s< t) = ≡→¬d< t

trio<≡ : {n : Level} →  {lx : ℕ} {x  : OrdinalD {n} lx } { y : OrdinalD  lx }  → x ≡ y  → x d< y → ⊥
trio<≡ refl = ≡→¬d<

trio>≡ : {n : Level} →  {lx : ℕ} {x  : OrdinalD {n} lx } { y : OrdinalD  lx }  → x ≡ y  → y d< x → ⊥
trio>≡ refl = ≡→¬d<

triOrdd : {n : Level} →  {lx : ℕ}   → Trichotomous  _≡_ ( _d<_  {n} {lx} {lx} )
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

o<¬≡ : {n : Level } { ox oy : Ordinal {suc n}} → ox ≡ oy  → ox o< oy  → ⊥
o<¬≡ {_} {ox} {ox} refl (case1 lt) =  =→¬< lt
o<¬≡ {_} {ox} {ox} refl (case2 (s< lt)) = trio<≡ refl lt

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

orddtrans : {n : Level} {lx : ℕ} {x y z : OrdinalD {n}  lx }   → x d< y → y d< z → x d< z
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
... | case2 (case1 x) = ⊥-elim (¬a≤a  x) 

osuc-< : {n : Level} { x y : Ordinal {n} } → y o< osuc x  → x o< y → ⊥
osuc-< {n} {x} {y} y<ox x<y with osuc-≡< y<ox
osuc-< {n} {x} {x} y<ox (case1 x₁) | case1 refl = ⊥-elim (¬a≤a x₁)
osuc-< {n} {x} {x} (case1 x₂) (case2 x₁) | case1 refl = ⊥-elim (¬a≤a x₂)
osuc-< {n} {x} {x} (case2 x₂) (case2 x₁) | case1 refl = ≡→¬d<  x₁
osuc-< {n} {x} {y} y<ox (case1 x₂) | case2 (case1 x₁) = nat-<> x₂ x₁
osuc-< {n} {x} {y} y<ox (case1 x₂) | case2 (case2 x₁) = nat-≡< (sym (d<→lv x₁)) x₂
osuc-< {n} {x} {y} y<ox (case2 x<y) | case2 y<x = o<> (case2 x<y) y<x


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


open _∧_

TransFinite : {n m : Level} → { ψ : Ordinal {suc n} → Set m }
  → ( ∀ (lx : ℕ ) → ( (x : Ordinal {suc n} ) → x o< ordinal lx (Φ lx)  → ψ x ) → ψ ( record { lv = lx ; ord = Φ lx } ) )
  → ( ∀ (lx : ℕ ) → (x : OrdinalD lx ) → ( (y : Ordinal {suc n} ) → y o< ordinal lx (OSuc lx x)  → ψ y )   → ψ ( record { lv = lx ; ord = OSuc lx x } ) )
  →  ∀ (x : Ordinal)  → ψ x
TransFinite {n} {m} {ψ} caseΦ caseOSuc x = proj1 (TransFinite1 (lv x) (ord x) ) where
  TransFinite1 : (lx : ℕ) (ox : OrdinalD lx ) → ψ (ordinal lx ox) ∧ ( ( (x : Ordinal {suc n} ) → x o< ordinal lx ox  → ψ x ) )
  TransFinite1 Zero (Φ 0) = ⟪  caseΦ Zero lemma , lemma1 ⟫ where
      lemma : (x : Ordinal) → x o< ordinal Zero (Φ Zero) → ψ x
      lemma x (case1 ())
      lemma x (case2 ())
      lemma1 : (x : Ordinal) → x o< ordinal Zero (Φ Zero) → ψ x
      lemma1 x (case1 ())
      lemma1 x (case2 ())
  TransFinite1 (Suc lx) (Φ (Suc lx)) = ⟪ caseΦ (Suc lx) (λ x → lemma (lv x) (ord x)) , (λ x → lemma (lv x) (ord x)) ⟫ where
      lemma0 : (ly : ℕ) (oy : OrdinalD ly ) → ordinal ly oy  o< ordinal lx (Φ lx) → ψ (ordinal ly oy)
      lemma0 ly oy lt = proj2 ( TransFinite1 lx (Φ lx) ) (ordinal ly oy) lt
      lemma : (ly : ℕ) (oy : OrdinalD ly ) → ordinal ly oy  o< ordinal (Suc lx) (Φ (Suc lx)) → ψ (ordinal ly oy)
      lemma lx1 ox1            (case1 lt) with <-∨ lt
      lemma lx (Φ lx)          (case1 lt) | case1 refl = proj1 ( TransFinite1 lx (Φ lx) )
      lemma lx (Φ lx)          (case1 lt) | case2 lt1 = lemma0  lx (Φ lx) (case1 lt1)
      lemma lx (OSuc lx ox1)   (case1 lt) | case1 refl = caseOSuc lx ox1 lemma2 where
          lemma2 : (y : Ordinal) → (Suc (lv y) ≤ lx) ∨ (ord y d< OSuc lx ox1) → ψ y
          lemma2 y lt1 with osuc-≡< lt1
          lemma2 y lt1 | case1 refl = lemma lx ox1 (case1 a<sa)
          lemma2 y lt1 | case2 t = proj2 (TransFinite1 lx ox1) y t 
      lemma lx1 (OSuc lx1 ox1) (case1 lt) | case2 lt1 = caseOSuc lx1 ox1 lemma2 where
          lemma2 : (y : Ordinal) → (Suc (lv y) ≤ lx1) ∨ (ord y d< OSuc lx1 ox1) → ψ y
          lemma2 y lt2 with osuc-≡< lt2
          lemma2 y lt2 | case1 refl = lemma lx1 ox1 (ordtrans lt2 (case1 lt))
          lemma2 y lt2 | case2 (case1 lt3) = proj2 (TransFinite1 lx (Φ lx)) y (case1 (<-trans lt3 lt1 ))
          lemma2 y lt2 | case2 (case2 lt3) with d<→lv lt3
          ... | refl = proj2 (TransFinite1 lx (Φ lx)) y (case1 lt1)
  TransFinite1 lx (OSuc lx ox)  = ⟪ caseOSuc lx ox lemma , lemma ⟫ where
      lemma : (y : Ordinal) → y o< ordinal lx (OSuc lx ox) → ψ y
      lemma y lt with osuc-≡< lt
      lemma y lt | case1 refl = proj1 ( TransFinite1 lx ox ) 
      lemma y lt | case2 lt1 = proj2 ( TransFinite1 lx ox ) y lt1

OrdIrr : {n : Level } {x y : Ordinal {suc n} } {lt lt1 : x o< y} → lt ≡ lt1
OrdIrr {n} {ordinal lv₁ ord₁} {ordinal lv₂ ord₂} {case1 x} {case1 x₁} = cong case1 (NP.<-irrelevant _ _ )
OrdIrr {n} {ordinal lv₁ ord₁} {ordinal lv₂ ord₂} {case1 x} {case2 x₁} = ⊥-elim ( nat-≡< ( d<→lv x₁ ) x )
OrdIrr {n} {ordinal lv₁ ord₁} {ordinal lv₂ ord₂} {case2 x} {case1 x₁} = ⊥-elim ( nat-≡< ( d<→lv x ) x₁ )
OrdIrr {n} {ordinal lv₁ .(Φ lv₁)} {ordinal .lv₁ .(OSuc lv₁ _)} {case2 Φ<} {case2 Φ<} = refl
OrdIrr {n} {ordinal lv₁ (OSuc lv₁ a)} {ordinal .lv₁ (OSuc lv₁ b)} {case2 (s< x)} {case2 (s< x₁)} = cong (λ k → case2 (s< k)) (lemma1 _ _ x x₁) where
      lemma1 : {lx : ℕ} (a b : OrdinalD {suc n} lx) → (x y : a d< b ) → x ≡ y
      lemma1 {lx} .(Φ lx) .(OSuc lx _) Φ< Φ< = refl
      lemma1 {lx} (OSuc lx a) (OSuc lx b) (s< x) (s< y) = cong s< (lemma1 {lx} a b x y )

TransFinite3 : {n m : Level} { ψ : Ordinal {suc n} → Set m }
          → ( (x : Ordinal {suc n})  → ( (y : Ordinal {suc n}  ) → y o< x → ψ y ) → ψ x )
          →  ∀ (x : Ordinal {suc n} )  → ψ x
TransFinite3 {n} {m} {ψ} ind x = TransFinite {n} {m} {ψ} caseΦ caseOSuc x where
        caseΦ : (lx : ℕ) → ((x₁ : Ordinal {suc n}) → x₁ o< ordinal lx (Φ lx) → ψ x₁) →
            ψ (record { lv = lx ; ord = Φ lx })
        caseΦ lx prev = ind (ordinal lx (Φ lx) ) prev
        caseOSuc :  (lx : ℕ) (x₁ : OrdinalD lx) → ((y : Ordinal) → y o< ordinal lx (OSuc lx x₁) → ψ y) →
            ψ (record { lv = lx ; ord = OSuc lx x₁ })
        caseOSuc lx ox prev = ind (ordinal lx (OSuc lx ox)) prev 

-- TP : {n m l : Level} → {Q : Ordinal {suc n} → Set m} {P : { x y : Ordinal {suc n} } → Q x → Q y → Set l}  
--     → ( ind : (x : Ordinal {suc n})  → ( (y : Ordinal  {suc n} ) → y o< x → Q y ) → Q x )                                                                 
--     → ( (x : Ordinal {suc n} )  → ( prev : (y : Ordinal {suc n} ) → y o< x → Q y ) → {y : Ordinal {suc n}} → (y<x : y o< x)  → P (prev y y<x) (ind x prev)  )  
--     →  {x z : Ordinal {suc n} } → (z≤x : z o< osuc x ) → P (TransFinite3 {n} {m} { λ x → Q x } {!!} x  )  {!!} -- P (TransFinite {?} ind z) (TransFinite {?} ind x )
-- TP = ?
 

open import Ordinals 

C-Ordinal : {n : Level} →  Ordinals {suc n} 
C-Ordinal {n} = record {
     Ordinal = Ordinal {suc n}
   ; o∅ = o∅
   ; osuc = osuc
   ; _o<_ = _o<_
   ; isOrdinal = record {
       ordtrans = ordtrans
     ; trio< = trio<
     ; ¬x<0 = ¬x<0 
     ; <-osuc = <-osuc
     ; osuc-≡< = osuc-≡<
     ; TransFinite = TransFinite2
     ; o<-irr = OrdIrr
     ; Oprev-p  = Oprev-p 
   } --
   -- isNext = record {
   --     x<nx = x<nx 
   --   ; osuc<nx = λ {x} {y} → osuc<nx {x} {y}
   --   -- ; ¬nx<nx = ¬nx<nx 
   -- }
  } where
     next : Ordinal {suc n} → Ordinal {suc n}
     next (ordinal lv ord) = ordinal (Suc lv) (Φ (Suc lv))
     x<nx :    { y : Ordinal } → (y o< next y )
     x<nx = case1 a<sa
     osuc<nx : { x y : Ordinal } → x o< next y → osuc x o< next y 
     osuc<nx (case1 lt) = case1 lt 
     ¬nx<nx :  {x y : Ordinal} → y o< x → x o< next y →  ¬ ((z : Ordinal) → ¬ (x ≡ osuc z)) 
     ¬nx<nx {x} {y} = lemma2 x where
         lemma2 : (x : Ordinal) → y o< x → x o< next y → ¬ ((z : Ordinal) → ¬ x ≡ osuc z)
         lemma2 (ordinal Zero (Φ 0)) (case2 ()) (case1 (s≤s z≤n)) not
         lemma2 (ordinal Zero (OSuc 0 dx)) (case2 Φ<) (case1 (s≤s z≤n)) not = not _ refl
         lemma2 (ordinal Zero (OSuc 0 dx)) (case2 (s< x)) (case1 (s≤s z≤n)) not = not _ refl
         lemma2 (ordinal (Suc lx) (OSuc (Suc lx) ox)) y<x (case1 (s≤s (s≤s lt))) not = not _ refl
         lemma2 (ordinal (Suc lx) (Φ (Suc lx))) (case1 x) (case1 (s≤s (s≤s lt))) not = lemma3 x lt where
             lemma3 : {n l : ℕ} → (Suc (Suc n) ≤ Suc l) → l ≤ n → ⊥
             lemma3   (s≤s sn≤l) (s≤s l≤n) = lemma3 sn≤l l≤n
     open Oprev
     Oprev-p  : (x : Ordinal) → Dec ( Oprev (Ordinal {suc n})  osuc x )
     Oprev-p  (ordinal lv (Φ lv)) = no (λ not → lemma (oprev not) (oprev=x not) ) where
          lemma : (x : Ordinal) → osuc x ≡ (ordinal lv (Φ lv)) → ⊥
          lemma x ()
     Oprev-p  (ordinal lv (OSuc lv ox)) = yes record { oprev = ordinal lv ox ; oprev=x = refl }
     ord1 : Set (suc n)
     ord1 = Ordinal {suc n}
     TransFinite2 : { ψ : ord1  → Set (suc (suc n)) }
          → ( (x : ord1)  → ( (y : ord1  ) → y o< x → ψ y ) → ψ x )
          →  ∀ (x : ord1)  → ψ x
     TransFinite2 {ψ} ind x = TransFinite {n} {suc (suc n)} {ψ} caseΦ caseOSuc x where
        caseΦ : (lx : ℕ) → ((x₁ : Ordinal) → x₁ o< ordinal lx (Φ lx) → ψ x₁) →
            ψ (record { lv = lx ; ord = Φ lx })
        caseΦ lx prev = ind (ordinal lx (Φ lx) ) prev
        caseOSuc :  (lx : ℕ) (x₁ : OrdinalD lx) → ((y : Ordinal) → y o< ordinal lx (OSuc lx x₁) → ψ y) →
            ψ (record { lv = lx ; ord = OSuc lx x₁ })
        caseOSuc lx ox prev = ind (ordinal lx (OSuc lx ox)) prev 


-- H-Ordinal : {n : Level} → Ordinals {suc n} →  Ordinals {suc n}  →  Ordinals {suc n} 
-- H-Ordinal {n} O1 O2 = record {
--      Ordinal = Ordinals.Ordinal O1 ∧ Ordinals.Ordinal O2 
--   }
-- We may have an oridinal as proper subset  of an ordinal
--   then the internal ordinal become a set in the outer ordinal
