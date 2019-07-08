{-# OPTIONS --allow-unsolved-metas #-}

open import Level
module ordinal-definable where

open import zf
open import ordinal

open import Data.Nat renaming ( zero to Zero ; suc to Suc ;  ℕ to Nat ; _⊔_ to _n⊔_ ) 
open import  Relation.Binary.PropositionalEquality
open import Data.Nat.Properties 
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.Core

-- Ordinal Definable Set

record OD {n : Level}  : Set (suc n) where
  field
    def : (x : Ordinal {n} ) → Set n

open OD
open import Data.Unit

open Ordinal

-- Ordinal in OD ( and ZFSet )
Ord : { n : Level } → ( a : Ordinal {n} ) → OD {n}
Ord {n} a = record { def = λ y → y o< a }  

-- od∅ : {n : Level} → OD {n} 
-- od∅ {n} = record { def = λ _ → Lift n ⊥ }
od∅ : {n : Level} → OD {n} 
od∅ {n} = Ord o∅ 

record _==_ {n : Level} ( a b :  OD {n} ) : Set n where
  field
     eq→ : ∀ { x : Ordinal {n} } → def a x → def b x 
     eq← : ∀ { x : Ordinal {n} } → def b x → def a x 

id : {n : Level} {A : Set n} → A → A
id x = x

eq-refl : {n : Level} {  x :  OD {n} } → x == x
eq-refl {n} {x} = record { eq→ = id ; eq← = id }

open  _==_ 

eq-sym : {n : Level} {  x y :  OD {n} } → x == y → y == x
eq-sym eq = record { eq→ = eq← eq ; eq← = eq→ eq }

eq-trans : {n : Level} {  x y z :  OD {n} } → x == y → y == z → x == z
eq-trans x=y y=z = record { eq→ = λ t → eq→ y=z ( eq→ x=y  t) ; eq← = λ t → eq← x=y ( eq← y=z t) }

ord→od : {n : Level} → Ordinal {n} → OD {n} 
ord→od a = Ord a

o<→c<  : {n : Level} {x y : Ordinal {n} } → x o< y             → def (ord→od y) x 
o<→c< {n} {x} {y} lt = lt 

postulate      
  -- OD can be iso to a subset of Ordinal ( by means of Godel Set )
  od→ord : {n : Level} → OD {n} → Ordinal {n}
  c<→o<  : {n : Level} {x y : OD {n} }      → def y ( od→ord x ) → od→ord x o< od→ord y
  oiso   : {n : Level} {x : OD {n}}      → ord→od ( od→ord x ) ≡ x
  diso   : {n : Level} {x : Ordinal {n}} → od→ord ( ord→od x ) ≡ x
  -- supermum as Replacement Axiom
  sup-o  : {n : Level } → ( Ordinal {n} → Ordinal {n}) →  Ordinal {n}
  sup-o< : {n : Level } → { ψ : Ordinal {n} →  Ordinal {n}} → ∀ {x : Ordinal {n}} →  ψ x  o<  sup-o ψ 
  -- a property of supermum required in Power Set Axiom
  sup-x  : {n : Level } → ( Ordinal {n} → Ordinal {n}) →  Ordinal {n}
  sup-lb : {n : Level } → { ψ : Ordinal {n} →  Ordinal {n}} → {z : Ordinal {n}}  →  z o< sup-o ψ → z o< osuc (ψ (sup-x ψ))
  -- sup-lb : {n : Level } → ( ψ : Ordinal {n} →  Ordinal {n}) → ( ∀ {x : Ordinal {n}} →  ψx  o<  z ) →  z o< osuc ( sup-o ψ ) 

_∋_ : { n : Level } → ( a x : OD {n} ) → Set n
_∋_ {n} a x  = def a ( od→ord x )

_c<_ : { n : Level } → ( x a : OD {n} ) → Set n
x c< a = a ∋ x 

_c≤_ : {n : Level} →  OD {n} →  OD {n} → Set (suc n)
a c≤ b  = (a ≡ b)  ∨ ( b ∋ a )

def-subst : {n : Level } {Z : OD {n}} {X : Ordinal {n} }{z : OD {n}} {x : Ordinal {n} }→ def Z X → Z ≡ z  →  X ≡ x  →  def z x
def-subst df refl refl = df

sup-od : {n : Level } → ( OD {n} → OD {n}) →  OD {n}
sup-od ψ = ord→od ( sup-o ( λ x → od→ord (ψ (ord→od x ))) )

sup-c< : {n : Level } → ( ψ : OD {n} →  OD {n}) → ∀ {x : OD {n}} → def ( sup-od ψ ) (od→ord ( ψ x ))
sup-c< {n} ψ {x} = def-subst {n} {_} {_} {sup-od ψ} {od→ord ( ψ x )}
        ( o<→c< sup-o< ) refl (cong ( λ k → od→ord (ψ k) ) oiso)

∅1 : {n : Level} →  ( x : OD {n} )  → ¬ ( x c< od∅ {n} )
∅1 {n} x (case1 ())
∅1 {n} x (case2 ())

∅3 : {n : Level} →  { x : Ordinal {n}}  → ( ∀(y : Ordinal {n}) → ¬ (y o< x ) ) → x ≡ o∅ {n}
∅3 {n} {x} = TransFinite {n} c2 c3 x where
   c0 : Nat →  Ordinal {n}  → Set n
   c0 lx x = (∀(y : Ordinal {n}) → ¬ (y o< x))  → x ≡ o∅ {n}
   c2 : (lx : Nat) → c0 lx (record { lv = lx ; ord = Φ lx } )
   c2 Zero not = refl
   c2 (Suc lx) not with not ( record { lv = lx ; ord = Φ lx } )
   ... | t with t (case1 ≤-refl )
   c2 (Suc lx) not | t | ()
   c3 : (lx : Nat) (x₁ : OrdinalD lx) → c0 lx  (record { lv = lx ; ord = x₁ })  → c0 lx (record { lv = lx ; ord = OSuc lx x₁ })
   c3 lx (Φ .lx) d not with not ( record { lv = lx ; ord = Φ lx } )
   ... | t with t (case2 Φ< )
   c3 lx (Φ .lx) d not | t | ()
   c3 lx (OSuc .lx x₁) d not with not (  record { lv = lx ; ord = OSuc lx x₁ } )
   ... | t with t (case2 (s< s<refl ) )
   c3 lx (OSuc .lx x₁) d not | t | ()

transitive : {n : Level } { z y x : OD {suc n} } → z ∋ y → y ∋ x → z  ∋ x
transitive  {n} {z} {y} {x} z∋y x∋y  with  ordtrans ( c<→o< {suc n} {x} {y} x∋y ) (  c<→o< {suc n} {y} {z} z∋y ) 
... | t = lemma0 (lemma t) where
   lemma : ( od→ord x ) o< ( od→ord z ) → def ( ord→od ( od→ord z )) ( od→ord x)
   lemma xo<z = o<→c< xo<z
   lemma0 :  def ( ord→od ( od→ord z )) ( od→ord x) →  def z (od→ord x)
   lemma0 dz  = def-subst {suc n} { ord→od ( od→ord z )} { od→ord x} dz (oiso)  refl

∅5 : {n : Level} →  { x : Ordinal {n} }  → ¬ ( x  ≡ o∅ {n} ) → o∅ {n} o< x
∅5 {n} {record { lv = Zero ; ord = (Φ .0) }} not = ⊥-elim (not refl) 
∅5 {n} {record { lv = Zero ; ord = (OSuc .0 ord) }} not = case2 Φ<
∅5 {n} {record { lv = (Suc lv) ; ord = ord }} not = case1 (s≤s z≤n)

ord-iso : {n : Level} {y : Ordinal {n} } → record { lv = lv (od→ord (ord→od y)) ; ord = ord (od→ord (ord→od y)) } ≡ record { lv = lv y ; ord = ord y }
ord-iso = cong ( λ k → record { lv = lv k ; ord = ord k } ) diso

-- avoiding lv != Zero error
orefl : {n : Level} →  { x : OD {n} } → { y : Ordinal {n} } → od→ord x ≡ y → od→ord x ≡ y
orefl refl = refl

==-iso : {n : Level} →  { x y : OD {n} } → ord→od (od→ord x) == ord→od (od→ord y)  →  x == y
==-iso {n} {x} {y} eq = record {
      eq→ = λ d →  lemma ( eq→  eq (def-subst d (sym oiso) refl )) ;
      eq← = λ d →  lemma ( eq←  eq (def-subst d (sym oiso) refl ))  }
        where
           lemma : {x : OD {n} } {z : Ordinal {n}} → def (ord→od (od→ord x)) z → def x z
           lemma {x} {z} d = def-subst d oiso refl

=-iso : {n : Level } {x y : OD {suc n} } → (x == y) ≡ (ord→od (od→ord x) == y)
=-iso {_} {_} {y} = cong ( λ k → k == y ) (sym oiso)

ord→== : {n : Level} →  { x y : OD {n} } → od→ord x ≡  od→ord y →  x == y
ord→== {n} {x} {y} eq = ==-iso (lemma (od→ord x) (od→ord y) (orefl eq)) where
   lemma : ( ox oy : Ordinal {n} ) → ox ≡ oy →  (ord→od ox) == (ord→od oy)
   lemma ox ox  refl = eq-refl

o≡→== : {n : Level} →  { x y : Ordinal {n} } → x ≡  y →  ord→od x == ord→od y
o≡→== {n} {x} {.x} refl = eq-refl

>→¬< : {x y : Nat  } → (x < y ) → ¬ ( y < x )
>→¬< (s≤s x<y) (s≤s y<x) = >→¬< x<y y<x

c≤-refl : {n : Level} →  ( x : OD {n} ) → x c≤ x
c≤-refl x = case1 refl

o<→o> : {n : Level} →  { x y : OD {n} } →  (x == y) → (od→ord x ) o< ( od→ord y) → ⊥
o<→o> {n} {x} {y} record { eq→ = xy ; eq← = yx } (case1 lt) with
     yx (def-subst {n} {ord→od (od→ord y)} {od→ord x} (o<→c< (case1 lt )) oiso refl )
... | oyx with o<¬≡ refl (c<→o< {n} {x} oyx )
... | ()
o<→o> {n} {x} {y} record { eq→ = xy ; eq← = yx } (case2 lt) with
     yx (def-subst {n} {ord→od (od→ord y)} {od→ord x} (o<→c< (case2 lt )) oiso refl )
... | oyx with o<¬≡ refl (c<→o< {n} {x} oyx )
... | ()

==→o≡ : {n : Level} →  { x y : Ordinal {suc n} } → ord→od x == ord→od y →  x ≡ y 
==→o≡ {n} {x} {y} eq with trio< {n} x y
==→o≡ {n} {x} {y} eq | tri< a ¬b ¬c = ⊥-elim ( o<→o> eq (o<-subst a (sym ord-iso) (sym ord-iso )))
==→o≡ {n} {x} {y} eq | tri≈ ¬a b ¬c = b
==→o≡ {n} {x} {y} eq | tri> ¬a ¬b c = ⊥-elim ( o<→o> (eq-sym eq) (o<-subst c (sym ord-iso) (sym ord-iso )))

≡-def : {n : Level} →  { x : Ordinal {suc n} } → x ≡ od→ord (record { def = λ z → z o< x } )
≡-def {n} {x} = ==→o≡ {n} (subst (λ k → ord→od x == k ) (sym oiso) lemma ) where
    lemma :  ord→od x == record { def = λ z → z o< x }
    eq→ lemma {w} z = subst₂ (λ k j → k o< j ) diso refl (subst (λ k → (od→ord ( ord→od w)) o< k ) diso t ) where 
        t : (od→ord ( ord→od w)) o< (od→ord (ord→od x))
        t = c<→o< {suc n} {ord→od w} {ord→od x} (def-subst {suc n} {_} {_} {ord→od x} {_} z refl (sym diso))
    eq← lemma {w} z = def-subst {suc n} {_} {_} {ord→od x} {w} ( o<→c< {suc n} {_} {_} z ) refl refl

od≡-def : {n : Level} →  { x : Ordinal {suc n} } → ord→od x ≡ record { def = λ z → z o< x } 
od≡-def {n} {x} = subst (λ k  → ord→od x ≡ k ) oiso (cong ( λ k → ord→od k ) (≡-def {n} {x} ))

==→o≡1 : {n : Level} →  { x y : OD {suc n} } → x == y →  od→ord x ≡ od→ord y 
==→o≡1 eq = ==→o≡ (subst₂ (λ k j → k == j ) (sym oiso) (sym oiso) eq )

==-def-l : {n : Level } {x y : Ordinal {suc n} } { z : OD {suc n} }→ (ord→od x == ord→od y) → def z x → def z y
==-def-l {n} {x} {y} {z} eq z>x = subst ( λ k → def z k ) (==→o≡ eq) z>x

==-def-r : {n : Level } {x y : OD {suc n} } { z : Ordinal {suc n} }→ (x == y) → def x z → def y z
==-def-r {n} {x} {y} {z} eq z>x = subst (λ k → def k z ) (subst₂ (λ j k → j ≡ k ) oiso oiso (cong (λ k → ord→od k) (==→o≡1 eq))) z>x  

∋→o< : {n : Level} →  { a x : OD {suc n} } → a ∋ x → od→ord x o< od→ord a
∋→o< {n} {a} {x} lt = t where
         t : (od→ord x) o< (od→ord a)
         t = c<→o< {suc n} {x} {a} lt 

o<∋→ : {n : Level} →  { a x : OD {suc n} } → od→ord x o< od→ord a → a ∋ x 
o<∋→ {n} {a} {x} lt = subst₂ (λ k j → def k j ) oiso refl t  where
         t : def (ord→od (od→ord a)) (od→ord x)
         t = o<→c< {suc n} {od→ord x} {od→ord a} lt 

o∅≡od∅ : {n : Level} → ord→od (o∅ {suc n}) ≡ od∅ {suc n}
o∅≡od∅ {n} with trio< {n} (o∅ {suc n}) (od→ord (od∅ {suc n} ))
o∅≡od∅ {n} | tri< a ¬b ¬c = ⊥-elim (lemma a) where
    lemma :  o∅ {suc n } o< (od→ord (od∅ {suc n} )) → ⊥
    lemma lt with def-subst (o<→c< lt) oiso refl
    lemma lt | case1 ()
    lemma lt | case2 ()
o∅≡od∅ {n} | tri≈ ¬a b ¬c = trans (cong (λ k → ord→od k ) b ) oiso
o∅≡od∅ {n} | tri> ¬a ¬b c = ⊥-elim (¬x<0 c)

o<→¬== : {n : Level} →  { x y : OD {n} } → (od→ord x ) o< ( od→ord y) →  ¬ (x == y )
o<→¬== {n} {x} {y} lt eq = o<→o> eq lt

o<→¬c> : {n : Level} →  { x y : OD {n} } → (od→ord x ) o< ( od→ord y) →  ¬ (y c< x )
o<→¬c> {n} {x} {y} olt clt = o<> olt (c<→o< clt ) where

o≡→¬c< : {n : Level} →  { x y : OD {n} } →  (od→ord x ) ≡ ( od→ord y) →   ¬ x c< y
o≡→¬c< {n} {x} {y} oeq lt  = o<¬≡   (orefl oeq ) (c<→o< lt) 

tri-c< : {n : Level} →  Trichotomous _==_ (_c<_ {suc n})
tri-c< {n} x y with trio< {n} (od→ord x) (od→ord y) 
tri-c< {n} x y | tri< a ¬b ¬c = tri< (def-subst (o<→c< a) oiso refl) (o<→¬== a) ( o<→¬c> a )
tri-c< {n} x y | tri≈ ¬a b ¬c = tri≈ (o≡→¬c< b) (ord→== b) (o≡→¬c< (sym b))
tri-c< {n} x y | tri> ¬a ¬b c = tri>  ( o<→¬c> c) (λ eq → o<→¬== c (eq-sym eq ) ) (def-subst (o<→c< c) oiso refl)

c<> : {n : Level } { x y : OD {suc n}} → x c<  y  → y c< x  →  ⊥
c<> {n} {x} {y} x<y y<x with tri-c< x y
c<> {n} {x} {y} x<y y<x | tri< a ¬b ¬c = ¬c y<x
c<> {n} {x} {y} x<y y<x | tri≈ ¬a b ¬c = o<→o> b ( c<→o< x<y )
c<> {n} {x} {y} x<y y<x | tri> ¬a ¬b c = ¬a x<y

∅< : {n : Level} →  { x y : OD {n} } → def x (od→ord y ) → ¬ (  x  == od∅ {n} )
∅< {n} {x} {y} d eq with eq→ eq d
∅< {n} {x} {y} d eq | case1 ()
∅< {n} {x} {y} d eq | case2 ()
       
∅6 : {n : Level} →  { x : OD {suc n} }  → ¬ ( x ∋ x )    --  no Russel paradox
∅6 {n} {x} x∋x = c<> {n} {x} {x} x∋x x∋x

def-iso : {n : Level} {A B : OD {n}} {x y : Ordinal {n}} → x ≡ y  → (def A y → def B y)  → def A x → def B x
def-iso refl t = t

is-∋ : {n : Level} →  ( x y : OD {suc n} ) → Dec ( x ∋ y )
is-∋ {n} x y with tri-c< x y
is-∋ {n} x y | tri< a ¬b ¬c = no ¬c
is-∋ {n} x y | tri≈ ¬a b ¬c = no ¬c
is-∋ {n} x y | tri> ¬a ¬b c = yes c

is-o∅ : {n : Level} →  ( x : Ordinal {suc n} ) → Dec ( x ≡ o∅ {suc n} )
is-o∅ {n} record { lv = Zero ; ord = (Φ .0) } = yes refl
is-o∅ {n} record { lv = Zero ; ord = (OSuc .0 ord₁) } = no ( λ () )
is-o∅ {n} record { lv = (Suc lv₁) ; ord = ord } = no (λ())

open _∧_

--
-- This menas OD is Ordinal here
--
¬∅=→∅∈ :  {n : Level} →  { x : OD {suc n} } → ¬ (  x  == od∅ {suc n} ) → x ∋ od∅ {suc n} 
¬∅=→∅∈  {n} {x} ne = def-subst (lemma (od→ord x) (subst (λ k → ¬ (k == od∅ {suc n} )) (sym oiso) ne )) oiso refl where
     lemma : (ox : Ordinal {suc n}) →  ¬ (ord→od  ox  == od∅ {suc n} ) → ord→od ox ∋ od∅ {suc n}
     lemma ox ne with is-o∅ ox
     lemma ox ne | yes refl with ne ( ord→== lemma1 ) where
         lemma1 : od→ord (ord→od o∅) ≡ od→ord od∅
         lemma1 = cong ( λ k → od→ord k ) o∅≡od∅
     lemma o∅ ne | yes refl | ()
     lemma ox ne | no ¬p = subst ( λ k → def (ord→od ox) (od→ord k) ) o∅≡od∅ (o<→c< (subst (λ k → k o< ox ) (sym diso) (∅5 ¬p)) )  

-- open import Relation.Binary.HeterogeneousEquality as HE using (_≅_ ) 
-- postulate f-extensionality : { n : Level}  → Relation.Binary.PropositionalEquality.Extensionality (suc n) (suc (suc n))

csuc :  {n : Level} →  OD {suc n} → OD {suc n}
csuc x = Ord ( osuc ( od→ord x ))

in-codomain : {n : Level} → (X : OD {suc n} ) → ( ψ : OD {suc n} → OD {suc n} ) → OD {suc n}
in-codomain {n} X ψ = record { def = λ x → ¬ ( (y : Ordinal {suc n}) → ¬ ( def X y ∧  ( x ≡ od→ord (ψ (Ord y )))))  }

-- Power Set of X ( or constructible by λ y → def X (od→ord y )

ZFSubset : {n : Level} → (A x : OD {suc n} ) → OD {suc n}
ZFSubset A x =  record { def = λ y → def A y ∧  def x y }  

Def :  {n : Level} → (A :  OD {suc n}) → OD {suc n}
Def {n} A = Ord ( sup-o ( λ x → od→ord ( ZFSubset A (ord→od x )) ) )  

-- Constructible Set on α
L : {n : Level} → (α : Ordinal {suc n}) → OD {suc n}
L {n}  record { lv = Zero ; ord = (Φ .0) } = od∅
L {n}  record { lv = lx ; ord = (OSuc lv ox) } = Def ( L {n} ( record { lv = lx ; ord = ox } ) ) 
L {n}  record { lv = (Suc lx) ; ord = (Φ (Suc lx)) } = -- Union ( L α )
    record { def = λ y → osuc y o< (od→ord (L {n}  (record { lv = lx ; ord = Φ lx }) )) }

Ord→ZF : {n : Level} → ZF {suc (suc n)} {suc n}
Ord→ZF {n}  = record { 
    ZFSet = OD {suc n}
    ; _∋_ = _∋_ 
    ; _≈_ = _==_ 
    ; ∅  = od∅
    ; _,_ = _,_
    ; Union = Union
    ; Power = Power
    ; Select = Select
    ; Replace = Replace
    ; infinite = ord→od ( record { lv = Suc Zero ; ord = Φ 1 } )
    ; isZF = isZF 
 } where
    Select : OD {suc n} → (OD {suc n} → Set (suc n) ) → OD {suc n}
    Select X ψ = record { def = λ x →  ( def X  x ∧  ψ ( ord→od x )) } 
    _,_ : OD {suc n} → OD {suc n} → OD {suc n}
    x , y = record { def = λ z → z o< (omax (od→ord x) (od→ord y)) }
    _∩_ : ( A B : OD {suc n} ) → OD
    A ∩ B = record { def = λ x → def A x  ∧ def B x }
    Replace : OD {suc n} → (OD {suc n} → OD {suc n} ) → OD {suc n}
    Replace X ψ = record { def = λ x → (x o< sup-o ( λ x → od→ord (ψ (ord→od x )))) ∧ def (in-codomain X ψ) x }
    Union : OD {suc n} → OD {suc n}
    Union U = record { def = λ y → osuc y o< (od→ord U) }
    -- power : ∀ X ∃ A ∀ t ( t ∈ A ↔ ( ∀ {x} → t ∋ x →  X ∋ x )
    Power : OD {suc n} → OD {suc n}
    Power A = Def A
    ZFSet = OD {suc n}
    _∈_ : ( A B : ZFSet  ) → Set (suc n)
    A ∈ B = B ∋ A
    _⊆_ : ( A B : ZFSet  ) → ∀{ x : ZFSet } →  Set (suc n)
    _⊆_ A B {x} = A ∋ x →  B ∋ x
    -- _∪_ : ( A B : ZFSet  ) → ZFSet
    -- A ∪ B = Select (A , B) (  λ x → (A ∋ x)  ∨ ( B ∋ x ) )
    infixr  200 _∈_
    -- infixr  230 _∩_ _∪_
    infixr  220 _⊆_
    isZF : IsZF (OD {suc n})  _∋_  _==_ od∅ _,_ Union Power Select Replace (ord→od ( record { lv = Suc Zero ; ord = Φ 1} ))
    isZF = record {
           isEquivalence  = record { refl = eq-refl ; sym = eq-sym; trans = eq-trans }
       ;   pair  = pair
       ;   union-u = λ _ z _ → csuc z
       ;   union→ = union→
       ;   union← = union←
       ;   empty = empty
       ;   power→ = power→
       ;   power← = power← 
       ;   extensionality = extensionality
       ;   minimul = minimul
       ;   regularity = regularity
       ;   infinity∅ = infinity∅
       ;   infinity = λ _ → infinity
       ;   selection = λ {ψ} {X} {y} → selection {ψ} {X} {y}
       ;   replacement← = replacement←
       ;   replacement→ = replacement→
     } where
         pair : (A B : OD {suc n} ) → ((A , B) ∋ A) ∧  ((A , B) ∋ B)
         proj1 (pair A B ) = omax-x {n} (od→ord A) (od→ord B)
         proj2 (pair A B ) = omax-y {n} (od→ord A) (od→ord B)
         empty : (x : OD {suc n} ) → ¬  (od∅ ∋ x)
         empty x (case1 ())
         empty x (case2 ())
         ---
         --- ZFSubset A x =  record { def = λ y → def A y ∧  def x y }                   subset of A
         --- Power X = ord→od ( sup-o ( λ x → od→ord ( ZFSubset A (ord→od x )) ) )       Power X is a sup of all subset of A
         --
         --  if Power A ∋ t, from a propertiy of minimum sup there is osuc ZFSubset A ∋ t 
         --    then ZFSubset A ≡ t or ZFSubset A ∋ t. In the former case ZFSubset A ∋ x implies A ∋ x
         --    In case of later, ZFSubset A ∋ t and t ∋ x implies ZFSubset A ∋ x by transitivity
         --
         power→ : (A t : OD) → Power A ∋ t → {x : OD} → t ∋ x → A ∋ x
         power→ A t P∋t {x} t∋x = proj1 lemma-s where
              minsup :  OD
              minsup =  ZFSubset A ( ord→od ( sup-x (λ x → od→ord ( ZFSubset A (ord→od x))))) 
              lemma-t : csuc minsup ∋ t
              lemma-t = o<→c< (o<-subst (sup-lb (o<-subst (c<→o< P∋t) refl diso )) refl refl ) 
              lemma-s : ZFSubset A ( ord→od ( sup-x (λ x → od→ord ( ZFSubset A (ord→od x)))))  ∋ x
              lemma-s with osuc-≡< ( o<-subst (c<→o< lemma-t ) refl diso  )
              lemma-s | case1 eq = def-subst ( ==-def-r (o≡→== eq) (subst (λ k → def k (od→ord x)) (sym oiso) t∋x ) ) oiso refl
              lemma-s | case2 lt = transitive {n} {minsup} {t} {x} (def-subst (o<→c< lt) oiso refl ) t∋x
         -- 
         -- we have t ∋ x → A ∋ x means t is a subset of A, that is ZFSubset A t == t
         -- Power A is a sup of ZFSubset A t, so Power A ∋ t
         -- 
         power← : (A t : OD) → ({x : OD} → (t ∋ x → A ∋ x)) → Power A ∋ t
         power← A t t→A  = def-subst {suc n} {_} {_} {Power A} {od→ord t}
                  ( o<→c< {suc n} {od→ord (ZFSubset A (ord→od (od→ord t)) )} {sup-o (λ x → od→ord (ZFSubset A (ord→od x)))}
                      lemma ) refl lemma1 where
              lemma-eq :  ZFSubset A t == t
              eq→ lemma-eq {z} w = proj2 w 
              eq← lemma-eq {z} w = record { proj2 = w  ;
                 proj1 = def-subst {suc n} {_} {_} {A} {z} ( t→A (def-subst {suc n} {_} {_} {t} {od→ord (ord→od z)} w refl (sym diso) )) refl diso  }
              lemma1 : od→ord (ZFSubset A (ord→od (od→ord t))) ≡ od→ord t
              lemma1 = subst (λ k → od→ord (ZFSubset A k) ≡ od→ord t ) (sym oiso) (==→o≡1 (lemma-eq))
              lemma :  od→ord (ZFSubset A (ord→od (od→ord t)) ) o< sup-o (λ x → od→ord (ZFSubset A (ord→od x)))
              lemma = sup-o<   
         union-lemma-u : {X z : OD {suc n}} → (U>z : Union X ∋ z ) → csuc z ∋ z
         union-lemma-u {X} {z} U>z = lemma <-osuc where
             lemma : {oz ooz : Ordinal {suc n}} → oz o< ooz → def (ord→od ooz) oz
             lemma {oz} {ooz} lt = def-subst {suc n} {ord→od  ooz} (o<→c< lt) refl refl
         union→ :  (X z u : OD) → (X ∋ u) ∧ (u ∋ z) → Union X ∋ z
         union→ X y u xx with trio< ( od→ord u ) ( osuc ( od→ord y ))
         union→ X y u xx | tri< a ¬b ¬c with  osuc-< a (c<→o< (proj2 xx))
         union→ X y u xx | tri< a ¬b ¬c | ()
         union→ X y u xx | tri≈ ¬a b ¬c = lemma b (c<→o< (proj1 xx )) where
             lemma : {oX ou ooy : Ordinal {suc n}} →  ou ≡ ooy  → ou o< oX   → ooy  o< oX
             lemma refl lt = lt
         union→ X y u xx | tri> ¬a ¬b c = ordtrans {suc n} {osuc ( od→ord y )} {od→ord u} {od→ord X} c ( c<→o< (proj1 xx )) 
         union← :  (X z : OD) (X∋z : Union X ∋ z) → (X ∋ csuc z) ∧ (csuc z ∋ z )
         union← X z X∋z = record { proj1 = def-subst {suc n} {_} {_} {X} {od→ord (csuc z )} (o<→c< X∋z) oiso (sym diso) ; proj2 = union-lemma-u X∋z } 
         ψiso :  {ψ : OD {suc n} → Set (suc n)} {x y : OD {suc n}} → ψ x → x ≡ y   → ψ y
         ψiso {ψ} t refl = t
         selection : {ψ : OD → Set (suc n)} {X y : OD} → ((X ∋ y) ∧ ψ y) ⇔ (Select X ψ ∋ y)
         selection {ψ} {X} {y} = record {
              proj1 = λ cond → record { proj1 = proj1 cond ; proj2 = ψiso {ψ} (proj2 cond) (sym oiso)  }
            ; proj2 = λ select → record { proj1 = proj1 select  ; proj2 =  ψiso {ψ} (proj2 select) oiso  }
           }
         replacement← : {ψ : OD → OD} (X x : OD) →  X ∋ x → Replace X ψ ∋ ψ x
         replacement← {ψ} X x lt = record { proj1 =  sup-c< ψ {x} ; proj2 = lemma } where
             lemma : def (in-codomain X ψ) (od→ord (ψ x))
             lemma not = ⊥-elim ( not ( od→ord x ) (record { proj1 = lt ; proj2 = cong (λ k → od→ord (ψ k)) (sym oiso)} ) )
         replacement→ : {ψ : OD → OD} (X x : OD) → (lt : Replace X ψ ∋ x) → ¬ ( (y : OD) → ¬ (x == ψ y))
         replacement→ {ψ} X x lt = contra-position lemma (lemma2 (proj2 lt)) where
            lemma2 :  ¬ ((y : Ordinal) → ¬ def X y ∧ ((od→ord x) ≡ od→ord (ψ (Ord y))))
                    → ¬ ((y : Ordinal) → ¬ def X y ∧ (ord→od (od→ord x) == ψ (Ord y)))
            lemma2 not not2  = not ( λ y d →  not2 y (record { proj1 = proj1 d ; proj2 = lemma3 (proj2 d)})) where
                lemma3 : {y : Ordinal } → (od→ord x ≡ od→ord (ψ (Ord y))) → (ord→od (od→ord x) == ψ (Ord y))  
                lemma3 {y} eq = subst (λ k  → ord→od (od→ord x) == k ) oiso (o≡→== eq )
            lemma :  ( (y : OD) → ¬ (x == ψ y)) → ( (y : Ordinal) → ¬ def X y ∧ (ord→od (od→ord x) == ψ (Ord y)) )
            lemma not y not2 = not (Ord y) (subst (λ k → k == ψ (Ord y)) oiso  ( proj2 not2 ))
         ∅-iso :  {x : OD} → ¬ (x == od∅) → ¬ ((ord→od (od→ord x)) == od∅) 
         ∅-iso {x} neq = subst (λ k → ¬ k) (=-iso {n} ) neq  
         minimul : (x : OD {suc n} ) → ¬ (x == od∅ )→ OD {suc n} 
         minimul x  not = od∅   
         regularity :  (x : OD) (not : ¬ (x == od∅)) →
            (x ∋ minimul x not) ∧ (Select (minimul x not) (λ x₁ → (minimul x not ∋ x₁) ∧ (x ∋ x₁)) == od∅)
         proj1 (regularity x not ) = ¬∅=→∅∈ not 
         proj2 (regularity x not ) = record { eq→ = reg ; eq← = lemma } where
            lemma : {ox : Ordinal} → def od∅ ox → def (Select (minimul x not) (λ y → (minimul x not ∋ y) ∧ (x ∋ y))) ox
            lemma (case1 ())
            lemma (case2 ())
            reg : {y : Ordinal} → def (Select (minimul x not) (λ x₂ → (minimul x not ∋ x₂) ∧ (x ∋ x₂))) y → def od∅ y
            reg {y} t = ⊥-elim ( ¬x<0 (proj1 (proj2 t )) )
         extensionality : {A B : OD {suc n}} → ((z : OD) → (A ∋ z) ⇔ (B ∋ z)) → A == B
         eq→ (extensionality {A} {B} eq ) {x} d = def-iso {suc n} {A} {B} (sym diso) (proj1 (eq (ord→od x))) d  
         eq← (extensionality {A} {B} eq ) {x} d = def-iso {suc n} {B} {A} (sym diso) (proj2 (eq (ord→od x))) d  
         xx-union : {x  : OD {suc n}} → (x , x) ≡ record { def = λ z → z o< osuc (od→ord x) }
         xx-union {x} = cong ( λ k → record { def = λ z → z o< k } ) (omxx (od→ord x))
         xxx-union : {x  : OD {suc n}} → (x , (x , x)) ≡ record { def = λ z → z o< osuc (osuc (od→ord x))}
         xxx-union {x} = cong ( λ k → record { def = λ z → z o< k } ) lemma where
             lemma1 : {x  : OD {suc n}} → od→ord x o< od→ord (x , x)
             lemma1 {x} = c<→o< ( proj1 (pair x x ) )
             lemma2 : {x  : OD {suc n}} → od→ord (x , x) ≡ osuc (od→ord x)
             lemma2 = trans ( cong ( λ k →  od→ord k ) xx-union ) (sym ≡-def)
             lemma : {x  : OD {suc n}} → omax (od→ord x) (od→ord (x , x)) ≡ osuc (osuc (od→ord x))
             lemma {x} = trans ( sym ( omax< (od→ord x) (od→ord (x , x)) lemma1 ) ) ( cong ( λ k → osuc k ) lemma2 )
         uxxx-union : {x  : OD {suc n}} → Union (x , (x , x)) ≡ record { def = λ z → osuc z o< osuc (osuc (od→ord x)) }
         uxxx-union {x} = cong ( λ k → record { def = λ z → osuc z o< k } ) lemma where
             lemma : od→ord (x , (x , x)) ≡ osuc (osuc (od→ord x))
             lemma = trans ( cong ( λ k → od→ord k ) xxx-union ) (sym ≡-def )
         uxxx-2 : {x  : OD {suc n}} → record { def = λ z → osuc z o< osuc (osuc (od→ord x)) } == record { def = λ z → z o< osuc (od→ord x) }
         eq→ ( uxxx-2 {x} ) {m} lt = proj1 (osuc2 m (od→ord x)) lt
         eq← ( uxxx-2 {x} ) {m} lt = proj2 (osuc2 m (od→ord x)) lt
         uxxx-ord : {x  : OD {suc n}} → od→ord (Union (x , (x , x))) ≡ osuc (od→ord x)
         uxxx-ord {x} = trans (cong (λ k →  od→ord k ) uxxx-union) (==→o≡ (subst₂ (λ j k → j == k ) (sym oiso) (sym od≡-def ) uxxx-2 )) 
         omega = record { lv = Suc Zero ; ord = Φ 1 }
         infinite : OD {suc n}
         infinite = ord→od ( omega )
         infinity∅ : ord→od ( omega ) ∋ od∅ {suc n}
         infinity∅ = def-subst {suc n} {_} {o∅} {infinite} {od→ord od∅}
              (o<→c< ( case1 (s≤s z≤n )))  refl (subst ( λ k → ( k ≡ od→ord od∅ )) diso (cong (λ k →  od→ord k) o∅≡od∅ ))
         infinite∋x : (x : OD) → infinite ∋ x → od→ord x o< omega
         infinite∋x x lt = subst (λ k → od→ord x o< k ) diso t where
              t  : od→ord x o< od→ord (ord→od (omega))
              t  = ∋→o< {n} {infinite} {x} lt
         infinite∋uxxx : (x : OD) → osuc (od→ord x) o< omega → infinite ∋ Union (x , (x , x ))
         infinite∋uxxx x lt = o<∋→ t where
              t  :  od→ord (Union (x , (x , x))) o< od→ord (ord→od (omega))
              t  = subst (λ k →  od→ord (Union (x , (x , x))) o< k ) (sym diso ) ( subst ( λ k → k o< omega ) ( sym  (uxxx-ord {x} ) ) lt ) 
         infinity : (x : OD) → infinite ∋ x → infinite ∋ Union (x , (x , x ))
         infinity x lt = infinite∋uxxx x ( lemma (od→ord x) (infinite∋x x lt ))   where
              lemma : (ox : Ordinal {suc n} ) → ox o< omega → osuc ox o< omega 
              lemma record { lv = Zero ; ord = (Φ .0) } (case1 (s≤s x)) = case1 (s≤s z≤n)
              lemma record { lv = Zero ; ord = (OSuc .0 ord₁) } (case1 (s≤s x)) = case1 (s≤s z≤n)
              lemma record { lv = (Suc lv₁) ; ord = (Φ .(Suc lv₁)) } (case1 (s≤s ()))
              lemma record { lv = (Suc lv₁) ; ord = (OSuc .(Suc lv₁) ord₁) } (case1 (s≤s ()))
              lemma record { lv = 1 ; ord = (Φ 1) } (case2 c2) with d<→lv c2
              lemma record { lv = (Suc Zero) ; ord = (Φ .1) } (case2 ()) | refl

