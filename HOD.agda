open import Level
module HOD where

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
open _∧_

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

⇔→== : {n : Level} {  x y :  OD {suc n} } → ( {z : Ordinal {suc n}} → def x z ⇔  def y z) → x == y 
eq→ ( ⇔→== {n} {x} {y}  eq ) {z} m = proj1 eq m 
eq← ( ⇔→== {n} {x} {y}  eq ) {z} m = proj2 eq m 

-- Ordinal in OD ( and ZFSet )
Ord : { n : Level } → ( a : Ordinal {n} ) → OD {n}
Ord {n} a = record { def = λ y → y o< a }  

od∅ : {n : Level} → OD {n} 
od∅ {n} = Ord o∅ 

postulate      
  -- OD can be iso to a subset of Ordinal ( by means of Godel Set )
  od→ord : {n : Level} → OD {n} → Ordinal {n}
  ord→od : {n : Level} → Ordinal {n} → OD {n} 
  c<→o<  : {n : Level} {x y : OD {n} }      → def y ( od→ord x ) → od→ord x o< od→ord y
  oiso   : {n : Level} {x : OD {n}}     → ord→od ( od→ord x ) ≡ x
  diso   : {n : Level} {x : Ordinal {n}} → od→ord ( ord→od x ) ≡ x
  -- we should prove this in agda, but simply put here
  ==→o≡ : {n : Level} →  { x y : OD {suc n} } → (x == y) → x ≡ y
  -- next assumption causes ∀ x ∋ ∅ . It menas only an ordinal becomes a set
  -- o<→c<  : {n : Level} {x y : Ordinal {n} } → x o< y             → def (ord→od y) x 
  -- supermum as Replacement Axiom
  sup-o  : {n : Level } → ( Ordinal {n} → Ordinal {n}) →  Ordinal {n}
  sup-o< : {n : Level } → { ψ : Ordinal {n} →  Ordinal {n}} → ∀ {x : Ordinal {n}} →  ψ x  o<  sup-o ψ 
  -- contra-position of mimimulity of supermum required in Power Set Axiom
  sup-x  : {n : Level } → ( Ordinal {n} → Ordinal {n}) →  Ordinal {n}
  sup-lb : {n : Level } → { ψ : Ordinal {n} →  Ordinal {n}} → {z : Ordinal {n}}  →  z o< sup-o ψ → z o< osuc (ψ (sup-x ψ))
  -- sup-lb : {n : Level } → ( ψ : Ordinal {n} →  Ordinal {n}) → ( ∀ {x : Ordinal {n}} →  ψx  o<  z ) →  z o< osuc ( sup-o ψ ) 
  minimul : {n : Level } → (x : OD {suc n} ) → ¬ (x == od∅ )→ OD {suc n} 
  -- this should be ¬ (x == od∅ )→ ∃ ox → x ∋ Ord ox  ( minimum of x )
  x∋minimul : {n : Level } → (x : OD {suc n} ) → ( ne : ¬ (x == od∅ ) ) → def x ( od→ord ( minimul x ne ) )
  minimul-1 : {n : Level } → (x : OD {suc n} ) → ( ne : ¬ (x == od∅ ) ) → (y : OD {suc n}) → ¬ ( def (minimul x ne) (od→ord y)) ∧ (def x (od→ord  y) )

_∋_ : { n : Level } → ( a x : OD {n} ) → Set n
_∋_ {n} a x  = def a ( od→ord x )

_c<_ : { n : Level } → ( x a : OD {n} ) → Set n
x c< a = a ∋ x 

_c≤_ : {n : Level} →  OD {n} →  OD {n} → Set (suc n)
a c≤ b  = (a ≡ b)  ∨ ( b ∋ a )

cseq : {n : Level} →  OD {n} →  OD {n}
cseq x = record { def = λ y → def x (osuc y) } where

def-subst : {n : Level } {Z : OD {n}} {X : Ordinal {n} }{z : OD {n}} {x : Ordinal {n} }→ def Z X → Z ≡ z  →  X ≡ x  →  def z x
def-subst df refl refl = df

sup-od : {n : Level } → ( OD {n} → OD {n}) →  OD {n}
sup-od ψ = Ord ( sup-o ( λ x → od→ord (ψ (ord→od x ))) )

sup-c< : {n : Level } → ( ψ : OD {n} →  OD {n}) → ∀ {x : OD {n}} → def ( sup-od ψ ) (od→ord ( ψ x ))
sup-c< {n} ψ {x} = def-subst {n} {_} {_} {Ord ( sup-o ( λ x → od→ord (ψ (ord→od x ))) )} {od→ord ( ψ x )}
        lemma refl (cong ( λ k → od→ord (ψ k) ) oiso) where
    lemma : od→ord (ψ (ord→od (od→ord x))) o< sup-o (λ x → od→ord (ψ (ord→od x)))
    lemma = subst₂ (λ j k → j o< k ) refl diso (o<-subst sup-o< refl (sym diso)  )

otrans : {n : Level} {a x : Ordinal {n} } → def (Ord a) x → { y : Ordinal {n} } → y o< x → def (Ord a) y
otrans {n} {a} {x} x<a {y} y<x = ordtrans y<x x<a

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

∋→o< : {n : Level} →  { a x : OD {suc n} } → a ∋ x → od→ord x o< od→ord a
∋→o< {n} {a} {x} lt = t where
         t : (od→ord x) o< (od→ord a)
         t = c<→o< {suc n} {x} {a} lt 

-- o∅≡od∅ : {n : Level} → ord→od (o∅ {suc n}) ≡ od∅ {suc n}

o<→¬c> : {n : Level} →  { x y : OD {n} } → (od→ord x ) o< ( od→ord y) →  ¬ (y c< x )
o<→¬c> {n} {x} {y} olt clt = o<> olt (c<→o< clt ) where

o≡→¬c< : {n : Level} →  { x y : OD {n} } →  (od→ord x ) ≡ ( od→ord y) →   ¬ x c< y
o≡→¬c< {n} {x} {y} oeq lt  = o<¬≡  (orefl oeq ) (c<→o< lt) 

∅0 : {n : Level} →  record { def = λ x →  Lift n ⊥ } == od∅ {n} 
eq→ ∅0 {w} (lift ())
eq← ∅0 {w} (case1 ())
eq← ∅0 {w} (case2 ())

∅< : {n : Level} →  { x y : OD {n} } → def x (od→ord y ) → ¬ (  x  == od∅ {n} )
∅< {n} {x} {y} d eq with eq→ (eq-trans eq (eq-sym ∅0) ) d
∅< {n} {x} {y} d eq | lift ()
       
∅6 : {n : Level} →  { x : OD {suc n} }  → ¬ ( x ∋ x )    --  no Russel paradox
∅6 {n} {x} x∋x = o<¬≡ refl ( c<→o< {suc n} {x} {x} x∋x )

def-iso : {n : Level} {A B : OD {n}} {x y : Ordinal {n}} → x ≡ y  → (def A y → def B y)  → def A x → def B x
def-iso refl t = t

is-o∅ : {n : Level} →  ( x : Ordinal {suc n} ) → Dec ( x ≡ o∅ {suc n} )
is-o∅ {n} record { lv = Zero ; ord = (Φ .0) } = yes refl
is-o∅ {n} record { lv = Zero ; ord = (OSuc .0 ord₁) } = no ( λ () )
is-o∅ {n} record { lv = (Suc lv₁) ; ord = ord } = no (λ())


-- open import Relation.Binary.HeterogeneousEquality as HE using (_≅_ ) 
-- postulate f-extensionality : { n : Level}  → Relation.Binary.PropositionalEquality.Extensionality (suc n) (suc (suc n))

in-codomain : {n : Level} → (X : OD {suc n} ) → ( ψ : OD {suc n} → OD {suc n} ) → OD {suc n}
in-codomain {n} X ψ = record { def = λ x → ¬ ( (y : Ordinal {suc n}) → ¬ ( def X y ∧  ( x ≡ od→ord (ψ (ord→od y )))))  }

-- Power Set of X ( or constructible by λ y → def X (od→ord y )

ZFSubset : {n : Level} → (A x : OD {suc n} ) → OD {suc n}
ZFSubset A x =  record { def = λ y → def A y ∧  def x y }   where

Def :  {n : Level} → (A :  OD {suc n}) → OD {suc n}
Def {n} A = Ord ( sup-o ( λ x → od→ord ( ZFSubset A (ord→od x )) ) )  

OrdSubset : {n : Level} → (A x : Ordinal {suc n} ) → ZFSubset (Ord A) (Ord x) ≡ Ord ( minα A x )
OrdSubset {n} A x = ==→o≡ ( record { eq→ = lemma1 ; eq← = lemma2 } ) where
  lemma1 :  {y : Ordinal} → def (ZFSubset (Ord A) (Ord x)) y → def (Ord (minα A x)) y
  lemma1 {y} s with trio< A x
  lemma1 {y} s | tri< a ¬b ¬c = proj1 s
  lemma1 {y} s | tri≈ ¬a refl ¬c = proj1 s
  lemma1 {y} s | tri> ¬a ¬b c = proj2 s
  lemma2 : {y : Ordinal} → def (Ord (minα A x)) y → def (ZFSubset (Ord A) (Ord x)) y
  lemma2 {y} lt with trio< A x
  lemma2 {y} lt | tri< a ¬b ¬c = record { proj1 = lt ; proj2 = ordtrans lt a }
  lemma2 {y} lt | tri≈ ¬a refl ¬c = record { proj1 = lt ; proj2 = lt }
  lemma2 {y} lt | tri> ¬a ¬b c = record { proj1 = ordtrans lt c ; proj2 = lt }

-- Constructible Set on α
-- Def X = record { def = λ y → ∀ (x : OD ) → y < X ∧ y <  od→ord x } 
-- L (Φ 0) = Φ
-- L (OSuc lv n) = { Def ( L n )  } 
-- L (Φ (Suc n)) = Union (L α) (α < Φ (Suc n) )
L : {n : Level} → (α : Ordinal {suc n}) → OD {suc n}
L {n}  record { lv = Zero ; ord = (Φ .0) } = od∅
L {n}  record { lv = lx ; ord = (OSuc lv ox) } = Def ( L {n} ( record { lv = lx ; ord = ox } ) ) 
L {n}  record { lv = (Suc lx) ; ord = (Φ (Suc lx)) } = -- Union ( L α )
    cseq ( Ord (od→ord (L {n}  (record { lv = lx ; ord = Φ lx }))))

-- L0 :  {n : Level} → (α : Ordinal {suc n}) → α o< β → L (osuc α) ∋ L α
-- L1 :  {n : Level} → (α β : Ordinal {suc n}) → α o< β → ∀ (x : OD {suc n})  → L α ∋ x → L β ∋ x 

omega : { n : Level } → Ordinal {n}
omega = record { lv = Suc Zero ; ord = Φ 1 }

OD→ZF : {n : Level} → ZF {suc (suc n)} {suc n}
OD→ZF {n}  = record { 
    ZFSet = OD {suc n}
    ; _∋_ = _∋_ 
    ; _≈_ = _==_ 
    ; ∅  = od∅
    ; _,_ = _,_
    ; Union = Union
    ; Power = Power
    ; Select = Select
    ; Replace = Replace
    ; infinite = Ord omega
    ; isZF = isZF 
 } where
    ZFSet = OD {suc n}
    Select : (X : OD {suc n} ) → ((x : OD {suc n} ) → Set (suc n) ) → OD {suc n}
    Select X ψ = record { def = λ x →  ( def X  x ∧  ψ ( ord→od x )) }
    Replace : OD {suc n} → (OD {suc n} → OD {suc n} ) → OD {suc n}
    Replace X ψ = record { def = λ x → (x o< sup-o ( λ x → od→ord (ψ (ord→od x )))) ∧ def (in-codomain X ψ) x }
    _,_ : OD {suc n} → OD {suc n} → OD {suc n}
    x , y = Ord (omax (od→ord x) (od→ord y))
    _∩_ : ( A B : ZFSet  ) → ZFSet
    A ∩ B = record { def = λ x → def A x ∧ def B x } 
    Union : OD {suc n} → OD {suc n}
    Union U = record { def = λ y  → def U (osuc y) }
    _∈_ : ( A B : ZFSet  ) → Set (suc n)
    A ∈ B = B ∋ A
    _⊆_ : ( A B : ZFSet  ) → ∀{ x : ZFSet } →  Set (suc n)
    _⊆_ A B {x} = A ∋ x →  B ∋ x
    Power : OD {suc n} → OD {suc n}
    Power A = Replace (Def (Ord (od→ord A))) ( λ x → A ∩ x )
    ｛_｝ : ZFSet → ZFSet
    ｛ x ｝ = ( x ,  x )

    infixr  200 _∈_
    -- infixr  230 _∩_ _∪_
    infixr  220 _⊆_
    isZF : IsZF (OD {suc n})  _∋_  _==_ od∅ _,_ Union Power Select Replace (Ord omega)
    isZF = record {
           isEquivalence  = record { refl = eq-refl ; sym = eq-sym; trans = eq-trans }
       ;   pair  = pair
       ;   union-u = λ X z UX∋z → union-u {X} {z} UX∋z
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
       ;   selection = λ {X} {ψ} {y} → selection {X} {ψ} {y}
       ;   replacement← = replacement←
       ;   replacement→ = replacement→
     } where

         pair : (A B : OD {suc n} ) → ((A , B) ∋ A) ∧  ((A , B) ∋ B)
         proj1 (pair A B ) = omax-x {n} (od→ord A) (od→ord B)
         proj2 (pair A B ) = omax-y {n} (od→ord A) (od→ord B)

         empty : (x : OD {suc n} ) → ¬  (od∅ ∋ x)
         empty x (case1 ())
         empty x (case2 ())

         union-d : (X : OD {suc n}) → OD {suc n}
         union-d X = record { def = λ y → def X (osuc y) }
         union-u : {X z : OD {suc n}} → (U>z : Union X ∋ z ) → OD {suc n}
         union-u {X} {z} U>z = Ord ( osuc ( od→ord z ) )
         union→ :  (X z u : OD) → (X ∋ u) ∧ (u ∋ z) → Union X ∋ z
         union→ X z u xx with trio< ( od→ord u ) ( osuc ( od→ord z ))
         union→ X z u xx | tri< a ¬b ¬c with  osuc-< a (c<→o< (proj2 xx))
         union→ X z u xx | tri< a ¬b ¬c | ()
         union→ X z u xx | tri≈ ¬a b ¬c =  def-subst {suc n} {_} {_} {X} {osuc (od→ord z)} (proj1 xx) refl b
         union→ X z u xx | tri> ¬a ¬b c =  def-subst lemma1 (sym lemma0) diso where
             lemma0 : X ≡ Ord (od→ord X)
             lemma0 = sym {!!}
             lemma : osuc (od→ord z) o< od→ord X
             lemma = ordtrans c ( c<→o< ( proj1 xx ) )
             lemma1 : Ord ( od→ord X) ∋ ord→od (osuc (od→ord z) )
             lemma1 = o<-subst lemma (sym diso) refl
         union← :  (X z : OD) (X∋z : Union X ∋ z) → (X ∋  union-u {X} {z} X∋z ) ∧ (union-u {X} {z} X∋z ∋ z )
         union← X z UX∋z = record { proj1 = lemma ; proj2 = <-osuc } where
             lemma : X ∋ union-u {X} {z} UX∋z
             lemma = def-subst {suc n} {_} {_} {X} {od→ord (Ord (osuc ( od→ord z )))} UX∋z refl {!!}

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
             lemma not = ⊥-elim ( not ( od→ord x ) (record { proj1 = lt ; proj2 = cong (λ k → od→ord (ψ k))
                 {!!} } ))
         replacement→ : {ψ : OD → OD} (X x : OD) → (lt : Replace X ψ ∋ x) → ¬ ( (y : OD) → ¬ (x == ψ y))
         replacement→ {ψ} X x lt = contra-position lemma (lemma2 {!!}) where
            lemma2 :  ¬ ((y : Ordinal) → ¬ def X y ∧ ((od→ord x) ≡ od→ord (ψ (Ord y))))
                    → ¬ ((y : Ordinal) → ¬ def X y ∧ (ord→od (od→ord x) == ψ (Ord y)))
            lemma2 not not2  = not ( λ y d →  not2 y (record { proj1 = proj1 d ; proj2 = lemma3 (proj2 d)})) where
                lemma3 : {y : Ordinal } → (od→ord x ≡ od→ord (ψ (Ord y))) → (ord→od (od→ord x) == ψ (Ord y))  
                lemma3 {y} eq = subst (λ k  → ord→od (od→ord x) == k ) oiso (o≡→== eq )
            lemma :  ( (y : OD) → ¬ (x == ψ y)) → ( (y : Ordinal) → ¬ def X y ∧ (ord→od (od→ord x) == ψ (Ord y)) )
            lemma not y not2 = not (Ord y) (subst (λ k → k == ψ (Ord y)) oiso  ( proj2 not2 ))

         ---
         --- Power Set
         ---
         ---    First consider ordinals in OD
         ---
         --- ZFSubset A x =  record { def = λ y → def A y ∧  def x y }                   subset of A
         --- Power X = ord→od ( sup-o ( λ x → od→ord ( ZFSubset A (ord→od x )) ) )       Power X is a sup of all subset of A
         --
         --  if Power A ∋ t, from a propertiy of minimum sup there is osuc ZFSubset A ∋ t 
         --    then ZFSubset A ≡ t or ZFSubset A ∋ t. In the former case ZFSubset A ∋ x implies A ∋ x
         --    In case of later, ZFSubset A ∋ t and t ∋ x implies A ∋ x by transitivity
         --
         POrd : {a : Ordinal } {t : OD} → Def (Ord a) ∋ t → Def (Ord a) ∋ Ord (od→ord t)
         POrd {a} {t} P∋t = {!!}
         ∩-≡ :  { a b : OD {suc n} } → ({x : OD {suc n} } → (a ∋ x → b ∋ x)) → a == ( b ∩ a )
         ∩-≡ {a} {b} inc = record {
            eq→ = λ {x} x<a → record { proj2 = x<a ;
                 proj1 = def-subst {suc n} {_} {_} {b} {x} (inc (def-subst {suc n} {_} {_} {a} {_} x<a refl (sym diso) )) refl diso  } ;
            eq← = λ {x} x<a∩b → proj2 x<a∩b }
         ord-power→ : (a : Ordinal ) ( t : OD) → Def (Ord a) ∋ t → {x : OD} → t ∋ x → Ord a ∋ x
         ord-power→ a t P∋t {x} t∋x with osuc-≡<  (sup-lb  (POrd P∋t))
         ... | case1 eq = proj1 (def-subst (Ltx t∋x) (sym (subst₂ (λ j k → j ≡ k ) oiso oiso ( cong (λ k → ord→od k) (sym eq) ))) refl )  where
              Ltx :   {n : Level} → {x t : OD {suc n}} → t ∋ x → Ord (od→ord t) ∋ x
              Ltx {n} {x} {t} lt = c<→o< lt
         ... | case2 lt = lemma3 where
              sp =  sup-x (λ x → od→ord ( ZFSubset (Ord a) (ord→od x)))
              minsup :  OD
              minsup =  ZFSubset (Ord a) ( ord→od ( sup-x (λ x → od→ord ( ZFSubset (Ord a) (ord→od x))))) 
              Ltx :   {n : Level} → {x t : OD {suc n}} → t ∋ x → Ord (od→ord t) ∋ x
              Ltx {n} {x} {t} lt = c<→o< lt
              -- lemma1 hold because minsup is Ord (minα a sp) 
              lemma1 : od→ord (Ord (od→ord t)) o< od→ord minsup → minsup ∋ Ord (od→ord t)
              lemma1 lt with OrdSubset a ( sup-x (λ x → od→ord ( ZFSubset (Ord a) (ord→od x))))
              ... | eq with subst ( λ k →  ZFSubset (Ord a) k ≡ Ord (minα a sp)) {!!} eq
              ... | eq1 = def-subst {suc n} {_} {_} {minsup} {od→ord (Ord (od→ord t))} {!!} lemma2 {!!} where
                  lemma2 : Ord (od→ord (ZFSubset (Ord a) (ord→od sp))) ≡ minsup
                  lemma2 =  let open ≡-Reasoning in begin
                      Ord (od→ord (ZFSubset (Ord a) (ord→od sp)))
                    ≡⟨ cong (λ k → Ord (od→ord k)) eq1 ⟩
                      Ord (od→ord (Ord (minα a sp))) 
                    ≡⟨ cong (λ k → Ord (od→ord k)) {!!}  ⟩
                      Ord (od→ord (ord→od (minα a sp))) 
                    ≡⟨ cong (λ k → Ord k) diso ⟩
                      Ord (minα a sp)
                    ≡⟨ sym eq1 ⟩
                      minsup
                    ∎
              lemma3 : od→ord x o< a
              lemma3 = otrans (proj1 (lemma1 lt) ) (c<→o< {suc n} {x} {Ord (od→ord t)} (Ltx t∋x) )
         -- 
         -- we have t ∋ x → A ∋ x means t is a subset of A, that is ZFSubset A t == t
         -- Power A is a sup of ZFSubset A t, so Power A ∋ t
         -- 
         ord-power← : (a : Ordinal ) (t : OD) → ({x : OD} → (t ∋ x → (Ord a) ∋ x)) → Def (Ord a) ∋ t
         ord-power← a t t→A  = def-subst {suc n} {_} {_} {Def (Ord a)} {od→ord t}
                 lemma refl (lemma1 lemma-eq )where
              lemma-eq :  ZFSubset (Ord a) t == t
              eq→ lemma-eq {z} w = proj2 w 
              eq← lemma-eq {z} w = record { proj2 = w  ;
                 proj1 = def-subst {suc n} {_} {_} {(Ord a)} {z}
                    ( t→A (def-subst {suc n} {_} {_} {t} {od→ord (ord→od z)} w refl (sym diso) )) refl diso  }
              lemma1 : {n : Level } {a : Ordinal {suc n}} { t : OD {suc n}}
                 → (eq : ZFSubset (Ord a) t == t)  → od→ord (ZFSubset (Ord a) (ord→od (od→ord t))) ≡ od→ord t
              lemma1 {n} {a} {t} eq = subst (λ k → od→ord (ZFSubset (Ord a) k) ≡ od→ord t ) (sym oiso) (cong (λ k → od→ord k ) (==→o≡ eq ))
              lemma :  od→ord (ZFSubset (Ord a) (ord→od (od→ord t)) ) o< sup-o (λ x → od→ord (ZFSubset (Ord a) (ord→od x)))
              lemma = sup-o<   

         -- 
         -- Every set in OD is a subset of Ordinals
         -- 
         -- Power A = Replace (Def (Ord (od→ord A))) ( λ y → A ∩ y )
         power→ :  ( A t : OD) → Power A ∋ t → {x : OD} → t ∋ x → A ∋ x
         power→ A t P∋t {x} t∋x = TransFiniteExists {suc n} {λ y → (t ==  (A ∩ ord→od y))}
                 lemma4 lemma5  where
              a = od→ord A
              lemma2 : ¬ ( (y : OD) → ¬ (t ==  (A ∩ y)))
              lemma2 = replacement→ (Def (Ord (od→ord A))) t P∋t
              lemma3 : (y : OD) → t == ( A ∩ y ) → A ∋ x
              lemma3 y eq = proj1 (eq→ eq t∋x)
              lemma4 : ¬ ((y : Ordinal) → ¬ (t == (A ∩ ord→od y)))
              lemma4 not = lemma2 ( λ y not1 → not (od→ord y) (subst (λ k → t == ( A ∩ k )) (sym oiso) not1 ))
              lemma5 : {y : Ordinal} → t == (A ∩ ord→od y) → def A (od→ord x)
              lemma5 {y} eq = lemma3 (ord→od y) eq
         power← :  (A t : OD) → ({x : OD} → (t ∋ x → A ∋ x)) → Power A ∋ t
         power← A t t→A = record { proj1 = lemma1 ; proj2 = lemma2 } where 
              a = od→ord A
              lemma0 : {x : OD} → t ∋ x → Ord a ∋ x
              lemma0 {x} t∋x = c<→o< (t→A t∋x)
              lemma3 : Def (Ord a) ∋ t
              lemma3 = ord-power← a t lemma0
              lemma4 : od→ord t ≡ od→ord (A ∩ Ord (od→ord t))
              lemma4 = cong ( λ k → od→ord k ) ( ==→o≡ (subst (λ k → t == (A ∩ k)) {!!} {!!} ))
              lemma1 : od→ord t o< sup-o (λ x → od→ord (A ∩ ord→od x))
              lemma1 with sup-o< {suc n} {λ x → od→ord (A ∩ ord→od x)} {od→ord t}
              ... | lt = o<-subst {suc n} {_} {_} {_} {_} lt (sym (subst (λ k → od→ord t ≡ k) lemma5 lemma4 )) refl where
                  lemma5 : od→ord (A ∩ Ord (od→ord t)) ≡ od→ord (A ∩ ord→od (od→ord t))
                  lemma5 = cong (λ k → od→ord (A ∩ k )) {!!}
              lemma2 :  def (in-codomain (Def (Ord (od→ord A))) (_∩_ A)) (od→ord t)
              lemma2 not = ⊥-elim ( not (od→ord t) (record { proj1 = lemma3 ; proj2 = {!!} }) ) where

         ∅-iso :  {x : OD} → ¬ (x == od∅) → ¬ ((ord→od (od→ord x)) == od∅) 
         ∅-iso {x} neq = subst (λ k → ¬ k) (=-iso {n} ) neq  
         regularity :  (x : OD) (not : ¬ (x == od∅)) →
            (x ∋ minimul x not) ∧ (Select (minimul x not) (λ x₁ → (minimul x not ∋ x₁) ∧ (x ∋ x₁)) == od∅)
         proj1 (regularity x not ) = x∋minimul x not
         proj2 (regularity x not ) = record { eq→ = lemma1 ; eq← = λ {y} d → lemma2 {y} d } where
             lemma1 : {x₁ : Ordinal} → def (Select (minimul x not) (λ x₂ → (minimul x not ∋ x₂) ∧ (x ∋ x₂))) x₁ → def od∅ x₁
             lemma1 {x₁} s = ⊥-elim  ( minimul-1 x not (ord→od x₁) lemma3 ) where
                 lemma3 : def (minimul x not) (od→ord (ord→od x₁)) ∧ def x (od→ord (ord→od x₁))
                 lemma3 = record { proj1 = def-subst {suc n} {_} {_} {minimul x not} {_} (proj1 s) refl (sym diso)
                                 ; proj2 = proj2 (proj2 s) } 
             lemma2 : {x₁ : Ordinal} → def od∅ x₁ → def (Select (minimul x not) (λ x₂ → (minimul x not ∋ x₂) ∧ (x ∋ x₂))) x₁
             lemma2 {y} d = ⊥-elim (empty (ord→od y) (def-subst {suc n} {_} {_} {od∅} {od→ord (ord→od y)} d refl (sym diso) ))

         extensionality : {A B : OD {suc n}} → ((z : OD) → (A ∋ z) ⇔ (B ∋ z)) → A == B
         eq→ (extensionality {A} {B} eq ) {x} d = def-iso {suc n} {A} {B} (sym diso) (proj1 (eq (ord→od x))) d  
         eq← (extensionality {A} {B} eq ) {x} d = def-iso {suc n} {B} {A} (sym diso) (proj2 (eq (ord→od x))) d  

         open  import  Relation.Binary.PropositionalEquality
         uxxx-ord : {x  : OD {suc n}} → {y : Ordinal {suc n}} → def (Union (x , (x , x))) y ⇔ ( y o< osuc (od→ord x) )
         uxxx-ord {x} {y} = subst (λ k → k ⇔ ( y o< osuc (od→ord x) )) (sym lemma) ( osuc2 y (od→ord x))  where
              lemma : {y : Ordinal {suc n}} → def (Union (x , (x , x))) y ≡ osuc y o< osuc (osuc (od→ord x)) 
              lemma {y} = let open ≡-Reasoning in begin
                   def (Union (x , (x , x))) y  
                ≡⟨⟩
                   def ( Ord ( omax (od→ord x) (od→ord (Ord (omax (od→ord x)  (od→ord x)  )) ))) ( osuc y )
                ≡⟨⟩
                   osuc y o<  omax (od→ord x) (od→ord (Ord (omax (od→ord x)  (od→ord x)  )) )
                ≡⟨ cong (λ k → osuc y o<  omax (od→ord x) k ) {!!}  ⟩
                   osuc y o<  omax (od→ord x) (omax (od→ord x)  (od→ord x)  ) 
                ≡⟨ cong (λ k → osuc y o<  k ) (omxxx  (od→ord x) )  ⟩
                   osuc y o< osuc (osuc (od→ord x))
                ∎ 
         infinite : OD {suc n}
         infinite = Ord omega 
         infinity∅ : Ord omega  ∋ od∅ {suc n}
         infinity∅ = o<-subst (case1 (s≤s z≤n) ) {!!} refl
         infinity : (x : OD) → infinite ∋ x → infinite ∋ Union (x , (x , x ))
         infinity x lt = o<-subst ( lemma (od→ord x) lt ) eq refl where
              eq :  osuc (od→ord x) ≡ od→ord (Union (x , (x , x)))
              eq = let open ≡-Reasoning in begin
                    osuc (od→ord x)
                 ≡⟨ {!!}  ⟩
                    od→ord (Ord (osuc (od→ord x)))
                 ≡⟨ cong ( λ k → od→ord  k ) ( sym (==→o≡ ( ⇔→==  uxxx-ord ))) ⟩
                    od→ord (Union (x , (x , x)))
                 ∎
              lemma : (ox : Ordinal {suc n} ) → ox o< omega → osuc ox o< omega 
              lemma record { lv = Zero ; ord = (Φ .0) } (case1 (s≤s x)) = case1 (s≤s z≤n)
              lemma record { lv = Zero ; ord = (OSuc .0 ord₁) } (case1 (s≤s x)) = case1 (s≤s z≤n)
              lemma record { lv = (Suc lv₁) ; ord = (Φ .(Suc lv₁)) } (case1 (s≤s ()))
              lemma record { lv = (Suc lv₁) ; ord = (OSuc .(Suc lv₁) ord₁) } (case1 (s≤s ()))
              lemma record { lv = 1 ; ord = (Φ 1) } (case2 c2) with d<→lv c2
              lemma record { lv = (Suc Zero) ; ord = (Φ .1) } (case2 ()) | refl
         -- ∀ X [ ∅ ∉ X → (∃ f : X → ⋃ X ) → ∀ A ∈ X ( f ( A ) ∈ A ) ] -- this form is no good since X is a transitive set
         -- ∀ z [ ∀ x ( x ∈ z  → ¬ ( x ≈ ∅ ) )  ∧ ∀ x ∀ y ( x , y ∈ z ∧ ¬ ( x ≈ y )  → x ∩ y ≈ ∅  ) → ∃ u ∀ x ( x ∈ z → ∃ t ( u ∩ x) ≈ ｛ t ｝) ]
         record Choice (z : OD {suc n}) : Set (suc (suc n)) where
             field
                 u : {x : OD {suc n}} ( x∈z  : x ∈ z ) → OD {suc n}
                 t : {x : OD {suc n}} ( x∈z  : x ∈ z ) → (x : OD {suc n} ) → OD {suc n}
                 choice : { x : OD {suc n} } → ( x∈z  : x ∈ z ) → ( u x∈z ∩ x) == ｛ t x∈z x ｝
         -- choice : {x :  OD {suc n}} ( x ∈ z  → ¬ ( x ≈ ∅ ) ) →
         -- axiom-of-choice : { X : OD } → ( ¬x∅ : ¬ ( X == od∅ ) ) → { A : OD } → (A∈X : A ∈ X ) →  choice ¬x∅ A∈X ∈ A 
         -- axiom-of-choice {X} nx {A} lt = ¬∅=→∅∈ {!!}

