open import Level
module OD where

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

-- Ordinal in OD ( and ZFSet ) Transitive Set
Ord : { n : Level } → ( a : Ordinal {n} ) → OD {n}
Ord {n} a = record { def = λ y → y o< a }  

od∅ : {n : Level} → OD {n} 
od∅ {n} = Ord o∅ 

postulate      
  -- OD can be iso to a subset of Ordinal ( by means of Godel Set )
  od→ord : {n : Level} → OD {n} → Ordinal {n}
  ord→od : {n : Level} → Ordinal {n} → OD {n} 
  c<→o<  : {n : Level} {x y : OD {n} }   → def y ( od→ord x ) → od→ord x o< od→ord y
  oiso   : {n : Level} {x : OD {n}}      → ord→od ( od→ord x ) ≡ x
  diso   : {n : Level} {x : Ordinal {n}} → od→ord ( ord→od x ) ≡ x
  -- we should prove this in agda, but simply put here
  ==→o≡ : {n : Level} →  { x y : OD {suc n} } → (x == y) → x ≡ y
  -- next assumption causes ∀ x ∋ ∅ . It menas only an ordinal becomes a set
  --   o<→c<  : {n : Level} {x y : Ordinal {n} } → x o< y → def (ord→od y) x 
  --   ord→od x ≡ Ord x results the same
  -- supermum as Replacement Axiom
  sup-o  : {n : Level } → ( Ordinal {n} → Ordinal {n}) →  Ordinal {n}
  sup-o< : {n : Level } → { ψ : Ordinal {n} →  Ordinal {n}} → ∀ {x : Ordinal {n}} →  ψ x  o<  sup-o ψ 
  -- contra-position of mimimulity of supermum required in Power Set Axiom
  -- sup-x  : {n : Level } → ( Ordinal {n} → Ordinal {n}) →  Ordinal {n}
  -- sup-lb : {n : Level } → { ψ : Ordinal {n} →  Ordinal {n}} → {z : Ordinal {n}}  →  z o< sup-o ψ → z o< osuc (ψ (sup-x ψ))
  -- mimimul and x∋minimul is an Axiom of choice
  minimul : {n : Level } → (x : OD {suc n} ) → ¬ (x == od∅ )→ OD {suc n} 
  -- this should be ¬ (x == od∅ )→ ∃ ox → x ∋ Ord ox  ( minimum of x )
  x∋minimul : {n : Level } → (x : OD {suc n} ) → ( ne : ¬ (x == od∅ ) ) → def x ( od→ord ( minimul x ne ) )
  -- minimulity (may proved by ε-induction )
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

otrans : {n : Level} {a x y : Ordinal {n} } → def (Ord a) x → def (Ord x) y → def (Ord a) y
otrans x<a y<x = ordtrans y<x x<a

def→o< : {n : Level } {X : OD {suc n}} → {x : Ordinal {suc n}} → def X x → x o< od→ord X 
def→o< {n} {X} {x} lt = o<-subst {suc n} {_} {_} {x} {od→ord X} ( c<→o< ( def-subst {suc n} {X} {x}  lt (sym oiso) (sym diso) )) diso diso

∅3 : {n : Level} →  { x : Ordinal {suc n}}  → ( ∀(y : Ordinal {suc n}) → ¬ (y o< x ) ) → x ≡ o∅ {suc n}
∅3 {n} {x} = TransFinite {n} c2 c3 x where
   c0 : Nat →  Ordinal {suc n}  → Set (suc n)
   c0 lx x = (∀(y : Ordinal {suc n}) → ¬ (y o< x))  → x ≡ o∅ {suc n}
   c2 : (lx : Nat) → ((x₁ : Ordinal) → x₁ o< ordinal lx (Φ lx) → c0 (lv x₁) (record { lv = lv x₁ ; ord = ord x₁ }))→ c0 lx (record { lv = lx ; ord = Φ lx } )
   c2 Zero _ not = refl
   c2 (Suc lx) _ not with not ( record { lv = lx ; ord = Φ lx } )
   ... | t with t (case1 ≤-refl )
   c2 (Suc lx) _ not | t | ()
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

o∅≡od∅ : {n : Level} → ord→od (o∅ {suc n}) ≡ od∅ {suc n}
o∅≡od∅ {n} = ==→o≡ lemma where
     lemma0 :  {x : Ordinal} → def (ord→od o∅) x → def od∅ x
     lemma0 {x} lt = o<-subst (c<→o< {suc n} {ord→od x} {ord→od o∅} (def-subst {suc n} {ord→od o∅} {x} lt refl (sym diso)) ) diso diso
     lemma1 :  {x : Ordinal} → def od∅ x → def (ord→od o∅) x
     lemma1 (case1 ())
     lemma1 (case2 ())
     lemma : ord→od o∅ == od∅
     lemma = record { eq→ = lemma0 ; eq← = lemma1 }

ord-od∅ : {n : Level} → od→ord (od∅ {suc n}) ≡ o∅ {suc n}
ord-od∅ {n} = sym ( subst (λ k → k ≡  od→ord (od∅ {suc n}) ) diso (cong ( λ k → od→ord k ) o∅≡od∅ ) )

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

ppp : { n : Level } → { p : Set (suc n) } { a : OD {suc n} } → record { def = λ x → p } ∋ a → p
ppp {n} {p} {a} d = d

--
-- Axiom of choice in intutionistic logic implies the exclude middle
--     https://plato.stanford.edu/entries/axiom-choice/#AxiChoLog
--
p∨¬p : { n : Level } → ( p : Set (suc n) ) → p ∨ ( ¬ p )         -- assuming axiom of choice
p∨¬p {n} p with is-o∅ ( od→ord ( record { def = λ x → p } ))
p∨¬p {n} p | yes eq = case2 (¬p eq) where
   ps = record { def = λ x → p }
   lemma : ps == od∅ → p → ⊥
   lemma eq p0 = ¬x<0 {n} {od→ord ps} (eq→ eq p0 )
   ¬p : (od→ord ps ≡ o∅) → p → ⊥
   ¬p eq = lemma ( subst₂ (λ j k → j ==  k ) oiso o∅≡od∅ ( o≡→== eq ))
p∨¬p {n} p | no ¬p = case1 (ppp {n} {p} {minimul ps (λ eq →  ¬p (eqo∅ eq))} lemma) where
   ps = record { def = λ x → p }
   eqo∅ : ps ==  od∅ {suc n} → od→ord ps ≡  o∅ {suc n} 
   eqo∅ eq = subst (λ k → od→ord ps ≡ k) ord-od∅ ( cong (λ k → od→ord k ) (==→o≡ eq)) 
   lemma : ps ∋ minimul ps (λ eq →  ¬p (eqo∅ eq)) 
   lemma = x∋minimul ps (λ eq →  ¬p (eqo∅ eq))

∋-p : { n : Level } → ( p : Set (suc n) ) → Dec p   -- assuming axiom of choice    
∋-p {n} p with p∨¬p p
∋-p {n} p | case1 x = yes x
∋-p {n} p | case2 x = no x

double-neg-eilm : {n  : Level } {A : Set (suc n)} → ¬ ¬ A → A      -- we don't have this in intutionistic logic
double-neg-eilm {n} {A} notnot with ∋-p  A                         -- assuming axiom of choice
... | yes p = p
... | no ¬p = ⊥-elim ( notnot ¬p )

OrdP : {n : Level} →  ( x : Ordinal {suc n} ) ( y : OD {suc n} ) → Dec ( Ord x ∋ y )
OrdP {n} x y with trio< x (od→ord y)
OrdP {n} x y | tri< a ¬b ¬c = no ¬c
OrdP {n} x y | tri≈ ¬a refl ¬c = no ( o<¬≡ refl )
OrdP {n} x y | tri> ¬a ¬b c = yes c

-- open import Relation.Binary.HeterogeneousEquality as HE using (_≅_ ) 
-- postulate f-extensionality : { n : Level}  → Relation.Binary.PropositionalEquality.Extensionality (suc n) (suc (suc n))

in-codomain : {n : Level} → (X : OD {suc n} ) → ( ψ : OD {suc n} → OD {suc n} ) → OD {suc n}
in-codomain {n} X ψ = record { def = λ x → ¬ ( (y : Ordinal {suc n}) → ¬ ( def X y ∧  ( x ≡ od→ord (ψ (ord→od y )))))  }

-- Power Set of X ( or constructible by λ y → def X (od→ord y )

ZFSubset : {n : Level} → (A x : OD {suc n} ) → OD {suc n}
ZFSubset A x =  record { def = λ y → def A y ∧  def x y }  --   roughly x = A → Set 

Def :  {n : Level} → (A :  OD {suc n}) → OD {suc n}
Def {n} A = Ord ( sup-o ( λ x → od→ord ( ZFSubset A (ord→od x )) ) )   


_⊆_ : {n : Level} ( A B : OD {suc n}  ) → ∀{ x : OD {suc n} } →  Set (suc n)
_⊆_ A B {x} = A ∋ x →  B ∋ x

infixr  220 _⊆_

subset-lemma : {n : Level} → {A x y : OD {suc n} } → (  x ∋ y → ZFSubset A x ∋  y ) ⇔  ( _⊆_ x A {y} )
subset-lemma {n} {A} {x} {y} = record {
      proj1 = λ z lt → proj1 (z  lt)
    ; proj2 = λ x⊆A lt → record { proj1 = x⊆A lt ; proj2 = lt }
   } 


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

-- L0 :  {n : Level} → (α : Ordinal {suc n}) → L (osuc α) ∋ L α
-- L1 :  {n : Level} → (α β : Ordinal {suc n}) → α o< β → ∀ (x : OD {suc n})  → L α ∋ x → L β ∋ x 


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
    ; infinite = infinite
    ; isZF = isZF 
 } where
    ZFSet = OD {suc n}
    Select : (X : OD {suc n} ) → ((x : OD {suc n} ) → Set (suc n) ) → OD {suc n}
    Select X ψ = record { def = λ x →  ( def X x ∧ ψ ( ord→od x )) }
    Replace : OD {suc n} → (OD {suc n} → OD {suc n} ) → OD {suc n}
    Replace X ψ = record { def = λ x → (x o< sup-o ( λ x → od→ord (ψ (ord→od x )))) ∧ def (in-codomain X ψ) x }
    _,_ : OD {suc n} → OD {suc n} → OD {suc n}
    x , y = Ord (omax (od→ord x) (od→ord y))
    _∩_ : ( A B : ZFSet  ) → ZFSet
    A ∩ B = record { def = λ x → def A x ∧ def B x } 
    Union : OD {suc n} → OD {suc n}  
    Union U = record { def = λ x → ¬ (∀ (u : Ordinal ) → ¬ ((def U u) ∧ (def (ord→od u) x)))  }
    _∈_ : ( A B : ZFSet  ) → Set (suc n)
    A ∈ B = B ∋ A
    Power : OD {suc n} → OD {suc n}
    Power A = Replace (Def (Ord (od→ord A))) ( λ x → A ∩ x )
    ｛_｝ : ZFSet → ZFSet
    ｛ x ｝ = ( x ,  x )

    data infinite-d  : ( x : Ordinal {suc n} ) → Set (suc n) where
        iφ :  infinite-d o∅
        isuc : {x : Ordinal {suc n} } →   infinite-d  x  →
                infinite-d  (od→ord ( Union (ord→od x , (ord→od x , ord→od x ) ) ))

    infinite : OD {suc n}
    infinite = record { def = λ x → infinite-d x }

    infixr  200 _∈_
    -- infixr  230 _∩_ _∪_
    isZF : IsZF (OD {suc n})  _∋_  _==_ od∅ _,_ Union Power Select Replace infinite
    isZF = record {
           isEquivalence  = record { refl = eq-refl ; sym = eq-sym; trans = eq-trans }
       ;   pair  = pair
       ;   union→ = union→
       ;   union← = union←
       ;   empty = empty
       ;   power→ = power→  
       ;   power← = power← 
       ;   extensionality = λ {A} {B} {w} → extensionality {A} {B} {w} 
       ;   ε-induction = ε-induction
       ;   infinity∅ = infinity∅
       ;   infinity = infinity
       ;   selection = λ {X} {ψ} {y} → selection {X} {ψ} {y}
       ;   replacement← = replacement←
       ;   replacement→ = replacement→
       ;   choice-func = choice-func
       ;   choice = choice
     } where

         pair : (A B : OD {suc n} ) → ((A , B) ∋ A) ∧  ((A , B) ∋ B)
         proj1 (pair A B ) = omax-x {n} (od→ord A) (od→ord B)
         proj2 (pair A B ) = omax-y {n} (od→ord A) (od→ord B)

         empty : {n : Level } (x : OD {suc n} ) → ¬  (od∅ ∋ x)
         empty x (case1 ())
         empty x (case2 ())

         o<→c< :  {x y : Ordinal {suc n}} {z : OD {suc n}}→ x o< y → _⊆_  (Ord x) (Ord y) {z}
         o<→c< lt lt1 = ordtrans lt1 lt
         
         ⊆→o< :  {x y : Ordinal {suc n}} → (∀ (z : OD) → _⊆_  (Ord x) (Ord y) {z} ) →  x o< osuc y
         ⊆→o< {x} {y}  lt with trio< x y 
         ⊆→o< {x} {y}  lt | tri< a ¬b ¬c = ordtrans a <-osuc
         ⊆→o< {x} {y}  lt | tri≈ ¬a b ¬c = subst ( λ k → k o< osuc y) (sym b) <-osuc
         ⊆→o< {x} {y}  lt | tri> ¬a ¬b c with lt (ord→od y) (o<-subst c (sym diso) refl )
         ... | ttt = ⊥-elim ( o<¬≡ refl (o<-subst ttt diso refl ))

         union→ :  (X z u : OD) → (X ∋ u) ∧ (u ∋ z) → Union X ∋ z
         union→ X z u xx not = ⊥-elim ( not (od→ord u) ( record { proj1 = proj1 xx
              ; proj2 = subst ( λ k → def k (od→ord z)) (sym oiso) (proj2 xx) } ))
         union← :  (X z : OD) (X∋z : Union X ∋ z) →  ¬  ( (u : OD ) → ¬ ((X ∋  u) ∧ (u ∋ z )))
         union← X z UX∋z =  TransFiniteExists _ lemma UX∋z where
              lemma : {y : Ordinal} → def X y ∧ def (ord→od y) (od→ord z) → ¬ ((u : OD) → ¬ (X ∋ u) ∧ (u ∋ z))
              lemma {y} xx not = not (ord→od y) record { proj1 = subst ( λ k → def X k ) (sym diso) (proj1 xx ) ; proj2 = proj2 xx } 

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
             lemma not = ⊥-elim ( not ( od→ord x ) (record { proj1 = lt ; proj2 = cong (λ k → od→ord (ψ k)) (sym oiso)} ))
         replacement→ : {ψ : OD → OD} (X x : OD) → (lt : Replace X ψ ∋ x) → ¬ ( (y : OD) → ¬ (x == ψ y))
         replacement→ {ψ} X x lt = contra-position lemma (lemma2 (proj2 lt)) where
            lemma2 :  ¬ ((y : Ordinal) → ¬ def X y ∧ ((od→ord x) ≡ od→ord (ψ (ord→od y))))
                    → ¬ ((y : Ordinal) → ¬ def X y ∧ (ord→od (od→ord x) == ψ (ord→od y)))
            lemma2 not not2  = not ( λ y d →  not2 y (record { proj1 = proj1 d ; proj2 = lemma3 (proj2 d)})) where
                lemma3 : {y : Ordinal } → (od→ord x ≡ od→ord (ψ (ord→od  y))) → (ord→od (od→ord x) == ψ (ord→od y))  
                lemma3 {y} eq = subst (λ k  → ord→od (od→ord x) == k ) oiso (o≡→== eq )
            lemma :  ( (y : OD) → ¬ (x == ψ y)) → ( (y : Ordinal) → ¬ def X y ∧ (ord→od (od→ord x) == ψ (ord→od y)) )
            lemma not y not2 = not (ord→od y) (subst (λ k → k == ψ (ord→od y)) oiso  ( proj2 not2 ))

         ---
         --- Power Set
         ---
         ---    First consider ordinals in OD
         ---
         --- ZFSubset A x =  record { def = λ y → def A y ∧  def x y }                   subset of A
         --- Power X = ord→od ( sup-o ( λ x → od→ord ( ZFSubset A (ord→od x )) ) )       Power X is a sup of all subset of A
         --
         --
         ∩-≡ :  { a b : OD {suc n} } → ({x : OD {suc n} } → (a ∋ x → b ∋ x)) → a == ( b ∩ a )
         ∩-≡ {a} {b} inc = record {
            eq→ = λ {x} x<a → record { proj2 = x<a ;
                 proj1 = def-subst {suc n} {_} {_} {b} {x} (inc (def-subst {suc n} {_} {_} {a} {_} x<a refl (sym diso) )) refl diso  } ;
            eq← = λ {x} x<a∩b → proj2 x<a∩b }
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

         -- we have oly double negation form because of the replacement axiom
         --
         power→ :  ( A t : OD) → Power A ∋ t → {x : OD} → t ∋ x → ¬ ¬ (A ∋ x)
         power→ A t P∋t {x} t∋x = TransFiniteExists _ lemma5 lemma4 where
              a = od→ord A
              lemma2 : ¬ ( (y : OD) → ¬ (t ==  (A ∩ y)))
              lemma2 = replacement→ (Def (Ord (od→ord A))) t P∋t
              lemma3 : (y : OD) → t == ( A ∩ y ) → ¬ ¬ (A ∋ x)
              lemma3 y eq not = not (proj1 (eq→ eq t∋x))
              lemma4 : ¬ ((y : Ordinal) → ¬ (t == (A ∩ ord→od y)))
              lemma4 not = lemma2 ( λ y not1 → not (od→ord y) (subst (λ k → t == ( A ∩ k )) (sym oiso) not1 ))
              lemma5 : {y : Ordinal} → t == (A ∩ ord→od y) →  ¬ ¬  (def A (od→ord x))
              lemma5 {y} eq not = (lemma3 (ord→od y) eq) not

         power← :  (A t : OD) → ({x : OD} → (t ∋ x → A ∋ x)) → Power A ∋ t
         power← A t t→A = record { proj1 = lemma1 ; proj2 = lemma2 } where 
              a = od→ord A
              lemma0 : {x : OD} → t ∋ x → Ord a ∋ x
              lemma0 {x} t∋x = c<→o< (t→A t∋x)
              lemma3 : Def (Ord a) ∋ t
              lemma3 = ord-power← a t lemma0
              lt1 : od→ord (A ∩ ord→od (od→ord t)) o< sup-o (λ x → od→ord (A ∩ ord→od x))
              lt1 = sup-o< {suc n} {λ x → od→ord (A ∩ ord→od x)} {od→ord t}
              lemma4 :  (A ∩ ord→od (od→ord t)) ≡ t
              lemma4 = let open ≡-Reasoning in begin
                    A ∩ ord→od (od→ord t)
                 ≡⟨ cong (λ k → A ∩ k) oiso ⟩
                    A ∩ t
                 ≡⟨ sym (==→o≡ ( ∩-≡ t→A )) ⟩
                    t
                 ∎
              lemma1 : od→ord t o< sup-o (λ x → od→ord (A ∩ ord→od x))
              lemma1 = subst (λ k → od→ord k o< sup-o (λ x → od→ord (A ∩ ord→od x)))
                  lemma4 (sup-o< {suc n} {λ x → od→ord (A ∩ ord→od x)} {od→ord t})
              lemma2 :  def (in-codomain (Def (Ord (od→ord A))) (_∩_ A)) (od→ord t)
              lemma2 not = ⊥-elim ( not (od→ord t) (record { proj1 = lemma3 ; proj2 = lemma6 }) ) where
                  lemma6 : od→ord t ≡ od→ord (A ∩ ord→od (od→ord t)) 
                  lemma6 = cong ( λ k → od→ord k ) (==→o≡ (subst (λ k → t == (A ∩ k)) (sym oiso) ( ∩-≡ t→A  )))

         --  assuming axiom of choice
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

         extensionality0 : {A B : OD {suc n}} → ((z : OD) → (A ∋ z) ⇔ (B ∋ z)) → A == B
         eq→ (extensionality0 {A} {B} eq ) {x} d = def-iso {suc n} {A} {B} (sym diso) (proj1 (eq (ord→od x))) d  
         eq← (extensionality0 {A} {B} eq ) {x} d = def-iso {suc n} {B} {A} (sym diso) (proj2 (eq (ord→od x))) d  

         extensionality : {A B w : OD {suc n} } → ((z : OD {suc n}) → (A ∋ z) ⇔ (B ∋ z)) → (w ∋ A) ⇔ (w ∋ B)
         proj1 (extensionality {A} {B} {w} eq ) d = subst (λ k → w ∋ k) ( ==→o≡ (extensionality0 {A} {B} eq) ) d
         proj2 (extensionality {A} {B} {w} eq ) d = subst (λ k → w ∋ k) (sym ( ==→o≡ (extensionality0 {A} {B} eq) )) d 

         infinity∅ : infinite  ∋ od∅ {suc n}
         infinity∅ = def-subst {suc n} {_} {_} {infinite} {od→ord (od∅ {suc n})} iφ refl lemma where
              lemma : o∅ ≡ od→ord od∅
              lemma =  let open ≡-Reasoning in begin
                    o∅
                 ≡⟨ sym diso ⟩
                    od→ord ( ord→od o∅ )
                 ≡⟨ cong ( λ k → od→ord k ) o∅≡od∅ ⟩
                    od→ord od∅
                 ∎
         infinity : (x : OD) → infinite ∋ x → infinite ∋ Union (x , (x , x ))
         infinity x lt = def-subst {suc n} {_} {_} {infinite} {od→ord (Union (x , (x , x )))} ( isuc {od→ord x} lt ) refl lemma where
               lemma :  od→ord (Union (ord→od (od→ord x) , (ord→od (od→ord x) , ord→od (od→ord x))))
                    ≡ od→ord (Union (x , (x , x)))
               lemma = cong (λ k → od→ord (Union ( k , ( k , k ) ))) oiso 

         -- Axiom of choice ( is equivalent to the existence of minimul in our case )
         -- ∀ X [ ∅ ∉ X → (∃ f : X → ⋃ X ) → ∀ A ∈ X ( f ( A ) ∈ A ) ] 
         choice-func : (X : OD {suc n} ) → {x : OD } → ¬ ( x == od∅ ) → ( X ∋ x ) → OD
         choice-func X {x} not X∋x = minimul x not
         choice : (X : OD {suc n} ) → {A : OD } → ( X∋A : X ∋ A ) → (not : ¬ ( A == od∅ )) → A ∋ choice-func X not X∋A 
         choice X {A} X∋A not = x∋minimul A not

         --
         -- another form of regularity 
         --
         ε-induction : {n m : Level} { ψ : OD {suc n} → Set m}
             → ( {x : OD {suc n} } → ({ y : OD {suc n} } →  x ∋ y → ψ y ) → ψ x )
             → (x : OD {suc n} ) → ψ x
         ε-induction {n} {m} {ψ} ind x = subst (λ k → ψ k ) oiso (ε-induction-ord (lv (osuc (od→ord x))) (ord (osuc (od→ord x)))  <-osuc) where
            ε-induction-ord : (lx : Nat) ( ox : OrdinalD {suc n} lx ) {ly : Nat} {oy : OrdinalD {suc n} ly }
                → (ly < lx) ∨ (oy d< ox  ) → ψ (ord→od (record { lv = ly ; ord = oy } ) )
            ε-induction-ord lx  (OSuc lx ox) {ly} {oy} y<x = 
                ind {ord→od (record { lv = ly ; ord = oy })} ( λ {y} lt → subst (λ k → ψ k ) oiso (ε-induction-ord lx ox (lemma y lt ))) where
                    lemma :  (z : OD) → ord→od record { lv = ly ; ord = oy } ∋ z → od→ord z o< record { lv = lx ; ord = ox }
                    lemma z lt with osuc-≡< y<x
                    lemma z lt | case1 refl = o<-subst (c<→o< lt) refl diso
                    lemma z lt | case2 lt1 = ordtrans  (o<-subst (c<→o< lt) refl diso) lt1  
            ε-induction-ord (Suc lx) (Φ (Suc lx)) {ly} {oy} (case1 y<sox ) =                    
                ind {ord→od (record { lv = ly ; ord = oy })} ( λ {y} lt → lemma y lt )  where  
                    --
                    --     if lv of z if less than x Ok
                    --     else lv z = lv x. We can create OSuc of z which is larger than z and less than x in lemma
                    --
                    --                         lx    Suc lx      (1) lz(a) <lx by case1
                    --                 ly(1)   ly(2)             (2) lz(b) <lx by case1
                    --           lz(a) lz(b)   lz(c)                 lz(c) <lx by case2 ( ly==lz==lx)
                    --
                    lemma0 : { lx ly : Nat } → ly < Suc lx  → lx < ly → ⊥
                    lemma0 {Suc lx} {Suc ly} (s≤s lt1) (s≤s lt2) = lemma0 lt1 lt2
                    lemma1 : {n : Level } {ly : Nat} {oy : OrdinalD {suc n} ly} → lv (od→ord (ord→od (record { lv = ly ; ord = oy }))) ≡ ly
                    lemma1 {n} {ly} {oy} = let open ≡-Reasoning in begin
                            lv (od→ord (ord→od (record { lv = ly ; ord = oy })))
                         ≡⟨ cong ( λ k → lv k ) diso ⟩
                            lv (record { lv = ly ; ord = oy })
                         ≡⟨⟩
                            ly
                         ∎
                    lemma :  (z : OD) → ord→od record { lv = ly ; ord = oy } ∋ z → ψ z
                    lemma z lt with  c<→o< {suc n} {z} {ord→od (record { lv = ly ; ord = oy })} lt
                    lemma z lt | case1 lz<ly with <-cmp lx ly
                    lemma z lt | case1 lz<ly | tri< a ¬b ¬c = ⊥-elim ( lemma0 y<sox a) -- can't happen
                    lemma z lt | case1 lz<ly | tri≈ ¬a refl ¬c =    -- ly(1)
                          subst (λ k → ψ k ) oiso (ε-induction-ord lx (Φ lx) {_} {ord (od→ord z)} (case1 (subst (λ k → lv (od→ord z) < k ) lemma1 lz<ly ) ))
                    lemma z lt | case1 lz<ly | tri> ¬a ¬b c =       -- lz(a)
                          subst (λ k → ψ k ) oiso (ε-induction-ord lx (Φ lx) {_} {ord (od→ord z)} (case1 (<-trans lz<ly (subst (λ k → k < lx ) (sym lemma1) c))))
                    lemma z lt | case2 lz=ly with <-cmp lx ly
                    lemma z lt | case2 lz=ly | tri< a ¬b ¬c = ⊥-elim ( lemma0 y<sox a) -- can't happen
                    lemma z lt | case2 lz=ly | tri> ¬a ¬b c with d<→lv lz=ly        -- lz(b)
                    ... | eq = subst (λ k → ψ k ) oiso
                         (ε-induction-ord lx (Φ lx) {_} {ord (od→ord z)} (case1 (subst (λ k → k < lx ) (trans (sym lemma1)(sym eq) ) c )))
                    lemma z lt | case2 lz=ly | tri≈ ¬a lx=ly ¬c with d<→lv lz=ly    -- lz(c)
                    ... | eq = lemma6 {ly} {Φ lx} {oy} lx=ly (sym (subst (λ k → lv (od→ord z) ≡  k) lemma1 eq)) where
                          lemma5 : (ox : OrdinalD lx) → (lv (od→ord z) < lx) ∨ (ord (od→ord z) d< ox) → ψ z
                          lemma5 ox lt = subst (λ k → ψ k ) oiso (ε-induction-ord lx ox lt )
                          lemma6 : { ly : Nat } { ox : OrdinalD {suc n} lx } { oy : OrdinalD {suc n} ly }  →
                               lx ≡ ly → ly ≡ lv (od→ord z)  → ψ z 
                          lemma6 {ly} {ox} {oy} refl refl = lemma5 (OSuc lx (ord (od→ord z)) ) (case2 s<refl)

         ---
         --- With assuption of OD is ordered,  p ∨ ( ¬ p ) <=> axiom of choice
         ---
         record choiced {n : Level} ( X : OD {suc n}) : Set (suc (suc n)) where
            field
                a-choice : OD {suc n}
                is-in : X ∋ a-choice
         choice-func' : (X : OD {suc n} ) → (p∨¬p : { n : Level } → ( p : Set (suc n) ) → p ∨ ( ¬ p )) → ¬ ( X == od∅ ) → choiced X
         choice-func' X p∨¬p not = have_to_find 
           where
            ψ : ( ox : Ordinal {suc n}) → Set (suc (suc n))
            ψ ox = (( x : Ordinal {suc n}) → x o< ox  → ( ¬ def X x )) ∨ choiced X
            lemma-ord : ( ox : Ordinal {suc n} ) → ψ ox
            lemma-ord  ox = TransFinite {n} {suc (suc n)} {ψ} caseΦ caseOSuc ox where
               ∋-p' : (A x : OD {suc n} ) → Dec ( A ∋ x ) 
               ∋-p' A x with p∨¬p ( A ∋ x )
               ∋-p' A x | case1 t = yes t
               ∋-p' A x | case2 t = no t
               ∀-imply-or :  {n : Level}  {A : Ordinal {suc n} → Set (suc n) } {B : Set (suc (suc n)) }
                   → ((x : Ordinal {suc n}) → A x ∨ B) →  ((x : Ordinal {suc n}) → A x) ∨ B
               ∀-imply-or {n} {A} {B} ∀AB with p∨¬p  ((x : Ordinal {suc n}) → A x)
               ∀-imply-or {n} {A} {B} ∀AB | case1 t = case1 t
               ∀-imply-or {n} {A} {B} ∀AB | case2 x = case2 (lemma x) where
                    lemma : ¬ ((x : Ordinal {suc n}) → A x) →  B
                    lemma not with p∨¬p B
                    lemma not | case1 b = b
                    lemma not | case2 ¬b = ⊥-elim  (not (λ x → dont-orb (∀AB x) ¬b ))
               caseΦ : (lx : Nat) → ( (x : Ordinal {suc n} ) → x o< ordinal lx (Φ lx) → ψ x) → ψ (ordinal lx (Φ lx) ) 
               caseΦ lx prev with ∋-p' X ( ord→od (ordinal lx (Φ lx) ))
               caseΦ lx prev | yes p = case2 ( record { a-choice = ord→od (ordinal lx (Φ lx)) ; is-in = p } )
               caseΦ lx prev | no ¬p = lemma where
                    lemma1 : (x : Ordinal) → (((Suc (lv x) ≤ lx) ∨ (ord x d< Φ lx) → def X x → ⊥) ∨ choiced X)
                    lemma1 x with trio< x (ordinal lx (Φ lx))
                    lemma1 x | tri< a ¬b ¬c with prev (osuc x) (lemma2 a) where
                        lemma2 : x o< (ordinal lx (Φ lx)) →  osuc x o< ordinal lx (Φ lx)
                        lemma2 (case1 lt) = case1 lt
                    lemma1 x | tri< a ¬b ¬c | case2 found = case2 found
                    lemma1 x | tri< a ¬b ¬c | case1 not_found = case1 ( λ lt df → not_found x <-osuc df )
                    lemma1 x | tri≈ ¬a refl ¬c = case1 ( λ lt → ⊥-elim (o<¬≡ refl lt ))
                    lemma1 x | tri> ¬a ¬b c = case1 ( λ lt → ⊥-elim (o<> lt c ))
                    lemma : ((x : Ordinal) → (Suc (lv x) ≤ lx) ∨ (ord x d< Φ lx) → def X x → ⊥) ∨ choiced X
                    lemma = ∀-imply-or lemma1
               caseOSuc : (lx : Nat) (x : OrdinalD lx) → ψ ( ordinal lx x ) → ψ ( ordinal lx (OSuc lx x) )
               caseOSuc lx x prev with ∋-p' X (ord→od record { lv = lx ; ord = x } )
               caseOSuc lx x prev | yes p = case2 (record { a-choice = ord→od record { lv = lx ; ord = x } ; is-in = p })
               caseOSuc lx x (case1 not_found) | no ¬p = case1 lemma where
                    lemma : (y : Ordinal) → (Suc (lv y) ≤ lx) ∨ (ord y d< OSuc lx x) → def X y → ⊥
                    lemma y lt with trio< y (ordinal lx x )
                    lemma y lt | tri< a ¬b ¬c = not_found y a
                    lemma y lt | tri≈ ¬a refl ¬c = subst (λ k → def X k → ⊥ ) diso ¬p
                    lemma y lt | tri> ¬a ¬b c with osuc-≡< lt
                    lemma y lt | tri> ¬a ¬b c | case1 refl = ⊥-elim ( ¬b refl )
                    lemma y lt | tri> ¬a ¬b c | case2 lt1 = ⊥-elim (o<> c lt1 )
               caseOSuc lx x (case2 found) | no ¬p = case2 found
            have_to_find : choiced X
            have_to_find with lemma-ord (od→ord X )
            have_to_find | t = dont-or  t ¬¬X∋x where
                ¬¬X∋x : ¬ ((x : Ordinal) → (Suc (lv x) ≤ lv (od→ord X)) ∨ (ord x d< ord (od→ord X)) → def X x → ⊥)
                ¬¬X∋x nn = not record {
                       eq→ = λ {x} lt → ⊥-elim  (nn x (def→o< lt) lt) 
                     ; eq← = λ {x} lt → ⊥-elim ( ¬x<0 lt )
                   }

