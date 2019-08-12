open import Level
open import Ordinals
module OD {n : Level } (O : Ordinals {n} ) where

open import zf
open import Data.Nat renaming ( zero to Zero ; suc to Suc ;  ℕ to Nat ; _⊔_ to _n⊔_ ) 
open import  Relation.Binary.PropositionalEquality
open import Data.Nat.Properties 
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.Core

open import logic
open import nat

open inOrdinal O

-- Ordinal Definable Set

record OD : Set (suc n ) where
  field
    def : (x : Ordinal  ) → Set n

open OD

open _∧_
open _∨_
open Bool

record _==_  ( a b :  OD  ) : Set n where
  field
     eq→ : ∀ { x : Ordinal  } → def a x → def b x 
     eq← : ∀ { x : Ordinal  } → def b x → def a x 

id : {n : Level} {A : Set n} → A → A
id x = x

eq-refl :  {  x :  OD  } → x == x
eq-refl  {x} = record { eq→ = id ; eq← = id }

open  _==_ 

eq-sym :  {  x y :  OD  } → x == y → y == x
eq-sym eq = record { eq→ = eq← eq ; eq← = eq→ eq }

eq-trans :  {  x y z :  OD  } → x == y → y == z → x == z
eq-trans x=y y=z = record { eq→ = λ t → eq→ y=z ( eq→ x=y  t) ; eq← = λ t → eq← x=y ( eq← y=z t) }

⇔→== :  {  x y :  OD  } → ( {z : Ordinal } → def x z ⇔  def y z) → x == y 
eq→ ( ⇔→==  {x} {y}  eq ) {z} m = proj1 eq m 
eq← ( ⇔→==  {x} {y}  eq ) {z} m = proj2 eq m 

-- Ordinal in OD ( and ZFSet ) Transitive Set
Ord : ( a : Ordinal  ) → OD 
Ord  a = record { def = λ y → y o< a }  

od∅ : OD  
od∅  = Ord o∅ 

postulate      
  -- OD can be iso to a subset of Ordinal ( by means of Godel Set )
  od→ord : OD  → Ordinal 
  ord→od : Ordinal  → OD  
  c<→o<  :  {x y : OD  }   → def y ( od→ord x ) → od→ord x o< od→ord y
  oiso   :  {x : OD }      → ord→od ( od→ord x ) ≡ x
  diso   :  {x : Ordinal } → od→ord ( ord→od x ) ≡ x
  -- we should prove this in agda, but simply put here
  ==→o≡ : { x y : OD  } → (x == y) → x ≡ y
  -- next assumption causes ∀ x ∋ ∅ . It menas only an ordinal becomes a set
  --   o<→c<  : {n : Level} {x y : Ordinal  } → x o< y → def (ord→od y) x 
  --   ord→od x ≡ Ord x results the same
  -- supermum as Replacement Axiom
  sup-o  :  ( Ordinal  → Ordinal ) →  Ordinal 
  sup-o< :  { ψ : Ordinal  →  Ordinal } → ∀ {x : Ordinal } →  ψ x  o<  sup-o ψ 
  -- contra-position of mimimulity of supermum required in Power Set Axiom
  -- sup-x  : {n : Level } → ( Ordinal  → Ordinal ) →  Ordinal 
  -- sup-lb : {n : Level } → { ψ : Ordinal  →  Ordinal } → {z : Ordinal }  →  z o< sup-o ψ → z o< osuc (ψ (sup-x ψ))
  -- mimimul and x∋minimul is an Axiom of choice
  minimul : (x : OD  ) → ¬ (x == od∅ )→ OD 
  -- this should be ¬ (x == od∅ )→ ∃ ox → x ∋ Ord ox  ( minimum of x )
  x∋minimul : (x : OD  ) → ( ne : ¬ (x == od∅ ) ) → def x ( od→ord ( minimul x ne ) )
  -- minimulity (may proved by ε-induction )
  minimul-1 : (x : OD  ) → ( ne : ¬ (x == od∅ ) ) → (y : OD ) → ¬ ( def (minimul x ne) (od→ord y)) ∧ (def x (od→ord  y) )

_∋_ : ( a x : OD  ) → Set n
_∋_  a x  = def a ( od→ord x )

_c<_ : ( x a : OD  ) → Set n
x c< a = a ∋ x 

_c≤_ : OD  →  OD  → Set (suc n)
a c≤ b  = (a ≡ b)  ∨ ( b ∋ a )

cseq : {n : Level} →  OD  →  OD 
cseq x = record { def = λ y → def x (osuc y) } where

def-subst :  {Z : OD } {X : Ordinal  }{z : OD } {x : Ordinal  }→ def Z X → Z ≡ z  →  X ≡ x  →  def z x
def-subst df refl refl = df

sup-od : ( OD  → OD ) →  OD 
sup-od ψ = Ord ( sup-o ( λ x → od→ord (ψ (ord→od x ))) )

sup-c< : ( ψ : OD  →  OD ) → ∀ {x : OD } → def ( sup-od ψ ) (od→ord ( ψ x ))
sup-c<  ψ {x} = def-subst  {_} {_} {Ord ( sup-o ( λ x → od→ord (ψ (ord→od x ))) )} {od→ord ( ψ x )}
        lemma refl (cong ( λ k → od→ord (ψ k) ) oiso) where
    lemma : od→ord (ψ (ord→od (od→ord x))) o< sup-o (λ x → od→ord (ψ (ord→od x)))
    lemma = subst₂ (λ j k → j o< k ) refl diso (o<-subst sup-o< refl (sym diso)  )

otrans : {n : Level} {a x y : Ordinal  } → def (Ord a) x → def (Ord x) y → def (Ord a) y
otrans x<a y<x = ordtrans y<x x<a

def→o< :  {X : OD } → {x : Ordinal } → def X x → x o< od→ord X 
def→o<  {X} {x} lt = o<-subst  {_} {_} {x} {od→ord X} ( c<→o< ( def-subst  {X} {x}  lt (sym oiso) (sym diso) )) diso diso

-- avoiding lv != Zero error
orefl : { x : OD  } → { y : Ordinal  } → od→ord x ≡ y → od→ord x ≡ y
orefl refl = refl

==-iso : { x y : OD  } → ord→od (od→ord x) == ord→od (od→ord y)  →  x == y
==-iso  {x} {y} eq = record {
      eq→ = λ d →  lemma ( eq→  eq (def-subst d (sym oiso) refl )) ;
      eq← = λ d →  lemma ( eq←  eq (def-subst d (sym oiso) refl ))  }
        where
           lemma : {x : OD  } {z : Ordinal } → def (ord→od (od→ord x)) z → def x z
           lemma {x} {z} d = def-subst d oiso refl

=-iso :  {x y : OD  } → (x == y) ≡ (ord→od (od→ord x) == y)
=-iso  {_} {y} = cong ( λ k → k == y ) (sym oiso)

ord→== : { x y : OD  } → od→ord x ≡  od→ord y →  x == y
ord→==  {x} {y} eq = ==-iso (lemma (od→ord x) (od→ord y) (orefl eq)) where
   lemma : ( ox oy : Ordinal  ) → ox ≡ oy →  (ord→od ox) == (ord→od oy)
   lemma ox ox  refl = eq-refl

o≡→== : { x y : Ordinal  } → x ≡  y →  ord→od x == ord→od y
o≡→==  {x} {.x} refl = eq-refl

c≤-refl : {n : Level} →  ( x : OD  ) → x c≤ x
c≤-refl x = case1 refl

o∅≡od∅ : ord→od (o∅ ) ≡ od∅ 
o∅≡od∅  = ==→o≡ lemma where
     lemma0 :  {x : Ordinal} → def (ord→od o∅) x → def od∅ x
     lemma0 {x} lt = o<-subst (c<→o<  {ord→od x} {ord→od o∅} (def-subst  {ord→od o∅} {x} lt refl (sym diso)) ) diso diso
     lemma1 :  {x : Ordinal} → def od∅ x → def (ord→od o∅) x
     lemma1 {x} lt = ⊥-elim (¬x<0 lt)
     lemma : ord→od o∅ == od∅
     lemma = record { eq→ = lemma0 ; eq← = lemma1 }

ord-od∅ : od→ord (od∅ ) ≡ o∅ 
ord-od∅  = sym ( subst (λ k → k ≡  od→ord (od∅ ) ) diso (cong ( λ k → od→ord k ) o∅≡od∅ ) )

∅0 : record { def = λ x →  Lift n ⊥ } == od∅  
eq→ ∅0 {w} (lift ())
eq← ∅0 {w} lt = lift (¬x<0 lt)

∅< : { x y : OD  } → def x (od→ord y ) → ¬ (  x  == od∅  )
∅<  {x} {y} d eq with eq→ (eq-trans eq (eq-sym ∅0) ) d
∅<  {x} {y} d eq | lift ()
       
∅6 : { x : OD  }  → ¬ ( x ∋ x )    --  no Russel paradox
∅6  {x} x∋x = o<¬≡ refl ( c<→o<  {x} {x} x∋x )

def-iso : {A B : OD } {x y : Ordinal } → x ≡ y  → (def A y → def B y)  → def A x → def B x
def-iso refl t = t

is-o∅ : ( x : Ordinal  ) → Dec ( x ≡ o∅  )
is-o∅ x with trio< x o∅
is-o∅ x | tri< a ¬b ¬c = no ¬b
is-o∅ x | tri≈ ¬a b ¬c = yes b
is-o∅ x | tri> ¬a ¬b c = no ¬b

ppp :  { p : Set n } { a : OD  } → record { def = λ x → p } ∋ a → p
ppp  {p} {a} d = d

--
-- Axiom of choice in intutionistic logic implies the exclude middle
--     https://plato.stanford.edu/entries/axiom-choice/#AxiChoLog
--
p∨¬p : ( p : Set n ) → p ∨ ( ¬ p )         -- assuming axiom of choice
p∨¬p  p with is-o∅ ( od→ord ( record { def = λ x → p } ))
p∨¬p  p | yes eq = case2 (¬p eq) where
   ps = record { def = λ x → p }
   lemma : ps == od∅ → p → ⊥
   lemma eq p0 = ¬x<0  {od→ord ps} (eq→ eq p0 )
   ¬p : (od→ord ps ≡ o∅) → p → ⊥
   ¬p eq = lemma ( subst₂ (λ j k → j ==  k ) oiso o∅≡od∅ ( o≡→== eq ))
p∨¬p  p | no ¬p = case1 (ppp  {p} {minimul ps (λ eq →  ¬p (eqo∅ eq))} lemma) where
   ps = record { def = λ x → p }
   eqo∅ : ps ==  od∅  → od→ord ps ≡  o∅  
   eqo∅ eq = subst (λ k → od→ord ps ≡ k) ord-od∅ ( cong (λ k → od→ord k ) (==→o≡ eq)) 
   lemma : ps ∋ minimul ps (λ eq →  ¬p (eqo∅ eq)) 
   lemma = x∋minimul ps (λ eq →  ¬p (eqo∅ eq))

∋-p : ( p : Set n ) → Dec p   -- assuming axiom of choice    
∋-p  p with p∨¬p p
∋-p  p | case1 x = yes x
∋-p  p | case2 x = no x

double-neg-eilm : {A : Set n} → ¬ ¬ A → A      -- we don't have this in intutionistic logic
double-neg-eilm  {A} notnot with ∋-p  A                         -- assuming axiom of choice
... | yes p = p
... | no ¬p = ⊥-elim ( notnot ¬p )

OrdP : ( x : Ordinal  ) ( y : OD  ) → Dec ( Ord x ∋ y )
OrdP  x y with trio< x (od→ord y)
OrdP  x y | tri< a ¬b ¬c = no ¬c
OrdP  x y | tri≈ ¬a refl ¬c = no ( o<¬≡ refl )
OrdP  x y | tri> ¬a ¬b c = yes c

-- open import Relation.Binary.HeterogeneousEquality as HE using (_≅_ ) 
-- postulate f-extensionality : { n : Level}  → Relation.Binary.PropositionalEquality.Extensionality n (suc n)

in-codomain : (X : OD  ) → ( ψ : OD  → OD  ) → OD 
in-codomain  X ψ = record { def = λ x → ¬ ( (y : Ordinal ) → ¬ ( def X y ∧  ( x ≡ od→ord (ψ (ord→od y )))))  }

-- Power Set of X ( or constructible by λ y → def X (od→ord y )

ZFSubset : (A x : OD  ) → OD 
ZFSubset A x =  record { def = λ y → def A y ∧  def x y }  --   roughly x = A → Set 

Def :  (A :  OD ) → OD 
Def  A = Ord ( sup-o ( λ x → od→ord ( ZFSubset A (ord→od x )) ) )   


_⊆_ :  ( A B : OD   ) → ∀{ x : OD  } →  Set n
_⊆_ A B {x} = A ∋ x →  B ∋ x

infixr  220 _⊆_

subset-lemma : {A x y : OD  } → (  x ∋ y → ZFSubset A x ∋  y ) ⇔  ( _⊆_ x A {y} )
subset-lemma  {A} {x} {y} = record {
      proj1 = λ z lt → proj1 (z  lt)
    ; proj2 = λ x⊆A lt → record { proj1 = x⊆A lt ; proj2 = lt }
   } 

-- Constructible Set on α
-- Def X = record { def = λ y → ∀ (x : OD ) → y < X ∧ y <  od→ord x } 
-- L (Φ 0) = Φ
-- L (OSuc lv n) = { Def ( L n )  } 
-- L (Φ (Suc n)) = Union (L α) (α < Φ (Suc n) )
-- L : {n : Level} → (α : Ordinal ) → OD 
-- L   record { lv = Zero ; ord = (Φ .0) } = od∅
-- L   record { lv = lx ; ord = (OSuc lv ox) } = Def ( L  ( record { lv = lx ; ord = ox } ) ) 
-- L   record { lv = (Suc lx) ; ord = (Φ (Suc lx)) } = -- Union ( L α )
--     cseq ( Ord (od→ord (L   (record { lv = lx ; ord = Φ lx }))))

-- L0 :  {n : Level} → (α : Ordinal ) → L (osuc α) ∋ L α
-- L1 :  {n : Level} → (α β : Ordinal ) → α o< β → ∀ (x : OD )  → L α ∋ x → L β ∋ x 

OD→ZF : ZF  
OD→ZF   = record { 
    ZFSet = OD 
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
    ZFSet = OD 
    Select : (X : OD  ) → ((x : OD  ) → Set n ) → OD 
    Select X ψ = record { def = λ x →  ( def X x ∧ ψ ( ord→od x )) }
    Replace : OD  → (OD  → OD  ) → OD 
    Replace X ψ = record { def = λ x → (x o< sup-o ( λ x → od→ord (ψ (ord→od x )))) ∧ def (in-codomain X ψ) x }
    _,_ : OD  → OD  → OD 
    x , y = Ord (omax (od→ord x) (od→ord y))
    _∩_ : ( A B : ZFSet  ) → ZFSet
    A ∩ B = record { def = λ x → def A x ∧ def B x } 
    Union : OD  → OD   
    Union U = record { def = λ x → ¬ (∀ (u : Ordinal ) → ¬ ((def U u) ∧ (def (ord→od u) x)))  }
    _∈_ : ( A B : ZFSet  ) → Set n
    A ∈ B = B ∋ A
    Power : OD  → OD 
    Power A = Replace (Def (Ord (od→ord A))) ( λ x → A ∩ x )
    ｛_｝ : ZFSet → ZFSet
    ｛ x ｝ = ( x ,  x )

    data infinite-d  : ( x : Ordinal  ) → Set n where
        iφ :  infinite-d o∅
        isuc : {x : Ordinal  } →   infinite-d  x  →
                infinite-d  (od→ord ( Union (ord→od x , (ord→od x , ord→od x ) ) ))

    infinite : OD 
    infinite = record { def = λ x → infinite-d x }

    infixr  200 _∈_
    -- infixr  230 _∩_ _∪_
    isZF : IsZF (OD )  _∋_  _==_ od∅ _,_ Union Power Select Replace infinite
    isZF = record {
           isEquivalence  = record { refl = eq-refl ; sym = eq-sym; trans = eq-trans }
       ;   pair  = pair
       ;   union→ = union→
       ;   union← = union←
       ;   empty = empty
       ;   power→ = power→  
       ;   power← = power← 
       ;   extensionality = λ {A} {B} {w} → extensionality {A} {B} {w} 
       -- ;   ε-induction = {!!}
       ;   infinity∅ = infinity∅
       ;   infinity = infinity
       ;   selection = λ {X} {ψ} {y} → selection {X} {ψ} {y}
       ;   replacement← = replacement←
       ;   replacement→ = replacement→
       ;   choice-func = choice-func
       ;   choice = choice
     } where

         pair : (A B : OD  ) → ((A , B) ∋ A) ∧  ((A , B) ∋ B)
         proj1 (pair A B ) = omax-x  (od→ord A) (od→ord B)
         proj2 (pair A B ) = omax-y  (od→ord A) (od→ord B)

         empty : (x : OD  ) → ¬  (od∅ ∋ x)
         empty x = ¬x<0 

         o<→c< :  {x y : Ordinal } {z : OD }→ x o< y → _⊆_  (Ord x) (Ord y) {z}
         o<→c< lt lt1 = ordtrans lt1 lt
         
         ⊆→o< :  {x y : Ordinal } → (∀ (z : OD) → _⊆_  (Ord x) (Ord y) {z} ) →  x o< osuc y
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

         ψiso :  {ψ : OD  → Set n} {x y : OD } → ψ x → x ≡ y   → ψ y
         ψiso {ψ} t refl = t
         selection : {ψ : OD → Set n} {X y : OD} → ((X ∋ y) ∧ ψ y) ⇔ (Select X ψ ∋ y)
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
         ∩-≡ :  { a b : OD  } → ({x : OD  } → (a ∋ x → b ∋ x)) → a == ( b ∩ a )
         ∩-≡ {a} {b} inc = record {
            eq→ = λ {x} x<a → record { proj2 = x<a ;
                 proj1 = def-subst  {_} {_} {b} {x} (inc (def-subst  {_} {_} {a} {_} x<a refl (sym diso) )) refl diso  } ;
            eq← = λ {x} x<a∩b → proj2 x<a∩b }
         -- 
         -- we have t ∋ x → A ∋ x means t is a subset of A, that is ZFSubset A t == t
         -- Power A is a sup of ZFSubset A t, so Power A ∋ t
         -- 
         ord-power← : (a : Ordinal ) (t : OD) → ({x : OD} → (t ∋ x → (Ord a) ∋ x)) → Def (Ord a) ∋ t
         ord-power← a t t→A  = def-subst  {_} {_} {Def (Ord a)} {od→ord t}
                 lemma refl (lemma1 lemma-eq )where
              lemma-eq :  ZFSubset (Ord a) t == t
              eq→ lemma-eq {z} w = proj2 w 
              eq← lemma-eq {z} w = record { proj2 = w  ;
                 proj1 = def-subst  {_} {_} {(Ord a)} {z}
                    ( t→A (def-subst  {_} {_} {t} {od→ord (ord→od z)} w refl (sym diso) )) refl diso  }
              lemma1 :  {a : Ordinal } { t : OD }
                 → (eq : ZFSubset (Ord a) t == t)  → od→ord (ZFSubset (Ord a) (ord→od (od→ord t))) ≡ od→ord t
              lemma1  {a} {t} eq = subst (λ k → od→ord (ZFSubset (Ord a) k) ≡ od→ord t ) (sym oiso) (cong (λ k → od→ord k ) (==→o≡ eq ))
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
              lt1 = sup-o<  {λ x → od→ord (A ∩ ord→od x)} {od→ord t}
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
                  lemma4 (sup-o<  {λ x → od→ord (A ∩ ord→od x)} {od→ord t})
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
                 lemma3 = record { proj1 = def-subst  {_} {_} {minimul x not} {_} (proj1 s) refl (sym diso)
                                 ; proj2 = proj2 (proj2 s) } 
             lemma2 : {x₁ : Ordinal} → def od∅ x₁ → def (Select (minimul x not) (λ x₂ → (minimul x not ∋ x₂) ∧ (x ∋ x₂))) x₁
             lemma2 {y} d = ⊥-elim (empty (ord→od y) (def-subst  {_} {_} {od∅} {od→ord (ord→od y)} d refl (sym diso) ))

         extensionality0 : {A B : OD } → ((z : OD) → (A ∋ z) ⇔ (B ∋ z)) → A == B
         eq→ (extensionality0 {A} {B} eq ) {x} d = def-iso  {A} {B} (sym diso) (proj1 (eq (ord→od x))) d  
         eq← (extensionality0 {A} {B} eq ) {x} d = def-iso  {B} {A} (sym diso) (proj2 (eq (ord→od x))) d  

         extensionality : {A B w : OD  } → ((z : OD ) → (A ∋ z) ⇔ (B ∋ z)) → (w ∋ A) ⇔ (w ∋ B)
         proj1 (extensionality {A} {B} {w} eq ) d = subst (λ k → w ∋ k) ( ==→o≡ (extensionality0 {A} {B} eq) ) d
         proj2 (extensionality {A} {B} {w} eq ) d = subst (λ k → w ∋ k) (sym ( ==→o≡ (extensionality0 {A} {B} eq) )) d 

         infinity∅ : infinite  ∋ od∅ 
         infinity∅ = def-subst  {_} {_} {infinite} {od→ord (od∅ )} iφ refl lemma where
              lemma : o∅ ≡ od→ord od∅
              lemma =  let open ≡-Reasoning in begin
                    o∅
                 ≡⟨ sym diso ⟩
                    od→ord ( ord→od o∅ )
                 ≡⟨ cong ( λ k → od→ord k ) o∅≡od∅ ⟩
                    od→ord od∅
                 ∎
         infinity : (x : OD) → infinite ∋ x → infinite ∋ Union (x , (x , x ))
         infinity x lt = def-subst  {_} {_} {infinite} {od→ord (Union (x , (x , x )))} ( isuc {od→ord x} lt ) refl lemma where
               lemma :  od→ord (Union (ord→od (od→ord x) , (ord→od (od→ord x) , ord→od (od→ord x))))
                    ≡ od→ord (Union (x , (x , x)))
               lemma = cong (λ k → od→ord (Union ( k , ( k , k ) ))) oiso 

         -- Axiom of choice ( is equivalent to the existence of minimul in our case )
         -- ∀ X [ ∅ ∉ X → (∃ f : X → ⋃ X ) → ∀ A ∈ X ( f ( A ) ∈ A ) ] 
         choice-func : (X : OD  ) → {x : OD } → ¬ ( x == od∅ ) → ( X ∋ x ) → OD
         choice-func X {x} not X∋x = minimul x not
         choice : (X : OD  ) → {A : OD } → ( X∋A : X ∋ A ) → (not : ¬ ( A == od∅ )) → A ∋ choice-func X not X∋A 
         choice X {A} X∋A not = x∋minimul A not

_,_ = ZF._,_ OD→ZF
Union = ZF.Union OD→ZF
Power = ZF.Power OD→ZF
Select = ZF.Select OD→ZF
Replace = ZF.Replace OD→ZF
isZF = ZF.isZF  OD→ZF
TransFinite = IsOrdinals.TransFinite (Ordinals.isOrdinal O)
