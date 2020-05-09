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

id : {A : Set n} → A → A
id x = x

==-refl :  {  x :  OD  } → x == x
==-refl  {x} = record { eq→ = id ; eq← = id }

open  _==_ 

==-trans : { x y z : OD } →  x == y →  y == z →  x ==  z
==-trans x=y y=z  = record { eq→ = λ {m} t → eq→ y=z (eq→ x=y t) ; eq← =  λ {m} t → eq← x=y (eq← y=z t) }

==-sym : { x y  : OD } →  x == y →  y == x 
==-sym x=y = record { eq→ = λ {m} t → eq← x=y t ; eq← =  λ {m} t → eq→ x=y t }


⇔→== :  {  x y :  OD  } → ( {z : Ordinal } → def x z ⇔  def y z) → x == y 
eq→ ( ⇔→==  {x} {y}  eq ) {z} m = proj1 eq m 
eq← ( ⇔→==  {x} {y}  eq ) {z} m = proj2 eq m 

-- next assumptions are our axiom
--  it defines a subset of OD, which is called HOD, usually defined as
--     HOD = { x | TC x ⊆ OD }
--  where TC x is a transitive clusure of x, i.e. Union of all elemnts of all subset of x

record ODAxiom : Set (suc n) where      
  -- OD can be iso to a subset of Ordinal ( by means of Godel Set )
 field
  od→ord : OD  → Ordinal 
  ord→od : Ordinal  → OD  
  c<→o<  :  {x y : OD  }   → def y ( od→ord x ) → od→ord x o< od→ord y
  oiso   :  {x : OD }      → ord→od ( od→ord x ) ≡ x
  diso   :  {x : Ordinal } → od→ord ( ord→od x ) ≡ x
  ==→o≡ : { x y : OD  } → (x == y) → x ≡ y
  -- supermum as Replacement Axiom ( corresponding Ordinal of OD has maximum )
  sup-o  :  ( OD → Ordinal ) →  Ordinal 
  sup-o< :  { ψ : OD →  Ordinal } → ∀ {x : OD } → ψ x  o<  sup-o ψ 
  -- contra-position of mimimulity of supermum required in Power Set Axiom which we don't use
  -- sup-x  : {n : Level } → ( OD → Ordinal ) →  Ordinal 
  -- sup-lb : {n : Level } → { ψ : OD →  Ordinal } → {z : Ordinal }  →  z o< sup-o ψ → z o< osuc (ψ (sup-x ψ))

postulate  odAxiom : ODAxiom
open ODAxiom odAxiom

data One : Set n where
  OneObj : One

-- Ordinals in OD , the maximum
Ords : OD
Ords = record { def = λ x → One }

maxod : {x : OD} → od→ord x o< od→ord Ords
maxod {x} = c<→o< OneObj

-- Ordinal in OD ( and ZFSet ) Transitive Set
Ord : ( a : Ordinal  ) → OD 
Ord  a = record { def = λ y → y o< a }  

od∅ : OD  
od∅  = Ord o∅ 


o<→c<→OD=Ord : ( {x y : Ordinal  } → x o< y → def (ord→od y) x ) → {x : OD } →  x ≡ Ord (od→ord x)
o<→c<→OD=Ord o<→c< {x} = ==→o≡ ( record { eq→ = lemma1 ; eq← = lemma2 } ) where
   lemma1 : {y : Ordinal} → def x y → def (Ord (od→ord x)) y
   lemma1 {y} lt = subst ( λ k → k o< od→ord x ) diso (c<→o< {ord→od y} {x} (subst (λ k → def x k ) (sym diso) lt))
   lemma2 : {y : Ordinal} → def (Ord (od→ord x)) y → def x y
   lemma2 {y} lt = subst (λ k → def k y ) oiso (o<→c< {y} {od→ord x} lt )

_∋_ : ( a x : OD  ) → Set n
_∋_  a x  = def a ( od→ord x )

_c<_ : ( x a : OD  ) → Set n
x c< a = a ∋ x 

cseq : {n : Level} →  OD  →  OD 
cseq x = record { def = λ y → def x (osuc y) } where

def-subst :  {Z : OD } {X : Ordinal  }{z : OD } {x : Ordinal  }→ def Z X → Z ≡ z  →  X ≡ x  →  def z x
def-subst df refl refl = df

sup-od : ( OD  → OD ) →  OD 
sup-od ψ = Ord ( sup-o ( λ x → od→ord (ψ x)) )

sup-c< :  ( ψ : OD  →  OD ) → ∀ {x : OD } → def ( sup-od ψ ) (od→ord ( ψ x ))
sup-c<   ψ {x} = def-subst  {_} {_} {Ord ( sup-o  ( λ x → od→ord (ψ x)) )} {od→ord ( ψ x )}
        lemma refl (cong ( λ k → od→ord (ψ k) ) oiso) where
    lemma : od→ord (ψ (ord→od (od→ord x))) o< sup-o (λ x → od→ord (ψ x))
    lemma = subst₂ (λ j k → j o< k ) refl diso (o<-subst (sup-o< ) refl (sym diso)  )

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
   lemma ox ox  refl = ==-refl

o≡→== : { x y : Ordinal  } → x ≡  y →  ord→od x == ord→od y
o≡→==  {x} {.x} refl = ==-refl

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
∅<  {x} {y} d eq with eq→ (==-trans eq (==-sym ∅0) ) d
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

_,_ : OD  → OD  → OD 
x , y = record { def = λ t → (t ≡ od→ord x ) ∨ ( t ≡ od→ord y ) } --  Ord (omax (od→ord x) (od→ord y))

-- open import Relation.Binary.HeterogeneousEquality as HE using (_≅_ ) 
-- postulate f-extensionality : { n : Level}  → Relation.Binary.PropositionalEquality.Extensionality n (suc n)

in-codomain : (X : OD  ) → ( ψ : OD  → OD  ) → OD 
in-codomain  X ψ = record { def = λ x → ¬ ( (y : Ordinal ) → ¬ ( def X y ∧  ( x ≡ od→ord (ψ (ord→od y )))))  }

-- Power Set of X ( or constructible by λ y → def X (od→ord y )

ZFSubset : (A x : OD  ) → OD 
ZFSubset A x =  record { def = λ y → def A y ∧  def x y }  --   roughly x = A → Set 

Def :  (A :  OD ) → OD 
Def  A = Ord ( sup-o  ( λ x → od→ord ( ZFSubset A x) ) )   

-- _⊆_ :  ( A B : OD   ) → ∀{ x : OD  } →  Set n
-- _⊆_ A B {x} = A ∋ x →  B ∋ x

record _⊆_ ( A B : OD   ) : Set (suc n) where
  field 
     incl : { x : OD } → A ∋ x →  B ∋ x

open _⊆_

infixr  220 _⊆_

subset-lemma : {A x : OD  } → ( {y : OD } →  x ∋ y → ZFSubset A x ∋  y ) ⇔  ( x ⊆ A  )
subset-lemma  {A} {x} = record {
      proj1 = λ lt  → record { incl = λ x∋z → proj1 (lt x∋z)  }
    ; proj2 = λ x⊆A lt → record { proj1 = incl x⊆A lt ; proj2 = lt } 
   } 

open import Data.Unit

ε-induction : { ψ : OD  → Set (suc n)}
   → ( {x : OD } → ({ y : OD } →  x ∋ y → ψ y ) → ψ x )
   → (x : OD ) → ψ x
ε-induction {ψ} ind x = subst (λ k → ψ k ) oiso (ε-induction-ord (osuc (od→ord x)) <-osuc )  where
     induction : (ox : Ordinal) → ((oy : Ordinal) → oy o< ox → ψ (ord→od oy)) → ψ (ord→od ox)
     induction ox prev = ind  ( λ {y} lt → subst (λ k → ψ k ) oiso (prev (od→ord y) (o<-subst (c<→o< lt) refl diso ))) 
     ε-induction-ord : (ox : Ordinal) { oy : Ordinal } → oy o< ox → ψ (ord→od oy)
     ε-induction-ord ox {oy} lt = TransFinite {λ oy → ψ (ord→od oy)} induction oy

-- minimal-2 : (x : OD  ) → ( ne : ¬ (x == od∅ ) ) → (y : OD ) → ¬ ( def (minimal x ne) (od→ord y)) ∧ (def x (od→ord  y) )
-- minimal-2 x ne y = contra-position ( ε-induction (λ {z} ind → {!!} ) x ) ( λ p → {!!} )

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
    Replace X ψ = record { def = λ x → (x o< sup-o  ( λ x → od→ord (ψ x))) ∧ def (in-codomain X ψ) x }
    _∩_ : ( A B : ZFSet  ) → ZFSet
    A ∩ B = record { def = λ x → def A x ∧ def B x } 
    Union : OD  → OD   
    Union U = record { def = λ x → ¬ (∀ (u : Ordinal ) → ¬ ((def U u) ∧ (def (ord→od u) x)))  }
    _∈_ : ( A B : ZFSet  ) → Set n
    A ∈ B = B ∋ A
    Power : OD  → OD 
    Power A = Replace (Def (Ord (od→ord A))) ( λ x → A ∩ x )
    -- ｛_｝ : ZFSet → ZFSet
    -- ｛ x ｝ = ( x ,  x )

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
           isEquivalence  = record { refl = ==-refl ; sym = ==-sym; trans = ==-trans }
       ;   pair→  = pair→
       ;   pair←  = pair←
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
       -- ;   choice-func = choice-func
       -- ;   choice = choice
     } where

         pair→ : ( x y t : ZFSet  ) →  (x , y)  ∋ t  → ( t == x ) ∨ ( t == y ) 
         pair→ x y t (case1 t≡x ) = case1 (subst₂ (λ j k → j == k ) oiso oiso (o≡→== t≡x ))
         pair→ x y t (case2 t≡y ) = case2 (subst₂ (λ j k → j == k ) oiso oiso (o≡→== t≡y ))

         pair← : ( x y t : ZFSet  ) → ( t == x ) ∨ ( t == y ) →  (x , y)  ∋ t  
         pair← x y t (case1 t==x) = case1 (cong (λ k → od→ord k ) (==→o≡ t==x))
         pair← x y t (case2 t==y) = case2 (cong (λ k → od→ord k ) (==→o≡ t==y))

         empty : (x : OD  ) → ¬  (od∅ ∋ x)
         empty x = ¬x<0 

         o<→c< :  {x y : Ordinal } → x o< y → (Ord x) ⊆ (Ord y) 
         o<→c< lt = record { incl = λ z → ordtrans z lt }  
         
         ⊆→o< :  {x y : Ordinal } → (Ord x) ⊆ (Ord y) →  x o< osuc y
         ⊆→o< {x} {y}  lt with trio< x y 
         ⊆→o< {x} {y}  lt | tri< a ¬b ¬c = ordtrans a <-osuc
         ⊆→o< {x} {y}  lt | tri≈ ¬a b ¬c = subst ( λ k → k o< osuc y) (sym b) <-osuc
         ⊆→o< {x} {y}  lt | tri> ¬a ¬b c with (incl lt)  (o<-subst c (sym diso) refl )
         ... | ttt = ⊥-elim ( o<¬≡ refl (o<-subst ttt diso refl ))

         union→ :  (X z u : OD) → (X ∋ u) ∧ (u ∋ z) → Union X ∋ z
         union→ X z u xx not = ⊥-elim ( not (od→ord u) ( record { proj1 = proj1 xx
              ; proj2 = subst ( λ k → def k (od→ord z)) (sym oiso) (proj2 xx) } ))
         union← :  (X z : OD) (X∋z : Union X ∋ z) →  ¬  ( (u : OD ) → ¬ ((X ∋  u) ∧ (u ∋ z )))
         union← X z UX∋z =  FExists _ lemma UX∋z where
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
         --
         --
         ∩-≡ :  { a b : OD  } → ({x : OD  } → (a ∋ x → b ∋ x)) → a == ( b ∩ a )
         ∩-≡ {a} {b} inc = record {
            eq→ = λ {x} x<a → record { proj2 = x<a ;
                 proj1 = def-subst  {_} {_} {b} {x} (inc (def-subst  {_} {_} {a} {_} x<a refl (sym diso) )) refl diso  } ;
            eq← = λ {x} x<a∩b → proj2 x<a∩b }
         -- 
         -- Transitive Set case
         -- we have t ∋ x → Ord a ∋ x means t is a subset of Ord a, that is ZFSubset (Ord a) t == t
         -- Def (Ord a) is a sup of ZFSubset (Ord a) t, so Def (Ord a) ∋ t
         -- Def  A = Ord ( sup-o ( λ x → od→ord ( ZFSubset A (ord→od x )) ) )   
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
              lemma :  od→ord (ZFSubset (Ord a) (ord→od (od→ord t)) ) o< sup-o  (λ x → od→ord (ZFSubset (Ord a) x))
              lemma = sup-o<  

         -- 
         -- Every set in OD is a subset of Ordinals, so make Def (Ord (od→ord A)) first
         -- then replace of all elements of the Power set by A ∩ y
         -- 
         -- Power A = Replace (Def (Ord (od→ord A))) ( λ y → A ∩ y )

         -- we have oly double negation form because of the replacement axiom
         --
         power→ :  ( A t : OD) → Power A ∋ t → {x : OD} → t ∋ x → ¬ ¬ (A ∋ x)
         power→ A t P∋t {x} t∋x = FExists _ lemma5 lemma4 where
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
              lemma4 :  (A ∩ ord→od (od→ord t)) ≡ t
              lemma4 = let open ≡-Reasoning in begin
                    A ∩ ord→od (od→ord t)
                 ≡⟨ cong (λ k → A ∩ k) oiso ⟩
                    A ∩ t
                 ≡⟨ sym (==→o≡ ( ∩-≡ t→A )) ⟩
                    t
                 ∎
              lemma1 : od→ord t o< sup-o  (λ x → od→ord (A ∩ x))
              lemma1 = subst (λ k → od→ord k o< sup-o   (λ x → od→ord (A ∩ x)))
                  lemma4 (sup-o<  {λ x → od→ord (A ∩ x)}  )
              lemma2 :  def (in-codomain (Def (Ord (od→ord A))) (_∩_ A)) (od→ord t)
              lemma2 not = ⊥-elim ( not (od→ord t) (record { proj1 = lemma3 ; proj2 = lemma6 }) ) where
                  lemma6 : od→ord t ≡ od→ord (A ∩ ord→od (od→ord t)) 
                  lemma6 = cong ( λ k → od→ord k ) (==→o≡ (subst (λ k → t == (A ∩ k)) (sym oiso) ( ∩-≡ t→A  )))

         ord⊆power : (a : Ordinal) → (Ord (osuc a)) ⊆ (Power (Ord a)) 
         ord⊆power a = record { incl = λ {x} lt →  power← (Ord a) x (lemma lt) } where
                lemma : {x y : OD} → od→ord x o< osuc a → x ∋ y →  Ord a ∋ y
                lemma lt y<x with osuc-≡< lt
                lemma lt y<x | case1 refl = c<→o< y<x
                lemma lt y<x | case2 x<a = ordtrans (c<→o< y<x) x<a 

         continuum-hyphotheis : (a : Ordinal) → Set (suc n)
         continuum-hyphotheis a = Power (Ord a) ⊆ Ord (osuc a)

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


Union = ZF.Union OD→ZF
Power = ZF.Power OD→ZF
Select = ZF.Select OD→ZF
Replace = ZF.Replace OD→ZF
isZF = ZF.isZF  OD→ZF
