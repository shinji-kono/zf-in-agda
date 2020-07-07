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
--
--  OD is an equation on Ordinals, so it contains Ordinals. If these Ordinals have one-to-one
--  correspondence to the OD then the OD looks like a ZF Set.
--
--  If all ZF Set have supreme upper bound, the solutions of OD have to be bounded, i.e.
--  bbounded ODs are ZF Set. Unbounded ODs are classes.
--
--  In classical Set Theory, HOD is used, as a subset of OD, 
--     HOD = { x | TC x ⊆ OD }
--  where TC x is a transitive clusure of x, i.e. Union of all elemnts of all subset of x.
--  This is not possible because we don't have V yet. So we assumes HODs are bounded OD.
--
--  We also assumes HODs are isomorphic to Ordinals, which is ususally proved by Goedel number tricks.
--  There two contraints on the HOD order, one is ∋, the other one is ⊂.
--  ODs have an ovbious maximum, but Ordinals are not, but HOD has no maximum because there is an aribtrary
--  bound on each HOD.
--
--  In classical Set Theory, sup is defined by Uion, since we are working on constructive logic,
--  we need explict assumption on sup.
--
--  ==→o≡ is necessary to prove axiom of extensionality.

data One : Set n where
  OneObj : One

-- Ordinals in OD , the maximum
Ords : OD
Ords = record { def = λ x → One }

record HOD : Set (suc n) where
  field
    od : OD
    odmax : Ordinal
    <odmax : {y : Ordinal} → def od y → y o< odmax

open HOD

record ODAxiom : Set (suc n) where      
 field
  -- HOD is isomorphic to Ordinal (by means of Goedel number)
  od→ord : HOD  → Ordinal 
  ord→od : Ordinal  → HOD  
  c<→o<  :  {x y : HOD  }   → def (od y) ( od→ord x ) → od→ord x o< od→ord y
  ⊆→o≤   :  {y z : HOD  }   → ({x : Ordinal} → def (od y) x → def (od z) x ) → od→ord y o< osuc (od→ord z)
  oiso   :  {x : HOD }      → ord→od ( od→ord x ) ≡ x
  diso   :  {x : Ordinal }  → od→ord ( ord→od x ) ≡ x
  ==→o≡  :  {x y : HOD  }   → (od x == od y) → x ≡ y
  sup-o  :  (A : HOD) → (     ( x : Ordinal ) → def (od A) x →  Ordinal ) →  Ordinal 
  sup-o< :  (A : HOD) → { ψ : ( x : Ordinal ) → def (od A) x →  Ordinal } → ∀ {x : Ordinal } → (lt : def (od A) x ) → ψ x lt o<  sup-o A ψ 

postulate  odAxiom : ODAxiom
open ODAxiom odAxiom

-- OD ⇔ Ordinal leads a contradiction, so we need bounded HOD
¬OD-order : ( od→ord : OD  → Ordinal ) → ( ord→od : Ordinal  → OD ) → ( { x y : OD  }  → def y ( od→ord x ) → od→ord x o< od→ord y) → ⊥
¬OD-order od→ord ord→od c<→o< = osuc-< <-osuc (c<→o< {Ords} OneObj )

-- Open supreme upper bound leads a contradition, so we use domain restriction on sup
¬open-sup : ( sup-o : (Ordinal →  Ordinal ) → Ordinal) → ((ψ : Ordinal →  Ordinal ) → (x : Ordinal) → ψ x  o<  sup-o ψ ) → ⊥
¬open-sup sup-o sup-o< = o<> <-osuc (sup-o< next-ord (sup-o next-ord)) where
   next-ord : Ordinal → Ordinal
   next-ord x = osuc x

-- Ordinal in OD ( and ZFSet ) Transitive Set
Ord : ( a : Ordinal  ) → HOD 
Ord  a = record { od = record { def = λ y → y o< a } ; odmax = a ; <odmax = lemma } where
   lemma :  {x : Ordinal} → x o< a → x o< a
   lemma {x} lt = lt

od∅ : HOD  
od∅  = Ord o∅ 

odef : HOD → Ordinal → Set n
odef A x = def ( od A ) x

-- If we have reverse of c<→o<, everything becomes Ordinal
o<→c<→HOD=Ord : ( o<→c< : {x y : Ordinal  } → x o< y → odef (ord→od y) x ) → {x : HOD } →  x ≡ Ord (od→ord x)
o<→c<→HOD=Ord o<→c< {x} = ==→o≡ ( record { eq→ = lemma1 ; eq← = lemma2 } ) where
   lemma1 : {y : Ordinal} → odef x y → odef (Ord (od→ord x)) y
   lemma1 {y} lt = subst ( λ k → k o< od→ord x ) diso (c<→o< {ord→od y} {x} (subst (λ k → odef x k ) (sym diso) lt))
   lemma2 : {y : Ordinal} → odef (Ord (od→ord x)) y → odef x y
   lemma2 {y} lt = subst (λ k → odef k y ) oiso (o<→c< {y} {od→ord x} lt )

_∋_ : ( a x : HOD  ) → Set n
_∋_  a x  = odef a ( od→ord x )

_c<_ : ( x a : HOD  ) → Set n
x c< a = a ∋ x 

cseq : {n : Level} →  HOD  →  HOD 
cseq x = record { od = record { def = λ y → odef x (osuc y) } ; odmax = osuc (odmax x) ; <odmax = lemma } where
    lemma : {y : Ordinal} → def (od x) (osuc y) → y o< osuc (odmax x)
    lemma {y} lt = ordtrans <-osuc (ordtrans (<odmax x lt) <-osuc ) 

odef-subst :  {Z : HOD } {X : Ordinal  }{z : HOD } {x : Ordinal  }→ odef Z X → Z ≡ z  →  X ≡ x  →  odef z x
odef-subst df refl refl = df

otrans : {n : Level} {a x y : Ordinal  } → odef (Ord a) x → odef (Ord x) y → odef (Ord a) y
otrans x<a y<x = ordtrans y<x x<a

odef→o< :  {X : HOD } → {x : Ordinal } → odef X x → x o< od→ord X 
odef→o<  {X} {x} lt = o<-subst  {_} {_} {x} {od→ord X} ( c<→o< ( odef-subst  {X} {x}  lt (sym oiso) (sym diso) )) diso diso

-- avoiding lv != Zero error
orefl : { x : HOD  } → { y : Ordinal  } → od→ord x ≡ y → od→ord x ≡ y
orefl refl = refl

==-iso : { x y : HOD  } → od (ord→od (od→ord x)) == od (ord→od (od→ord y))  →  od x == od y
==-iso  {x} {y} eq = record {
      eq→ = λ d →  lemma ( eq→  eq (odef-subst d (sym oiso) refl )) ;
      eq← = λ d →  lemma ( eq←  eq (odef-subst d (sym oiso) refl ))  }
        where
           lemma : {x : HOD  } {z : Ordinal } → odef (ord→od (od→ord x)) z → odef x z
           lemma {x} {z} d = odef-subst d oiso refl

=-iso :  {x y : HOD  } → (od x == od y) ≡ (od (ord→od (od→ord x)) == od y)
=-iso  {_} {y} = cong ( λ k → od k == od y ) (sym oiso)

ord→== : { x y : HOD  } → od→ord x ≡  od→ord y →  od x == od y
ord→==  {x} {y} eq = ==-iso (lemma (od→ord x) (od→ord y) (orefl eq)) where
   lemma : ( ox oy : Ordinal  ) → ox ≡ oy →  od (ord→od ox) == od (ord→od oy)
   lemma ox ox  refl = ==-refl

o≡→== : { x y : Ordinal  } → x ≡  y →  od (ord→od x) == od (ord→od y)
o≡→==  {x} {.x} refl = ==-refl

o∅≡od∅ : ord→od (o∅ ) ≡ od∅ 
o∅≡od∅  = ==→o≡ lemma where
     lemma0 :  {x : Ordinal} → odef (ord→od o∅) x → odef od∅ x
     lemma0 {x} lt = o<-subst (c<→o<  {ord→od x} {ord→od o∅} (odef-subst  {ord→od o∅} {x} lt refl (sym diso)) ) diso diso
     lemma1 :  {x : Ordinal} → odef od∅ x → odef (ord→od o∅) x
     lemma1 {x} lt = ⊥-elim (¬x<0 lt)
     lemma : od (ord→od o∅) == od od∅
     lemma = record { eq→ = lemma0 ; eq← = lemma1 }

ord-od∅ : od→ord (od∅ ) ≡ o∅ 
ord-od∅  = sym ( subst (λ k → k ≡  od→ord (od∅ ) ) diso (cong ( λ k → od→ord k ) o∅≡od∅ ) )

∅0 : record { def = λ x →  Lift n ⊥ } == od od∅  
eq→ ∅0 {w} (lift ())
eq← ∅0 {w} lt = lift (¬x<0 lt)

∅< : { x y : HOD  } → odef x (od→ord y ) → ¬ (  od x  == od od∅  )
∅<  {x} {y} d eq with eq→ (==-trans eq (==-sym ∅0) ) d
∅<  {x} {y} d eq | lift ()
       
∅6 : { x : HOD  }  → ¬ ( x ∋ x )    --  no Russel paradox
∅6  {x} x∋x = o<¬≡ refl ( c<→o<  {x} {x} x∋x )

odef-iso : {A B : HOD } {x y : Ordinal } → x ≡ y  → (odef A y → odef B y)  → odef A x → odef B x
odef-iso refl t = t

is-o∅ : ( x : Ordinal  ) → Dec ( x ≡ o∅  )
is-o∅ x with trio< x o∅
is-o∅ x | tri< a ¬b ¬c = no ¬b
is-o∅ x | tri≈ ¬a b ¬c = yes b
is-o∅ x | tri> ¬a ¬b c = no ¬b

-- the pair
_,_ : HOD  → HOD  → HOD 
x , y = record { od = record { def = λ t → (t ≡ od→ord x ) ∨ ( t ≡ od→ord y ) } ; odmax = omax (od→ord x)  (od→ord y) ; <odmax = lemma }  where
    lemma : {t : Ordinal} → (t ≡ od→ord x) ∨ (t ≡ od→ord y) → t o< omax (od→ord x) (od→ord y)
    lemma {t} (case1 refl) = omax-x  _ _
    lemma {t} (case2 refl) = omax-y  _ _


-- open import Relation.Binary.HeterogeneousEquality as HE using (_≅_ ) 
-- postulate f-extensionality : { n : Level}  → Relation.Binary.PropositionalEquality.Extensionality n (suc n)

in-codomain : (X : HOD  ) → ( ψ : HOD  → HOD  ) → OD 
in-codomain  X ψ = record { def = λ x → ¬ ( (y : Ordinal ) → ¬ ( odef X y ∧  ( x ≡ od→ord (ψ (ord→od y )))))  }

ZFSubset : (A x : HOD  ) → HOD 
ZFSubset A x =  record { od = record { def = λ y → odef A y ∧  odef x y } ; odmax = omin (odmax A) (odmax x) ; <odmax = lemma }  where --   roughly x = A → Set 
     lemma : {y : Ordinal} → def (od A) y ∧ def (od x) y → y o< omin (odmax A) (odmax x)
     lemma {y} and = min1 (<odmax A (proj1 and)) (<odmax x (proj2 and))

record _⊆_ ( A B : HOD   ) : Set (suc n) where
  field 
     incl : { x : HOD } → A ∋ x →  B ∋ x

open _⊆_
infixr  220 _⊆_

od⊆→o≤  : {x y : HOD } → x ⊆ y → od→ord x o< osuc (od→ord y)
od⊆→o≤ {x} {y} lt  =  ⊆→o≤ {x} {y} (λ {z} x>z  → subst (λ k → def (od y) k ) diso (incl lt (subst (λ k → def (od x) k ) (sym diso) x>z )))

-- if we have od→ord (x , x) ≡ osuc (od→ord x),  ⊆→o≤ → c<→o<
pair<y : {x y : HOD } → y ∋ x  → od→ord (x , x) o< osuc (od→ord y)
pair<y {x} {y} y∋x = ⊆→o≤ lemma where
   lemma : {z : Ordinal} → def (od (x , x)) z → def (od y) z
   lemma (case1 refl) = y∋x
   lemma (case2 refl) = y∋x

-- ⊆→o≤→c<→o< : ({x : HOD} → od→ord (x , x) ≡ osuc (od→ord x) )
--    →  ({y z : HOD  }   → ({x : Ordinal} → def (od y) x → def (od z) x ) → od→ord y o< osuc (od→ord z) )
--    →   {x y : HOD  }   → def (od y) ( od→ord x ) → od→ord x o< od→ord y 
-- ⊆→o≤→c<→o< peq ⊆→o≤ {x} {y} y∋x with trio< (od→ord x) (od→ord y)
-- ⊆→o≤→c<→o< peq ⊆→o≤ {x} {y} y∋x | tri< a ¬b ¬c = a
-- ⊆→o≤→c<→o< peq ⊆→o≤ {x} {y} y∋x | tri≈ ¬a b ¬c = ⊥-elim ( o<¬≡ (peq {x}) (pair<y (subst (λ k → def (od k)  (od→ord x)) {!!} y∋x)))
-- ⊆→o≤→c<→o< peq ⊆→o≤ {x} {y} y∋x | tri> ¬a ¬b c = ⊥-elim ( o<¬≡ (peq {x}) (pair<y (subst (λ k → def (od k)  (od→ord x)) {!!} y∋x)))

subset-lemma : {A x : HOD  } → ( {y : HOD } →  x ∋ y → ZFSubset A x ∋  y ) ⇔  ( x ⊆ A  )
subset-lemma  {A} {x} = record {
      proj1 = λ lt  → record { incl = λ x∋z → proj1 (lt x∋z)  }
    ; proj2 = λ x⊆A lt → record { proj1 = incl x⊆A lt ; proj2 = lt } 
   } 

power< : {A x : HOD  } → x ⊆ A → Ord (osuc (od→ord A)) ∋ x
power< {A} {x} x⊆A = ⊆→o≤  (λ {y} x∋y → subst (λ k →  def (od A) k) diso (lemma y x∋y ) ) where
    lemma : (y : Ordinal) → def (od x) y → def (od A) (od→ord (ord→od y))
    lemma y x∋y = incl x⊆A (subst (λ k → def (od x) k ) (sym diso) x∋y )

open import Data.Unit

ε-induction : { ψ : HOD  → Set n}
   → ( {x : HOD } → ({ y : HOD } →  x ∋ y → ψ y ) → ψ x )
   → (x : HOD ) → ψ x
ε-induction {ψ} ind x = subst (λ k → ψ k ) oiso (ε-induction-ord (osuc (od→ord x)) <-osuc )  where
     induction : (ox : Ordinal) → ((oy : Ordinal) → oy o< ox → ψ (ord→od oy)) → ψ (ord→od ox)
     induction ox prev = ind  ( λ {y} lt → subst (λ k → ψ k ) oiso (prev (od→ord y) (o<-subst (c<→o< lt) refl diso ))) 
     ε-induction-ord : (ox : Ordinal) { oy : Ordinal } → oy o< ox → ψ (ord→od oy)
     ε-induction-ord ox {oy} lt = TransFinite {λ oy → ψ (ord→od oy)} induction oy

-- level trick (what'a shame)
ε-induction1 : { ψ : HOD  → Set (suc n)}
   → ( {x : HOD } → ({ y : HOD } →  x ∋ y → ψ y ) → ψ x )
   → (x : HOD ) → ψ x
ε-induction1 {ψ} ind x = subst (λ k → ψ k ) oiso (ε-induction-ord (osuc (od→ord x)) <-osuc )  where
     induction : (ox : Ordinal) → ((oy : Ordinal) → oy o< ox → ψ (ord→od oy)) → ψ (ord→od ox)
     induction ox prev = ind  ( λ {y} lt → subst (λ k → ψ k ) oiso (prev (od→ord y) (o<-subst (c<→o< lt) refl diso ))) 
     ε-induction-ord : (ox : Ordinal) { oy : Ordinal } → oy o< ox → ψ (ord→od oy)
     ε-induction-ord ox {oy} lt = TransFinite1 {λ oy → ψ (ord→od oy)} induction oy

HOD→ZF : ZF  
HOD→ZF   = record { 
    ZFSet = HOD 
    ; _∋_ = _∋_ 
    ; _≈_ = _=h=_ 
    ; ∅  = od∅
    ; _,_ = _,_
    ; Union = Union
    ; Power = Power
    ; Select = Select
    ; Replace = Replace
    ; infinite = infinite
    ; isZF = isZF 
 } where
    ZFSet = HOD             -- is less than Ords because of maxod
    Select : (X : HOD  ) → ((x : HOD  ) → Set n ) → HOD 
    Select X ψ = record { od = record { def = λ x →  ( odef X x ∧ ψ ( ord→od x )) } ; odmax = odmax X ; <odmax = λ y → <odmax X (proj1 y) }
    Replace : HOD  → (HOD  → HOD) → HOD 
    Replace X ψ = record { od = record { def = λ x → (x o< sup-o X (λ y X∋y → od→ord (ψ (ord→od y)))) ∧ def (in-codomain X ψ) x }
       ; odmax = rmax ; <odmax = rmax<} where 
          rmax : Ordinal
          rmax = sup-o X (λ y X∋y → od→ord (ψ (ord→od y)))
          rmax< :  {y : Ordinal} → (y o< rmax) ∧ def (in-codomain X ψ) y → y o< rmax
          rmax< lt = proj1 lt
    _∩_ : ( A B : ZFSet  ) → ZFSet
    A ∩ B = record { od = record { def = λ x → odef A x ∧ odef B x }
        ; odmax = omin (odmax A) (odmax B) ; <odmax = λ y → min1 (<odmax A (proj1 y)) (<odmax B (proj2 y))}
    Union : HOD  → HOD   
    Union U = record { od = record { def = λ x → ¬ (∀ (u : Ordinal ) → ¬ ((odef U u) ∧ (odef (ord→od u) x)))  }
       ; odmax = osuc (od→ord U) ; <odmax = umax< } where
           umax< :  {y : Ordinal} → ¬ ((u : Ordinal) → ¬ def (od U) u ∧ def (od (ord→od u)) y) → y o< osuc (od→ord U)
           umax< {y} not = lemma (FExists _ lemma1 not ) where
               lemma0 : {x : Ordinal} → def (od (ord→od x)) y → y o< x
               lemma0 {x} x<y = subst₂ (λ j k → j o< k ) diso  diso (c<→o< (subst (λ k → def (od (ord→od x)) k) (sym diso) x<y))
               lemma2 : {x : Ordinal} → def (od U) x → x o< od→ord U
               lemma2 {x} x<U = subst (λ k → k o< od→ord U ) diso (c<→o< (subst (λ k → def (od U) k) (sym diso) x<U))
               lemma1 : {x : Ordinal} → def (od U) x ∧ def (od (ord→od x)) y → ¬ (od→ord U o< y)
               lemma1 {x} lt u<y = o<> u<y (ordtrans (lemma0 (proj2 lt)) (lemma2 (proj1 lt)) )
               lemma : ¬ ((od→ord U) o< y ) → y o< osuc (od→ord U)
               lemma not with trio< y (od→ord U)
               lemma not | tri< a ¬b ¬c = ordtrans a <-osuc
               lemma not | tri≈ ¬a refl ¬c = <-osuc
               lemma not | tri> ¬a ¬b c = ⊥-elim (not c)
    _∈_ : ( A B : ZFSet  ) → Set n
    A ∈ B = B ∋ A

    OPwr :  (A :  HOD ) → HOD 
    OPwr  A = Ord ( sup-o (Ord (osuc (od→ord A))) ( λ x A∋x → od→ord ( ZFSubset A (ord→od x)) ) )   

    Power : HOD  → HOD 
    Power A = Replace (OPwr (Ord (od→ord A))) ( λ x → A ∩ x )
    -- ｛_｝ : ZFSet → ZFSet
    -- ｛ x ｝ = ( x ,  x )     -- better to use (x , x) directly

    data infinite-d  : ( x : Ordinal  ) → Set n where
        iφ :  infinite-d o∅
        isuc : {x : Ordinal  } →   infinite-d  x  →
                infinite-d  (od→ord ( Union (ord→od x , (ord→od x , ord→od x ) ) ))

    -- ω can be diverged in our case, since we have no restriction on the corresponding ordinal of a pair.
    -- We simply assumes nfinite-d y has a maximum.
    -- 
    -- This means that many of OD cannot be HODs because of the od→ord mapping divergence.
    -- We should have some axioms to prevent this, but it may complicate thins.
    -- 
    postulate
        ωmax : Ordinal
        <ωmax : {y : Ordinal} → infinite-d y → y o< ωmax

    infinite : HOD 
    infinite = record { od = record { def = λ x → infinite-d x } ; odmax = ωmax ; <odmax = <ωmax } 

    _=h=_ : (x y : HOD) → Set n
    x =h= y  = od x == od y

    infixr  200 _∈_
    -- infixr  230 _∩_ _∪_
    isZF : IsZF (HOD )  _∋_  _=h=_ od∅ _,_ Union Power Select Replace infinite
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
       ;   replacement→ = λ {ψ} → replacement→ {ψ}
       -- ;   choice-func = choice-func
       -- ;   choice = choice
     } where

         pair→ : ( x y t : ZFSet  ) →  (x , y)  ∋ t  → ( t =h= x ) ∨ ( t =h= y ) 
         pair→ x y t (case1 t≡x ) = case1 (subst₂ (λ j k → j =h= k ) oiso oiso (o≡→== t≡x ))
         pair→ x y t (case2 t≡y ) = case2 (subst₂ (λ j k → j =h= k ) oiso oiso (o≡→== t≡y ))

         pair← : ( x y t : ZFSet  ) → ( t =h= x ) ∨ ( t =h= y ) →  (x , y)  ∋ t  
         pair← x y t (case1 t=h=x) = case1 (cong (λ k → od→ord k ) (==→o≡ t=h=x))
         pair← x y t (case2 t=h=y) = case2 (cong (λ k → od→ord k ) (==→o≡ t=h=y))

         empty : (x : HOD  ) → ¬  (od∅ ∋ x)
         empty x = ¬x<0 

         o<→c< :  {x y : Ordinal } → x o< y → (Ord x) ⊆ (Ord y) 
         o<→c< lt = record { incl = λ z → ordtrans z lt }  
         
         ⊆→o< :  {x y : Ordinal } → (Ord x) ⊆ (Ord y) →  x o< osuc y
         ⊆→o< {x} {y}  lt with trio< x y 
         ⊆→o< {x} {y}  lt | tri< a ¬b ¬c = ordtrans a <-osuc
         ⊆→o< {x} {y}  lt | tri≈ ¬a b ¬c = subst ( λ k → k o< osuc y) (sym b) <-osuc
         ⊆→o< {x} {y}  lt | tri> ¬a ¬b c with (incl lt)  (o<-subst c (sym diso) refl )
         ... | ttt = ⊥-elim ( o<¬≡ refl (o<-subst ttt diso refl ))

         union→ :  (X z u : HOD) → (X ∋ u) ∧ (u ∋ z) → Union X ∋ z
         union→ X z u xx not = ⊥-elim ( not (od→ord u) ( record { proj1 = proj1 xx
              ; proj2 = subst ( λ k → odef k (od→ord z)) (sym oiso) (proj2 xx) } ))
         union← :  (X z : HOD) (X∋z : Union X ∋ z) →  ¬  ( (u : HOD ) → ¬ ((X ∋  u) ∧ (u ∋ z )))
         union← X z UX∋z =  FExists _ lemma UX∋z where
              lemma : {y : Ordinal} → odef X y ∧ odef (ord→od y) (od→ord z) → ¬ ((u : HOD) → ¬ (X ∋ u) ∧ (u ∋ z))
              lemma {y} xx not = not (ord→od y) record { proj1 = subst ( λ k → odef X k ) (sym diso) (proj1 xx ) ; proj2 = proj2 xx } 

         ψiso :  {ψ : HOD  → Set n} {x y : HOD } → ψ x → x ≡ y   → ψ y
         ψiso {ψ} t refl = t
         selection : {ψ : HOD → Set n} {X y : HOD} → ((X ∋ y) ∧ ψ y) ⇔ (Select X ψ ∋ y)
         selection {ψ} {X} {y} = record {
              proj1 = λ cond → record { proj1 = proj1 cond ; proj2 = ψiso {ψ} (proj2 cond) (sym oiso)  }
            ; proj2 = λ select → record { proj1 = proj1 select  ; proj2 =  ψiso {ψ} (proj2 select) oiso  }
           }
         sup-c< :  (ψ : HOD → HOD) → {X x : HOD} → X ∋ x  → od→ord (ψ x) o< (sup-o X (λ y X∋y → od→ord (ψ (ord→od y))))
         sup-c< ψ {X} {x} lt = subst (λ k → od→ord (ψ k) o< _ ) oiso (sup-o< X lt )
         replacement← : {ψ : HOD → HOD} (X x : HOD) →  X ∋ x → Replace X ψ ∋ ψ x
         replacement← {ψ} X x lt = record { proj1 =  sup-c< ψ {X} {x} lt ; proj2 = lemma } where 
             lemma : def (in-codomain X ψ) (od→ord (ψ x))
             lemma not = ⊥-elim ( not ( od→ord x ) (record { proj1 = lt ; proj2 = cong (λ k → od→ord (ψ k)) (sym oiso)} ))
         replacement→ : {ψ : HOD → HOD} (X x : HOD) → (lt : Replace X ψ ∋ x) → ¬ ( (y : HOD) → ¬ (x =h= ψ y))
         replacement→ {ψ} X x lt = contra-position lemma (lemma2 (proj2 lt)) where
            lemma2 :  ¬ ((y : Ordinal) → ¬ odef X y ∧ ((od→ord x) ≡ od→ord (ψ (ord→od y))))
                    → ¬ ((y : Ordinal) → ¬ odef X y ∧ (ord→od (od→ord x) =h= ψ (ord→od y)))
            lemma2 not not2  = not ( λ y d →  not2 y (record { proj1 = proj1 d ; proj2 = lemma3 (proj2 d)})) where
                lemma3 : {y : Ordinal } → (od→ord x ≡ od→ord (ψ (ord→od  y))) → (ord→od (od→ord x) =h= ψ (ord→od y))  
                lemma3 {y} eq = subst (λ k  → ord→od (od→ord x) =h= k ) oiso (o≡→== eq )
            lemma :  ( (y : HOD) → ¬ (x =h= ψ y)) → ( (y : Ordinal) → ¬ odef X y ∧ (ord→od (od→ord x) =h= ψ (ord→od y)) )
            lemma not y not2 = not (ord→od y) (subst (λ k → k =h= ψ (ord→od y)) oiso  ( proj2 not2 ))

         ---
         --- Power Set
         ---
         ---    First consider ordinals in HOD
         ---
         --- ZFSubset A x =  record { def = λ y → odef A y ∧  odef x y }                   subset of A
         --
         --
         ∩-≡ :  { a b : HOD  } → ({x : HOD  } → (a ∋ x → b ∋ x)) → a =h= ( b ∩ a )
         ∩-≡ {a} {b} inc = record {
            eq→ = λ {x} x<a → record { proj2 = x<a ;
                 proj1 = odef-subst  {_} {_} {b} {x} (inc (odef-subst  {_} {_} {a} {_} x<a refl (sym diso) )) refl diso  } ;
            eq← = λ {x} x<a∩b → proj2 x<a∩b }
         -- 
         -- Transitive Set case
         -- we have t ∋ x → Ord a ∋ x means t is a subset of Ord a, that is ZFSubset (Ord a) t =h= t
         -- OPwr (Ord a) is a sup of ZFSubset (Ord a) t, so OPwr (Ord a) ∋ t
         -- OPwr  A = Ord ( sup-o ( λ x → od→ord ( ZFSubset A (ord→od x )) ) )   
         -- 
         ord-power← : (a : Ordinal ) (t : HOD) → ({x : HOD} → (t ∋ x → (Ord a) ∋ x)) → OPwr (Ord a) ∋ t
         ord-power← a t t→A  = odef-subst  {_} {_} {OPwr (Ord a)} {od→ord t}
                 lemma refl (lemma1 lemma-eq )where
              lemma-eq :  ZFSubset (Ord a) t =h= t
              eq→ lemma-eq {z} w = proj2 w 
              eq← lemma-eq {z} w = record { proj2 = w  ;
                 proj1 = odef-subst  {_} {_} {(Ord a)} {z}
                    ( t→A (odef-subst  {_} {_} {t} {od→ord (ord→od z)} w refl (sym diso) )) refl diso  }
              lemma1 :  {a : Ordinal } { t : HOD }
                 → (eq : ZFSubset (Ord a) t =h= t)  → od→ord (ZFSubset (Ord a) (ord→od (od→ord t))) ≡ od→ord t
              lemma1  {a} {t} eq = subst (λ k → od→ord (ZFSubset (Ord a) k) ≡ od→ord t ) (sym oiso) (cong (λ k → od→ord k ) (==→o≡ eq ))
              lemma2 : (od→ord t) o< (osuc (od→ord (Ord a)))
              lemma2 = ⊆→o≤  {t} {Ord a} (λ {x} x<t → subst (λ k → def (od (Ord a)) k) diso (t→A (subst (λ k → def (od t) k) (sym diso) x<t))) 
              lemma :  od→ord (ZFSubset (Ord a) (ord→od (od→ord t)) ) o< sup-o (Ord (osuc (od→ord (Ord a)))) (λ x lt → od→ord (ZFSubset (Ord a) (ord→od x)))
              lemma = sup-o< _ lemma2

         -- 
         -- Every set in HOD is a subset of Ordinals, so make OPwr (Ord (od→ord A)) first
         -- then replace of all elements of the Power set by A ∩ y
         -- 
         -- Power A = Replace (OPwr (Ord (od→ord A))) ( λ y → A ∩ y )

         -- we have oly double negation form because of the replacement axiom
         --
         power→ :  ( A t : HOD) → Power A ∋ t → {x : HOD} → t ∋ x → ¬ ¬ (A ∋ x)
         power→ A t P∋t {x} t∋x = FExists _ lemma5 lemma4 where
              a = od→ord A
              lemma2 : ¬ ( (y : HOD) → ¬ (t =h=  (A ∩ y)))
              lemma2 = replacement→ {λ x → A ∩ x} (OPwr (Ord (od→ord A))) t P∋t
              lemma3 : (y : HOD) → t =h= ( A ∩ y ) → ¬ ¬ (A ∋ x)
              lemma3 y eq not = not (proj1 (eq→ eq t∋x))
              lemma4 : ¬ ((y : Ordinal) → ¬ (t =h= (A ∩ ord→od y)))
              lemma4 not = lemma2 ( λ y not1 → not (od→ord y) (subst (λ k → t =h= ( A ∩ k )) (sym oiso) not1 ))
              lemma5 : {y : Ordinal} → t =h= (A ∩ ord→od y) →  ¬ ¬  (odef A (od→ord x))
              lemma5 {y} eq not = (lemma3 (ord→od y) eq) not

         power← :  (A t : HOD) → ({x : HOD} → (t ∋ x → A ∋ x)) → Power A ∋ t
         power← A t t→A = record { proj1 = lemma1 ; proj2 = lemma2 } where 
              a = od→ord A
              lemma0 : {x : HOD} → t ∋ x → Ord a ∋ x
              lemma0 {x} t∋x = c<→o< (t→A t∋x)
              lemma3 : OPwr (Ord a) ∋ t
              lemma3 = ord-power← a t lemma0
              lemma4 :  (A ∩ ord→od (od→ord t)) ≡ t
              lemma4 = let open ≡-Reasoning in begin
                    A ∩ ord→od (od→ord t)
                 ≡⟨ cong (λ k → A ∩ k) oiso ⟩
                    A ∩ t
                 ≡⟨ sym (==→o≡ ( ∩-≡ {t} {A} t→A )) ⟩
                    t
                 ∎
              sup1 : Ordinal
              sup1 =  sup-o (Ord (osuc (od→ord (Ord (od→ord A))))) (λ x A∋x → od→ord (ZFSubset (Ord (od→ord A)) (ord→od x)))
              lemma9 : def (od (Ord (Ordinals.osuc O (od→ord (Ord (od→ord A)))))) (od→ord (Ord (od→ord A)))
              lemma9 = <-osuc 
              lemmab : od→ord (ZFSubset (Ord (od→ord A)) (ord→od (od→ord (Ord (od→ord A) )))) o< sup1
              lemmab = sup-o< (Ord (osuc (od→ord (Ord (od→ord A))))) lemma9 
              lemmad : Ord (osuc (od→ord A)) ∋ t
              lemmad = ⊆→o≤ (λ {x} lt → subst (λ k → def (od A) k ) diso (t→A (subst (λ k → def (od t) k ) (sym diso) lt))) 
              lemmac : ZFSubset (Ord (od→ord A)) (ord→od (od→ord (Ord (od→ord A) ))) =h= Ord (od→ord A)
              lemmac = record { eq→ = lemmaf ; eq← = lemmag } where
                 lemmaf : {x : Ordinal} → def (od (ZFSubset (Ord (od→ord A)) (ord→od (od→ord (Ord (od→ord A)))))) x → def (od (Ord (od→ord A))) x
                 lemmaf {x} lt = proj1 lt
                 lemmag :  {x : Ordinal} → def (od (Ord (od→ord A))) x → def (od (ZFSubset (Ord (od→ord A)) (ord→od (od→ord (Ord (od→ord A)))))) x
                 lemmag {x} lt = record { proj1 = lt ; proj2 = subst (λ k → def (od k) x) (sym oiso) lt } 
              lemmae : od→ord (ZFSubset (Ord (od→ord A)) (ord→od (od→ord (Ord (od→ord A))))) ≡ od→ord (Ord (od→ord A))
              lemmae = cong (λ k → od→ord k ) ( ==→o≡ lemmac)
              lemma7 : def (od (OPwr (Ord (od→ord A)))) (od→ord t)
              lemma7 with osuc-≡< lemmad
              lemma7 | case2 lt = ordtrans (c<→o< lt) (subst (λ k → k o< sup1) lemmae lemmab )
              lemma7 | case1 eq with osuc-≡< (⊆→o≤ {ord→od (od→ord t)} {ord→od (od→ord (Ord (od→ord t)))} (λ {x} lt → lemmah lt )) where
                  lemmah : {x : Ordinal } → def (od (ord→od (od→ord t))) x → def (od (ord→od (od→ord (Ord (od→ord t))))) x
                  lemmah {x} lt = subst (λ k → def (od k) x ) (sym oiso) (subst (λ k → k o< (od→ord t))
                      diso
                      (c<→o< (subst₂ (λ j k → def (od j)  k) oiso (sym diso) lt )))
              lemma7 | case1 eq | case1 eq1 = subst (λ k → k o< sup1) (trans lemmae lemmai) lemmab where 
                  lemmai : od→ord (Ord (od→ord A)) ≡ od→ord t
                  lemmai = let open ≡-Reasoning in begin
                           od→ord (Ord (od→ord A)) 
                        ≡⟨ sym (cong (λ k → od→ord (Ord k)) eq) ⟩
                           od→ord (Ord (od→ord t)) 
                        ≡⟨ sym diso ⟩
                           od→ord (ord→od (od→ord (Ord (od→ord t))))
                        ≡⟨ sym eq1 ⟩
                           od→ord (ord→od (od→ord t))
                        ≡⟨ diso ⟩
                           od→ord t 
                        ∎
              lemma7 | case1 eq | case2 lt = ordtrans lemmaj (subst (λ k → k o< sup1) lemmae lemmab ) where
                  lemmak : od→ord (ord→od (od→ord (Ord (od→ord t)))) ≡ od→ord (Ord (od→ord A))
                  lemmak = let open ≡-Reasoning in begin
                           od→ord (ord→od (od→ord (Ord (od→ord t))))
                        ≡⟨ diso ⟩
                           od→ord (Ord (od→ord t))
                        ≡⟨ cong (λ k → od→ord (Ord k)) eq ⟩
                           od→ord (Ord (od→ord A))
                        ∎
                  lemmaj : od→ord t o< od→ord (Ord (od→ord A))
                  lemmaj = subst₂ (λ j k → j o< k ) diso lemmak lt 
              lemma1 : od→ord t o< sup-o (OPwr (Ord (od→ord A))) (λ x lt → od→ord (A ∩ (ord→od x)))
              lemma1 = subst (λ k → od→ord k o< sup-o (OPwr (Ord (od→ord A)))  (λ x lt → od→ord (A ∩ (ord→od x))))
                  lemma4 (sup-o< (OPwr (Ord (od→ord A))) lemma7 )
              lemma2 :  def (in-codomain (OPwr (Ord (od→ord A))) (_∩_ A)) (od→ord t)
              lemma2 not = ⊥-elim ( not (od→ord t) (record { proj1 = lemma3 ; proj2 = lemma6 }) ) where
                  lemma6 : od→ord t ≡ od→ord (A ∩ ord→od (od→ord t)) 
                  lemma6 = cong ( λ k → od→ord k ) (==→o≡ (subst (λ k → t =h= (A ∩ k)) (sym oiso) ( ∩-≡ {t} {A} t→A  )))


         ord⊆power : (a : Ordinal) → (Ord (osuc a)) ⊆ (Power (Ord a)) 
         ord⊆power a = record { incl = λ {x} lt →  power← (Ord a) x (lemma lt) } where
                lemma : {x y : HOD} → od→ord x o< osuc a → x ∋ y →  Ord a ∋ y
                lemma lt y<x with osuc-≡< lt
                lemma lt y<x | case1 refl = c<→o< y<x
                lemma lt y<x | case2 x<a = ordtrans (c<→o< y<x) x<a 

         continuum-hyphotheis : (a : Ordinal) → Set (suc n)
         continuum-hyphotheis a = Power (Ord a) ⊆ Ord (osuc a)

         extensionality0 : {A B : HOD } → ((z : HOD) → (A ∋ z) ⇔ (B ∋ z)) → A =h= B
         eq→ (extensionality0 {A} {B} eq ) {x} d = odef-iso  {A} {B} (sym diso) (proj1 (eq (ord→od x))) d  
         eq← (extensionality0 {A} {B} eq ) {x} d = odef-iso  {B} {A} (sym diso) (proj2 (eq (ord→od x))) d  

         extensionality : {A B w : HOD  } → ((z : HOD ) → (A ∋ z) ⇔ (B ∋ z)) → (w ∋ A) ⇔ (w ∋ B)
         proj1 (extensionality {A} {B} {w} eq ) d = subst (λ k → w ∋ k) ( ==→o≡ (extensionality0 {A} {B} eq) ) d
         proj2 (extensionality {A} {B} {w} eq ) d = subst (λ k → w ∋ k) (sym ( ==→o≡ (extensionality0 {A} {B} eq) )) d 

         infinity∅ : infinite  ∋ od∅ 
         infinity∅ = odef-subst  {_} {_} {infinite} {od→ord (od∅ )} iφ refl lemma where
              lemma : o∅ ≡ od→ord od∅
              lemma =  let open ≡-Reasoning in begin
                    o∅
                 ≡⟨ sym diso ⟩
                    od→ord ( ord→od o∅ )
                 ≡⟨ cong ( λ k → od→ord k ) o∅≡od∅ ⟩
                    od→ord od∅
                 ∎
         infinity : (x : HOD) → infinite ∋ x → infinite ∋ Union (x , (x , x ))
         infinity x lt = odef-subst  {_} {_} {infinite} {od→ord (Union (x , (x , x )))} ( isuc {od→ord x} lt ) refl lemma where
               lemma :  od→ord (Union (ord→od (od→ord x) , (ord→od (od→ord x) , ord→od (od→ord x))))
                    ≡ od→ord (Union (x , (x , x)))
               lemma = cong (λ k → od→ord (Union ( k , ( k , k ) ))) oiso 


Union = ZF.Union HOD→ZF
Power = ZF.Power HOD→ZF
Select = ZF.Select HOD→ZF
Replace = ZF.Replace HOD→ZF
isZF = ZF.isZF  HOD→ZF
