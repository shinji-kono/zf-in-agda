{-# OPTIONS --allow-unsolved-metas #-} 
open import Level
open import Ordinals
module OD {n : Level } (O : Ordinals {n} ) where

open import zf
open import Data.Nat renaming ( zero to Zero ; suc to Suc ;  ℕ to Nat ; _⊔_ to _n⊔_ ) 
open import  Relation.Binary.PropositionalEquality hiding ( [_] )
open import Data.Nat.Properties 
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary  hiding (_⇔_)
open import Relation.Binary.Core hiding (_⇔_)

open import logic
import OrdUtil
open import nat

open Ordinals.Ordinals  O
open Ordinals.IsOrdinals isOrdinal 
open Ordinals.IsNext isNext 
open OrdUtil O

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

==-refl :  {  x :  OD  } → x == x
==-refl  {x} = record { eq→ = λ x → x ; eq← = λ x → x }

open  _==_ 

==-trans : { x y z : OD } →  x == y →  y == z →  x ==  z
==-trans x=y y=z  = record { eq→ = λ {m} t → eq→ y=z (eq→ x=y t) ; eq← =  λ {m} t → eq← x=y (eq← y=z t) }

==-sym : { x y  : OD } →  x == y →  y == x 
==-sym x=y = record { eq→ = λ {m} t → eq← x=y t ; eq← =  λ {m} t → eq→ x=y t }


⇔→== :  {  x y :  OD  } → ( {z : Ordinal } → (def x z ⇔  def y z)) → x == y 
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
  & : HOD  → Ordinal 
  * : Ordinal  → HOD  
  c<→o<  :  {x y : HOD  }   → def (od y) ( & x ) → & x o< & y
  ⊆→o≤   :  {y z : HOD  }   → ({x : Ordinal} → def (od y) x → def (od z) x ) → & y o< osuc (& z)
  *iso   :  {x : HOD }      → * ( & x ) ≡ x
  &iso   :  {x : Ordinal }  → & ( * x ) ≡ x
  ==→o≡  :  {x y : HOD  }   → (od x == od y) → x ≡ y
  sup-o  :  (A : HOD) → (     ( x : Ordinal ) → def (od A) x →  Ordinal ) →  Ordinal 
  sup-o< :  (A : HOD) → { ψ : ( x : Ordinal ) → def (od A) x →  Ordinal } → ∀ {x : Ordinal } → (lt : def (od A) x ) → ψ x lt o<  sup-o A ψ 
-- possible order restriction
  ho< : {x : HOD} → & x o< next (odmax x)


postulate  odAxiom : ODAxiom
open ODAxiom odAxiom

-- odmax minimality
--
-- since we have ==→o≡ , so odmax have to be unique. We should have odmaxmin in HOD.
-- We can calculate the minimum using sup but it is tedius.
-- Only Select has non minimum odmax. 
-- We have the same problem on 'def' itself, but we leave it.

odmaxmin : Set (suc n)
odmaxmin = (y : HOD) (z : Ordinal) → ((x : Ordinal)→ def (od y) x → x o< z) → odmax y o< osuc z

-- OD ⇔ Ordinal leads a contradiction, so we need bounded HOD
¬OD-order : ( & : OD  → Ordinal ) → ( * : Ordinal  → OD ) → ( { x y : OD  }  → def y ( & x ) → & x o< & y) → ⊥
¬OD-order & * c<→o< = osuc-< <-osuc (c<→o< {Ords} OneObj )

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

_∋_ : ( a x : HOD  ) → Set n
_∋_  a x  = odef a ( & x )

-- _c<_ : ( x a : HOD  ) → Set n
-- x c< a = a ∋ x 

d→∋ : ( a : HOD  ) { x : Ordinal} → odef a x → a ∋ (* x)
d→∋ a lt = subst (λ k → odef a k ) (sym &iso) lt

-- odef-subst :  {Z : HOD } {X : Ordinal  }{z : HOD } {x : Ordinal  }→ odef Z X → Z ≡ z  →  X ≡ x  →  odef z x
-- odef-subst df refl refl = df

otrans : {a x y : Ordinal  } → odef (Ord a) x → odef (Ord x) y → odef (Ord a) y
otrans x<a y<x = ordtrans y<x x<a

-- If we have reverse of c<→o<, everything becomes Ordinal
∈→c<→HOD=Ord : ( o<→c< : {x y : Ordinal  } → x o< y → odef (* y) x ) → {x : HOD } →  x ≡ Ord (& x)
∈→c<→HOD=Ord o<→c< {x} = ==→o≡ ( record { eq→ = lemma1 ; eq← = lemma2 } ) where
   lemma1 : {y : Ordinal} → odef x y → odef (Ord (& x)) y
   lemma1 {y} lt = subst ( λ k → k o< & x ) &iso (c<→o< {* y} {x} (d→∋ x lt))
   lemma2 : {y : Ordinal} → odef (Ord (& x)) y → odef x y
   lemma2 {y} lt = subst (λ k → odef k y ) *iso (o<→c< {y} {& x} lt )

-- avoiding lv != Zero error
orefl : { x : HOD  } → { y : Ordinal  } → & x ≡ y → & x ≡ y
orefl refl = refl

==-iso : { x y : HOD  } → od (* (& x)) == od (* (& y))  →  od x == od y
==-iso  {x} {y} eq = record {
      eq→ = λ {z} d →  lemma ( eq→  eq (subst (λ k → odef k z ) (sym *iso) d )) ; 
      eq← = λ {z} d →  lemma ( eq←  eq (subst (λ k → odef k z ) (sym *iso) d )) } 
        where
           lemma : {x : HOD  } {z : Ordinal } → odef (* (& x)) z → odef x z
           lemma {x} {z} d = subst (λ k → odef k z) (*iso) d 

=-iso :  {x y : HOD  } → (od x == od y) ≡ (od (* (& x)) == od y)
=-iso  {_} {y} = cong ( λ k → od k == od y ) (sym *iso)

ord→== : { x y : HOD  } → & x ≡  & y →  od x == od y
ord→==  {x} {y} eq = ==-iso (lemma (& x) (& y) (orefl eq)) where
   lemma : ( ox oy : Ordinal  ) → ox ≡ oy →  od (* ox) == od (* oy)
   lemma ox ox  refl = ==-refl

o≡→== : { x y : Ordinal  } → x ≡  y →  od (* x) == od (* y)
o≡→==  {x} {.x} refl = ==-refl

o∅≡od∅ : * (o∅ ) ≡ od∅ 
o∅≡od∅  = ==→o≡ lemma where
     lemma0 :  {x : Ordinal} → odef (* o∅) x → odef od∅ x
     lemma0 {x} lt with c<→o< {* x} {* o∅} (subst (λ k → odef (* o∅) k ) (sym &iso) lt)
     ... | t = subst₂ (λ j k → j o< k ) &iso &iso t
     lemma1 :  {x : Ordinal} → odef od∅ x → odef (* o∅) x
     lemma1 {x} lt = ⊥-elim (¬x<0 lt)
     lemma : od (* o∅) == od od∅
     lemma = record { eq→ = lemma0 ; eq← = lemma1 }

ord-od∅ : & (od∅ ) ≡ o∅ 
ord-od∅  = sym ( subst (λ k → k ≡  & (od∅ ) ) &iso (cong ( λ k → & k ) o∅≡od∅ ) )

≡o∅→=od∅  : {x : HOD} → & x ≡ o∅ → od x == od od∅
≡o∅→=od∅ {x} eq = record { eq→ = λ {y} lt → ⊥-elim ( ¬x<0 {y} (subst₂ (λ j k → j o< k ) &iso eq ( c<→o< {* y} {x} (d→∋ x lt))))
    ; eq← = λ {y} lt → ⊥-elim ( ¬x<0 lt )}  

=od∅→≡o∅  : {x : HOD} → od x == od od∅ → & x ≡ o∅ 
=od∅→≡o∅ {x} eq = trans (cong (λ k → & k ) (==→o≡ {x} {od∅} eq)) ord-od∅

∅0 : record { def = λ x →  Lift n ⊥ } == od od∅  
eq→ ∅0 {w} (lift ())
eq← ∅0 {w} lt = lift (¬x<0 lt)

∅< : { x y : HOD  } → odef x (& y ) → ¬ (  od x  == od od∅  )
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
x , y = record { od = record { def = λ t → (t ≡ & x ) ∨ ( t ≡ & y ) } ; odmax = omax (& x)  (& y) ; <odmax = lemma }  where
    lemma : {t : Ordinal} → (t ≡ & x) ∨ (t ≡ & y) → t o< omax (& x) (& y)
    lemma {t} (case1 refl) = omax-x  _ _
    lemma {t} (case2 refl) = omax-y  _ _

pair<y : {x y : HOD } → y ∋ x  → & (x , x) o< osuc (& y)
pair<y {x} {y} y∋x = ⊆→o≤ lemma where
   lemma : {z : Ordinal} → def (od (x , x)) z → def (od y) z
   lemma (case1 refl) = y∋x
   lemma (case2 refl) = y∋x

-- another possible restriction. We reqest no minimality on odmax, so it may arbitrary larger.
odmax<&  : { x y : HOD } → x ∋ y →  Set n
odmax<& {x} {y} x∋y = odmax x o< & x

in-codomain : (X : HOD  ) → ( ψ : HOD  → HOD  ) → OD 
in-codomain  X ψ = record { def = λ x → ¬ ( (y : Ordinal ) → ¬ ( odef X y ∧  ( x ≡ & (ψ (* y )))))  }

_∩_ : ( A B : HOD ) → HOD 
A ∩ B = record { od = record { def = λ x → odef A x ∧ odef B x }
        ; odmax = omin (odmax A) (odmax B) ; <odmax = λ y → min1 (<odmax A (proj1 y)) (<odmax B (proj2 y))}

record _⊆_ ( A B : HOD   ) : Set (suc n) where
  field 
     incl : { x : HOD } → A ∋ x →  B ∋ x

open _⊆_
infixr  220 _⊆_

-- if we have & (x , x) ≡ osuc (& x),  ⊆→o≤ → c<→o<
⊆→o≤→c<→o< : ({x : HOD} → & (x , x) ≡ osuc (& x) )
   →  ({y z : HOD  }   → ({x : Ordinal} → def (od y) x → def (od z) x ) → & y o< osuc (& z) )
   →   {x y : HOD  }   → def (od y) ( & x ) → & x o< & y 
⊆→o≤→c<→o< peq ⊆→o≤ {x} {y} y∋x with trio< (& x) (& y)
⊆→o≤→c<→o< peq ⊆→o≤ {x} {y} y∋x | tri< a ¬b ¬c = a
⊆→o≤→c<→o< peq ⊆→o≤ {x} {y} y∋x | tri≈ ¬a b ¬c = ⊥-elim ( o<¬≡ (peq {x}) (pair<y (subst (λ k → k ∋ x) (sym ( ==→o≡ {x} {y} (ord→== b))) y∋x )))
⊆→o≤→c<→o< peq ⊆→o≤ {x} {y} y∋x | tri> ¬a ¬b c =
  ⊥-elim ( o<> (⊆→o≤ {x , x} {y} y⊆x,x ) lemma1 ) where
    lemma : {z : Ordinal} → (z ≡ & x) ∨ (z ≡ & x) → & x ≡ z
    lemma (case1 refl) = refl
    lemma (case2 refl) = refl
    y⊆x,x : {z : Ordinal} → def (od (x , x)) z → def (od y) z
    y⊆x,x {z} lt = subst (λ k → def (od y) k ) (lemma lt) y∋x 
    lemma1 : osuc (& y) o< & (x , x)
    lemma1 = subst (λ k → osuc (& y) o< k ) (sym (peq {x})) (osucc c ) 

ε-induction : { ψ : HOD  → Set (suc n)}
   → ( {x : HOD } → ({ y : HOD } →  x ∋ y → ψ y ) → ψ x )
   → (x : HOD ) → ψ x
ε-induction {ψ} ind x = subst (λ k → ψ k ) *iso (ε-induction-ord (osuc (& x)) <-osuc )  where
     induction : (ox : Ordinal) → ((oy : Ordinal) → oy o< ox → ψ (* oy)) → ψ (* ox)
     induction ox prev = ind  ( λ {y} lt → subst (λ k → ψ k ) *iso (prev (& y) (o<-subst (c<→o< lt) refl &iso ))) 
     ε-induction-ord : (ox : Ordinal) { oy : Ordinal } → oy o< ox → ψ (* oy)
     ε-induction-ord ox {oy} lt = TransFinite {λ oy → ψ (* oy)} induction oy

Select : (X : HOD  ) → ((x : HOD  ) → Set n ) → HOD 
Select X ψ = record { od = record { def = λ x →  ( odef X x ∧ ψ ( * x )) } ; odmax = odmax X ; <odmax = λ y → <odmax X (proj1 y) }

Replace : HOD  → (HOD  → HOD) → HOD 
Replace X ψ = record { od = record { def = λ x → (x o< sup-o X (λ y X∋y → & (ψ (* y)))) ∧ def (in-codomain X ψ) x }
    ; odmax = rmax ; <odmax = rmax<} where 
        rmax : Ordinal
        rmax = sup-o X (λ y X∋y → & (ψ (* y)))
        rmax< :  {y : Ordinal} → (y o< rmax) ∧ def (in-codomain X ψ) y → y o< rmax
        rmax< lt = proj1 lt

--
-- If we have LEM, Replace' is equivalent to Replace 
--
in-codomain' : (X : HOD  ) → ((x : HOD) → X ∋ x → HOD) → OD 
in-codomain'  X ψ = record { def = λ x → ¬ ( (y : Ordinal ) → ¬ ( odef X y ∧  ((lt : odef X y) →  x ≡ & (ψ (* y ) (d→∋ X lt) ))))  }
Replace' : (X : HOD)  → ((x : HOD) → X ∋ x → HOD) → HOD 
Replace' X ψ = record { od = record { def = λ x → (x o< sup-o X (λ y X∋y → & (ψ (* y) (d→∋ X X∋y) ))) ∧ def (in-codomain' X ψ) x }
      ; odmax = rmax ; <odmax = rmax< } where
        rmax : Ordinal
        rmax = sup-o X (λ y X∋y → & (ψ (* y) (d→∋ X X∋y)))
        rmax< :  {y : Ordinal} → (y o< rmax) ∧ def (in-codomain' X ψ) y → y o< rmax
        rmax< lt = proj1 lt

Union : HOD  → HOD   
Union U = record { od = record { def = λ x → ¬ (∀ (u : Ordinal ) → ¬ ((odef U u) ∧ (odef (* u) x)))  }
    ; odmax = osuc (& U) ; <odmax = umax< } where
        umax< :  {y : Ordinal} → ¬ ((u : Ordinal) → ¬ def (od U) u ∧ def (od (* u)) y) → y o< osuc (& U)
        umax< {y} not = lemma (FExists _ lemma1 not ) where
            lemma0 : {x : Ordinal} → def (od (* x)) y → y o< x
            lemma0 {x} x<y = subst₂ (λ j k → j o< k ) &iso  &iso (c<→o< (d→∋ (* x) x<y ))
            lemma2 : {x : Ordinal} → def (od U) x → x o< & U
            lemma2 {x} x<U = subst (λ k → k o< & U ) &iso (c<→o< (d→∋ U x<U)) 
            lemma1 : {x : Ordinal} → def (od U) x ∧ def (od (* x)) y → ¬ (& U o< y)
            lemma1 {x} lt u<y = o<> u<y (ordtrans (lemma0 (proj2 lt)) (lemma2 (proj1 lt)) )
            lemma : ¬ ((& U) o< y ) → y o< osuc (& U)
            lemma not with trio< y (& U)
            lemma not | tri< a ¬b ¬c = ordtrans a <-osuc
            lemma not | tri≈ ¬a refl ¬c = <-osuc
            lemma not | tri> ¬a ¬b c = ⊥-elim (not c)
_∈_ : ( A B : HOD  ) → Set n
A ∈ B = B ∋ A

OPwr :  (A :  HOD ) → HOD 
OPwr  A = Ord ( sup-o (Ord (osuc (& A))) ( λ x A∋x → & ( A ∩ (* x)) ) )   

Power : HOD  → HOD 
Power A = Replace (OPwr (Ord (& A))) ( λ x → A ∩ x )
-- ｛_｝ : ZFSet → ZFSet
-- ｛ x ｝ = ( x ,  x )     -- better to use (x , x) directly

union→ :  (X z u : HOD) → (X ∋ u) ∧ (u ∋ z) → Union X ∋ z
union→ X z u xx not = ⊥-elim ( not (& u) ( ⟪ proj1 xx
    , subst ( λ k → odef k (& z)) (sym *iso) (proj2 xx) ⟫ ))
union← :  (X z : HOD) (X∋z : Union X ∋ z) →  ¬  ( (u : HOD ) → ¬ ((X ∋  u) ∧ (u ∋ z )))
union← X z UX∋z =  FExists _ lemma UX∋z where
    lemma : {y : Ordinal} → odef X y ∧ odef (* y) (& z) → ¬ ((u : HOD) → ¬ (X ∋ u) ∧ (u ∋ z))
    lemma {y} xx not = not (* y) ⟪ d→∋ X (proj1 xx) , proj2 xx ⟫

data infinite-d  : ( x : Ordinal  ) → Set n where
    iφ :  infinite-d o∅
    isuc : {x : Ordinal  } →   infinite-d  x  →
            infinite-d  (& ( Union (* x , (* x , * x ) ) ))

-- ω can be diverged in our case, since we have no restriction on the corresponding ordinal of a pair.
-- We simply assumes infinite-d y has a maximum.
-- 
-- This means that many of OD may not be HODs because of the & mapping divergence.
-- We should have some axioms to prevent this such as & x o< next (odmax x).
-- 
-- postulate
--     ωmax : Ordinal
--     <ωmax : {y : Ordinal} → infinite-d y → y o< ωmax
-- 
-- infinite : HOD 
-- infinite = record { od = record { def = λ x → infinite-d x } ; odmax = ωmax ; <odmax = <ωmax } 

infinite : HOD 
infinite = record { od = record { def = λ x → infinite-d x } ; odmax = next o∅ ; <odmax = lemma }  where
    u : (y : Ordinal ) → HOD
    u y = Union (* y , (* y , * y))
    --   next< : {x y z : Ordinal} → x o< next z  → y o< next x → y o< next z
    lemma8 : {y : Ordinal} → & (* y , * y) o< next (odmax (* y , * y))
    lemma8 = ho<
    ---           (x,y) < next (omax x y) < next (osuc y) = next y 
    lemmaa : {x y : HOD} → & x o< & y → & (x , y) o< next (& y)
    lemmaa {x} {y} x<y = subst (λ k → & (x , y) o< k ) (sym nexto≡) (subst (λ k → & (x , y) o< next k ) (sym (omax< _ _ x<y)) ho< )
    lemma81 : {y : Ordinal} → & (* y , * y) o< next (& (* y))
    lemma81 {y} = nexto=n (subst (λ k →  & (* y , * y) o< k ) (cong (λ k → next k) (omxx _)) lemma8)
    lemma9 : {y : Ordinal} → & (* y , (* y , * y)) o< next (& (* y , * y))
    lemma9 = lemmaa (c<→o< (case1 refl))
    lemma71 : {y : Ordinal} → & (* y , (* y , * y)) o< next (& (* y))
    lemma71 = next< lemma81 lemma9
    lemma1 : {y : Ordinal} → & (u y) o< next (osuc (& (* y , (* y , * y))))
    lemma1 = ho<
    --- main recursion
    lemma : {y : Ordinal} → infinite-d y → y o< next o∅
    lemma {o∅} iφ = x<nx
    lemma (isuc {y} x) = next< (lemma x) (next< (subst (λ k → & (* y , (* y , * y)) o< next k) &iso lemma71 ) (nexto=n lemma1))

empty : (x : HOD  ) → ¬  (od∅ ∋ x)
empty x = ¬x<0 

_=h=_ : (x y : HOD) → Set n
x =h= y  = od x == od y

pair→ : ( x y t : HOD  ) →  (x , y)  ∋ t  → ( t =h= x ) ∨ ( t =h= y ) 
pair→ x y t (case1 t≡x ) = case1 (subst₂ (λ j k → j =h= k ) *iso *iso (o≡→== t≡x ))
pair→ x y t (case2 t≡y ) = case2 (subst₂ (λ j k → j =h= k ) *iso *iso (o≡→== t≡y ))

pair← : ( x y t : HOD  ) → ( t =h= x ) ∨ ( t =h= y ) →  (x , y)  ∋ t  
pair← x y t (case1 t=h=x) = case1 (cong (λ k → & k ) (==→o≡ t=h=x))
pair← x y t (case2 t=h=y) = case2 (cong (λ k → & k ) (==→o≡ t=h=y))

o<→c< :  {x y : Ordinal } → x o< y → (Ord x) ⊆ (Ord y) 
o<→c< lt = record { incl = λ z → ordtrans z lt }  

⊆→o< :  {x y : Ordinal } → (Ord x) ⊆ (Ord y) →  x o< osuc y
⊆→o< {x} {y}  lt with trio< x y 
⊆→o< {x} {y}  lt | tri< a ¬b ¬c = ordtrans a <-osuc
⊆→o< {x} {y}  lt | tri≈ ¬a b ¬c = subst ( λ k → k o< osuc y) (sym b) <-osuc
⊆→o< {x} {y}  lt | tri> ¬a ¬b c with (incl lt)  (o<-subst c (sym &iso) refl )
... | ttt = ⊥-elim ( o<¬≡ refl (o<-subst ttt &iso refl ))

ψiso :  {ψ : HOD  → Set n} {x y : HOD } → ψ x → x ≡ y   → ψ y
ψiso {ψ} t refl = t
selection : {ψ : HOD → Set n} {X y : HOD} → ((X ∋ y) ∧ ψ y) ⇔ (Select X ψ ∋ y)
selection {ψ} {X} {y} = ⟪
     ( λ cond → ⟪ proj1 cond , ψiso {ψ} (proj2 cond) (sym *iso)  ⟫ )
  ,  ( λ select → ⟪ proj1 select  , ψiso {ψ} (proj2 select) *iso  ⟫ )
  ⟫

selection-in-domain : {ψ : HOD → Set n} {X y : HOD} → Select X ψ ∋ y → X ∋ y 
selection-in-domain {ψ} {X} {y} lt = proj1 ((proj2 (selection {ψ} {X} )) lt)

sup-c< :  (ψ : HOD → HOD) → {X x : HOD} → X ∋ x  → & (ψ x) o< (sup-o X (λ y X∋y → & (ψ (* y))))
sup-c< ψ {X} {x} lt = subst (λ k → & (ψ k) o< _ ) *iso (sup-o< X lt )
replacement← : {ψ : HOD → HOD} (X x : HOD) →  X ∋ x → Replace X ψ ∋ ψ x
replacement← {ψ} X x lt = ⟪ sup-c< ψ {X} {x} lt , lemma ⟫ where 
    lemma : def (in-codomain X ψ) (& (ψ x))
    lemma not = ⊥-elim ( not ( & x ) ⟪ lt , cong (λ k → & (ψ k)) (sym *iso)⟫ )
replacement→ : {ψ : HOD → HOD} (X x : HOD) → (lt : Replace X ψ ∋ x) → ¬ ( (y : HOD) → ¬ (x =h= ψ y))
replacement→ {ψ} X x lt = contra-position lemma (lemma2 (proj2 lt)) where
    lemma2 :  ¬ ((y : Ordinal) → ¬ odef X y ∧ ((& x) ≡ & (ψ (* y))))
            → ¬ ((y : Ordinal) → ¬ odef X y ∧ (* (& x) =h= ψ (* y)))
    lemma2 not not2  = not ( λ y d →  not2 y ⟪ proj1 d , lemma3 (proj2 d)⟫) where
        lemma3 : {y : Ordinal } → (& x ≡ & (ψ (*  y))) → (* (& x) =h= ψ (* y))  
        lemma3 {y} eq = subst (λ k  → * (& x) =h= k ) *iso (o≡→== eq )
    lemma :  ( (y : HOD) → ¬ (x =h= ψ y)) → ( (y : Ordinal) → ¬ odef X y ∧ (* (& x) =h= ψ (* y)) )
    lemma not y not2 = not (* y) (subst (λ k → k =h= ψ (* y)) *iso  ( proj2 not2 ))

---
--- Power Set
---
---    First consider ordinals in HOD
---
--- A ∩ x =  record { def = λ y → odef A y ∧  odef x y }                   subset of A
--
--
∩-≡ :  { a b : HOD  } → ({x : HOD  } → (a ∋ x → b ∋ x)) → a =h= ( b ∩ a )
∩-≡ {a} {b} inc = record {
   eq→ = λ {x} x<a → ⟪ (subst (λ k → odef b k ) &iso (inc (d→∋ a x<a))) , x<a  ⟫ ;
   eq← = λ {x} x<a∩b → proj2 x<a∩b }
-- 
-- Transitive Set case
-- we have t ∋ x → Ord a ∋ x means t is a subset of Ord a, that is (Ord a) ∩ t =h= t
-- OPwr (Ord a) is a sup of (Ord a) ∩ t, so OPwr (Ord a) ∋ t
-- OPwr  A = Ord ( sup-o ( λ x → & ( A ∩ (* x )) ) )   
-- 
ord-power← : (a : Ordinal ) (t : HOD) → ({x : HOD} → (t ∋ x → (Ord a) ∋ x)) → OPwr (Ord a) ∋ t
ord-power← a t t→A  = subst (λ k → odef (OPwr (Ord a)) k ) (lemma1 lemma-eq) lemma where 
    lemma-eq :  ((Ord a) ∩ t) =h= t
    eq→ lemma-eq {z} w = proj2 w 
    eq← lemma-eq {z} w = ⟪ subst (λ k → odef (Ord a) k ) &iso ( t→A (d→∋ t w)) , w ⟫ 
    lemma1 :  {a : Ordinal } { t : HOD }
        → (eq : ((Ord a) ∩ t) =h= t)  → & ((Ord a) ∩ (* (& t))) ≡ & t
    lemma1  {a} {t} eq = subst (λ k → & ((Ord a) ∩ k) ≡ & t ) (sym *iso) (cong (λ k → & k ) (==→o≡ eq ))
    lemma2 : (& t) o< (osuc (& (Ord a)))
    lemma2 = ⊆→o≤  {t} {Ord a} (λ {x} x<t → subst (λ k → def (od (Ord a)) k) &iso (t→A (d→∋ t x<t))) 
    lemma :  & ((Ord a) ∩ (* (& t)) ) o< sup-o (Ord (osuc (& (Ord a)))) (λ x lt → & ((Ord a) ∩ (* x)))
    lemma = sup-o< _ lemma2

-- 
-- Every set in HOD is a subset of Ordinals, so make OPwr (Ord (& A)) first
-- then replace of all elements of the Power set by A ∩ y
-- 
-- Power A = Replace (OPwr (Ord (& A))) ( λ y → A ∩ y )

-- we have oly double negation form because of the replacement axiom
--
power→ :  ( A t : HOD) → Power A ∋ t → {x : HOD} → t ∋ x → ¬ ¬ (A ∋ x)
power→ A t P∋t {x} t∋x = FExists _ lemma5 lemma4 where
    a = & A
    lemma2 : ¬ ( (y : HOD) → ¬ (t =h=  (A ∩ y)))
    lemma2 = replacement→ {λ x → A ∩ x} (OPwr (Ord (& A))) t P∋t
    lemma3 : (y : HOD) → t =h= ( A ∩ y ) → ¬ ¬ (A ∋ x)
    lemma3 y eq not = not (proj1 (eq→ eq t∋x))
    lemma4 : ¬ ((y : Ordinal) → ¬ (t =h= (A ∩ * y)))
    lemma4 not = lemma2 ( λ y not1 → not (& y) (subst (λ k → t =h= ( A ∩ k )) (sym *iso) not1 ))
    lemma5 : {y : Ordinal} → t =h= (A ∩ * y) →  ¬ ¬  (odef A (& x))
    lemma5 {y} eq not = (lemma3 (* y) eq) not

power← :  (A t : HOD) → ({x : HOD} → (t ∋ x → A ∋ x)) → Power A ∋ t
power← A t t→A = ⟪ lemma1 , lemma2 ⟫ where 
    a = & A
    lemma0 : {x : HOD} → t ∋ x → Ord a ∋ x
    lemma0 {x} t∋x = c<→o< (t→A t∋x)
    lemma3 : OPwr (Ord a) ∋ t
    lemma3 = ord-power← a t lemma0
    lemma4 :  (A ∩ * (& t)) ≡ t
    lemma4 = let open ≡-Reasoning in begin
        A ∩ * (& t)
        ≡⟨ cong (λ k → A ∩ k) *iso ⟩
        A ∩ t
        ≡⟨ sym (==→o≡ ( ∩-≡ {t} {A} t→A )) ⟩
        t
        ∎
    sup1 : Ordinal
    sup1 =  sup-o (Ord (osuc (& (Ord (& A))))) (λ x A∋x → & ((Ord (& A)) ∩ (* x)))
    lemma9 : def (od (Ord (Ordinals.osuc O (& (Ord (& A)))))) (& (Ord (& A)))
    lemma9 = <-osuc 
    lemmab : & ((Ord (& A)) ∩ (* (& (Ord (& A) )))) o< sup1
    lemmab = sup-o< (Ord (osuc (& (Ord (& A))))) lemma9 
    lemmad : Ord (osuc (& A)) ∋ t
    lemmad = ⊆→o≤ (λ {x} lt → subst (λ k → def (od A) k ) &iso (t→A (d→∋ t lt))) 
    lemmac : ((Ord (& A)) ∩  (* (& (Ord (& A) )))) =h= Ord (& A)
    lemmac = record { eq→ = lemmaf ; eq← = lemmag } where
        lemmaf : {x : Ordinal} → def (od ((Ord (& A)) ∩  (* (& (Ord (& A)))))) x → def (od (Ord (& A))) x
        lemmaf {x} lt = proj1 lt
        lemmag :  {x : Ordinal} → def (od (Ord (& A))) x → def (od ((Ord (& A)) ∩ (* (& (Ord (& A)))))) x
        lemmag {x} lt = ⟪ lt , subst (λ k → def (od k) x) (sym *iso) lt ⟫ 
    lemmae : & ((Ord (& A)) ∩ (* (& (Ord (& A))))) ≡ & (Ord (& A))
    lemmae = cong (λ k → & k ) ( ==→o≡ lemmac)
    lemma7 : def (od (OPwr (Ord (& A)))) (& t)
    lemma7 with osuc-≡< lemmad
    lemma7 | case2 lt = ordtrans (c<→o< lt) (subst (λ k → k o< sup1) lemmae lemmab )
    lemma7 | case1 eq with osuc-≡< (⊆→o≤ {* (& t)} {* (& (Ord (& t)))} (λ {x} lt → lemmah lt )) where
        lemmah : {x : Ordinal } → def (od (* (& t))) x → def (od (* (& (Ord (& t))))) x
        lemmah {x} lt = subst (λ k → def (od k) x ) (sym *iso) (subst (λ k → k o< (& t))
            &iso
            (c<→o< (subst₂ (λ j k → def (od j)  k) *iso (sym &iso) lt )))
    lemma7 | case1 eq | case1 eq1 = subst (λ k → k o< sup1) (trans lemmae lemmai) lemmab where 
        lemmai : & (Ord (& A)) ≡ & t
        lemmai = let open ≡-Reasoning in begin
                & (Ord (& A)) 
            ≡⟨ sym (cong (λ k → & (Ord k)) eq) ⟩
                & (Ord (& t)) 
            ≡⟨ sym &iso ⟩
                & (* (& (Ord (& t))))
            ≡⟨ sym eq1 ⟩
                & (* (& t))
            ≡⟨ &iso ⟩
                & t 
            ∎
    lemma7 | case1 eq | case2 lt = ordtrans lemmaj (subst (λ k → k o< sup1) lemmae lemmab ) where
        lemmak : & (* (& (Ord (& t)))) ≡ & (Ord (& A))
        lemmak = let open ≡-Reasoning in begin
                & (* (& (Ord (& t))))
            ≡⟨ &iso ⟩
                & (Ord (& t))
            ≡⟨ cong (λ k → & (Ord k)) eq ⟩
                & (Ord (& A))
            ∎
        lemmaj : & t o< & (Ord (& A))
        lemmaj = subst₂ (λ j k → j o< k ) &iso lemmak lt 
    lemma1 : & t o< sup-o (OPwr (Ord (& A))) (λ x lt → & (A ∩ (* x)))
    lemma1 = subst (λ k → & k o< sup-o (OPwr (Ord (& A)))  (λ x lt → & (A ∩ (* x))))
        lemma4 (sup-o< (OPwr (Ord (& A))) lemma7 )
    lemma2 :  def (in-codomain (OPwr (Ord (& A))) (_∩_ A)) (& t)
    lemma2 not = ⊥-elim ( not (& t) ⟪ lemma3 , lemma6 ⟫ ) where
        lemma6 : & t ≡ & (A ∩ * (& t)) 
        lemma6 = cong ( λ k → & k ) (==→o≡ (subst (λ k → t =h= (A ∩ k)) (sym *iso) ( ∩-≡ {t} {A} t→A  )))


extensionality0 : {A B : HOD } → ((z : HOD) → (A ∋ z) ⇔ (B ∋ z)) → A =h= B
eq→ (extensionality0 {A} {B} eq ) {x} d = odef-iso  {A} {B} (sym &iso) (proj1 (eq (* x))) d  
eq← (extensionality0 {A} {B} eq ) {x} d = odef-iso  {B} {A} (sym &iso) (proj2 (eq (* x))) d  

extensionality : {A B w : HOD  } → ((z : HOD ) → (A ∋ z) ⇔ (B ∋ z)) → (w ∋ A) ⇔ (w ∋ B)
proj1 (extensionality {A} {B} {w} eq ) d = subst (λ k → w ∋ k) ( ==→o≡ (extensionality0 {A} {B} eq) ) d
proj2 (extensionality {A} {B} {w} eq ) d = subst (λ k → w ∋ k) (sym ( ==→o≡ (extensionality0 {A} {B} eq) )) d 

infinity∅ : infinite  ∋ od∅ 
infinity∅ = subst (λ k → odef infinite k ) lemma iφ where 
    lemma : o∅ ≡ & od∅
    lemma =  let open ≡-Reasoning in begin
        o∅
        ≡⟨ sym &iso ⟩
        & ( * o∅ )
        ≡⟨ cong ( λ k → & k ) o∅≡od∅ ⟩
        & od∅
        ∎
infinity : (x : HOD) → infinite ∋ x → infinite ∋ Union (x , (x , x ))
infinity x lt = subst (λ k → odef infinite k ) lemma (isuc {& x} lt) where
    lemma :  & (Union (* (& x) , (* (& x) , * (& x))))
        ≡ & (Union (x , (x , x)))
    lemma = cong (λ k → & (Union ( k , ( k , k ) ))) *iso 

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
    } 

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
 } 
  

