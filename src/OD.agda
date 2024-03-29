{-# OPTIONS --allow-unsolved-metas #-}
open import Level
open import Ordinals
module OD {n : Level } (O : Ordinals {n} ) where

open import Data.Nat renaming ( zero to Zero ; suc to Suc ;  ℕ to Nat ; _⊔_ to _n⊔_ )
open import  Relation.Binary.PropositionalEquality hiding ( [_] )
open import Data.Nat.Properties
open import Data.Empty
open import Data.Unit
open import Relation.Nullary
open import Relation.Binary  hiding (_⇔_)
open import Relation.Binary.Core hiding (_⇔_)

open import logic
import OrdUtil
open import nat

open Ordinals.Ordinals  O
open Ordinals.IsOrdinals isOrdinal
-- open Ordinals.IsNext isNext
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
--  we need explict assumption on sup for unrestricted Replacement.
--
--  ==→o≡ is necessary to prove axiom of extensionality.

-- Ordinals in OD , the maximum
Ords : OD
Ords = record { def = λ x → Lift n ⊤ }

record HOD : Set (suc n) where
  field
    od : OD
    odmax : Ordinal
    <odmax : {y : Ordinal} → def od y → y o< odmax

open HOD

open import Relation.Binary.HeterogeneousEquality as HE using (_≅_ )

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
  ∋-irr : {X : HOD} {x : Ordinal } → (a b : def (od X) x) → a ≅ b

postulate  odAxiom : ODAxiom
open ODAxiom odAxiom

-- possible order restriction (required in the axiom of Omega )

-- postulate  odAxiom-ho< : ODAxiom-ho<
-- open ODAxiom-ho< odAxiom-ho<

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
¬OD-order & * c<→o< = o≤> <-osuc (c<→o< {Ords} (lift tt) )

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

*≡*→≡ : { x y : Ordinal  } → * x ≡ * y →  x ≡ y
*≡*→≡ eq = subst₂ (λ j k → j ≡ k ) &iso &iso ( cong (&) eq )

&≡&→≡ : { x y : HOD  } → & x ≡  & y →  x ≡ y
&≡&→≡ eq = subst₂ (λ j k → j ≡ k ) *iso *iso ( cong (*) eq )

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

≡od∅→=od∅  : {x : HOD} → x ≡ od∅ → od x == od od∅
≡od∅→=od∅ {x} eq = ≡o∅→=od∅ (subst (λ k → & x  ≡ k ) ord-od∅ ( cong & eq ) )

∅0 : record { def = λ x →  Lift n ⊥ } == od od∅
eq→ ∅0 {w} (lift ())
eq← ∅0 {w} lt = lift (¬x<0 lt)

∅< : { x y : HOD  } → odef x (& y ) → ¬ (  od x  == od od∅  )
∅<  {x} {y} d eq with eq→ (==-trans eq (==-sym ∅0) ) d
∅<  {x} {y} d eq | lift ()

¬x∋y→x≡od∅  : { x : HOD  } → ({y : Ordinal } → ¬ odef x y ) → x ≡ od∅ 
¬x∋y→x≡od∅ {x} nxy = ==→o≡ record { eq→ = λ {y} lt → ⊥-elim (nxy lt) ; eq← = λ {y} lt → ⊥-elim (¬x<0 lt)  }

0<P→ne  : { x : HOD  } → o∅ o< & x → ¬ (  od x  == od od∅  )
0<P→ne {x} 0<x eq = ⊥-elim ( o<¬≡ (sym (=od∅→≡o∅ eq)) 0<x )

∈∅< : { x : HOD  } {y : Ordinal } → odef x y → o∅  o< (& x)
∈∅<  {x} {y} d with trio< o∅ (& x)
... | tri< a ¬b ¬c = a
... | tri≈ ¬a b ¬c = ⊥-elim ( ∅< {x} {* y} (subst (λ k → odef x k ) (sym &iso) d )  ( ≡o∅→=od∅ (sym b) ) )
... | tri> ¬a ¬b c = ⊥-elim (  ¬x<0 c  )

∅6 : { x : HOD  }  → ¬ ( x ∋ x )    --  no Russel paradox
∅6  {x} x∋x = o<¬≡ refl ( c<→o<  {x} {x} x∋x )

odef-iso : {A B : HOD } {x y : Ordinal } → x ≡ y  → (odef A y → odef B y)  → odef A x → odef B x
odef-iso refl t = t

is-o∅ : ( x : Ordinal  ) → Dec ( x ≡ o∅  )
is-o∅ x with trio< x o∅
is-o∅ x | tri< a ¬b ¬c = no ¬b
is-o∅ x | tri≈ ¬a b ¬c = yes b
is-o∅ x | tri> ¬a ¬b c = no ¬b

odef< : {b : Ordinal } { A : HOD } → odef A b → b o< & A
odef< {b} {A} ab = subst (λ k → k o< & A) &iso ( c<→o< (subst (λ k → odef A k ) (sym &iso ) ab))

odef∧< : {A : HOD } {y : Ordinal} {n : Level } → {P : Set n} → odef A y ∧ P → y o< & A
odef∧< {A } {y} p = subst (λ k → k o< & A) &iso ( c<→o< (subst (λ k → odef A k ) (sym &iso ) (proj1 p )))

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

-- another possible restriction. We require no minimality on odmax, so it may arbitrary larger.
odmax<&  : { x y : HOD } → x ∋ y →  Set n
odmax<& {x} {y} x∋y = odmax x o< & x

in-codomain : (X : HOD  ) → ( ψ : HOD  → HOD  ) → OD
in-codomain  X ψ = record { def = λ x → ¬ ( (y : Ordinal ) → ¬ ( odef X y ∧  ( x ≡ & (ψ (* y )))))  }

_∩_ : ( A B : HOD ) → HOD
A ∩ B = record { od = record { def = λ x → odef A x ∧ odef B x }
        ; odmax = omin (odmax A) (odmax B) ; <odmax = λ y → min1 (<odmax A (proj1 y)) (<odmax B (proj2 y))}

_⊆_ : ( A B : HOD)   → Set n
_⊆_ A B = { x : Ordinal } → odef A x → odef B x

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

ε-induction0 : { ψ : HOD  → Set n}
   → ( {x : HOD } → ({ y : HOD } →  x ∋ y → ψ y ) → ψ x )
   → (x : HOD ) → ψ x
ε-induction0 {ψ} ind x = subst (λ k → ψ k ) *iso (ε-induction-ord (osuc (& x)) <-osuc )  where
     induction : (ox : Ordinal) → ((oy : Ordinal) → oy o< ox → ψ (* oy)) → ψ (* ox)
     induction ox prev = ind  ( λ {y} lt → subst (λ k → ψ k ) *iso (prev (& y) (o<-subst (c<→o< lt) refl &iso )))
     ε-induction-ord : (ox : Ordinal) { oy : Ordinal } → oy o< ox → ψ (* oy)
     ε-induction-ord ox {oy} lt = inOrdinal.TransFinite0 O {λ oy → ψ (* oy)} induction oy

-- Open supreme upper bound leads a contradition, so we use domain restriction on sup
¬open-sup : ( sup-o : (Ordinal →  Ordinal ) → Ordinal) → ((ψ : Ordinal →  Ordinal ) → (x : Ordinal) → ψ x  o<  sup-o ψ ) → ⊥
¬open-sup sup-o sup-o< = o<> <-osuc (sup-o< next-ord (sup-o next-ord)) where
   next-ord : Ordinal → Ordinal
   next-ord x = osuc x

Select : (X : HOD  ) → ((x : HOD  ) → Set n ) → HOD
Select X ψ = record { od = record { def = λ x →  ( odef X x ∧ ψ ( * x )) } ; odmax = odmax X ; <odmax = λ y → <odmax X (proj1 y) }

_=h=_ : (x y : HOD) → Set n
x =h= y  = od x == od y

record Own (A : HOD) (x : Ordinal) : Set n where
    field
       owner : Ordinal
       ao : odef A owner
       ox : odef (* owner) x

Union : HOD  → HOD
Union U = record { od = record { def = λ x → Own U x } ; odmax = osuc (& U) ; <odmax = umax } where
        umax :  {y : Ordinal} → Own U y → y o< osuc (& U)
        umax {y} uy = o<→≤ ( ordtrans (odef< (Own.ox uy)) (subst (λ k → k o< & U) (sym &iso) umax1) ) where
            umax1 : Own.owner uy o< & U
            umax1 = odef< (Own.ao uy)
         
union→ :  (X z u : HOD) → (X ∋ u) ∧ (u ∋ z) → Union X ∋ z
union→ X z u xx =  record { owner = & u ; ao = proj1 xx ; ox = subst (λ k → odef k (& z)) (sym *iso) (proj2 xx)   }
union← :  (X z : HOD) (X∋z : Union X ∋ z) →  ¬  ( (u : HOD ) → ¬ ((X ∋  u) ∧ (u ∋ z )))
union← X z UX∋z not = ⊥-elim ( not (* (Own.owner UX∋z)) ⟪ subst (λ k → odef X k) (sym &iso) ( Own.ao UX∋z) , Own.ox UX∋z ⟫  )

--
--
--

record RCod (COD : HOD) (ψ : HOD → HOD)  : Set (suc n) where
 field
     ≤COD : ∀ {x : HOD } → ψ x ⊆ COD 

record Replaced (A : HOD) (ψ : Ordinal → Ordinal ) (x : Ordinal ) : Set n where
   field
      z : Ordinal
      az : odef A z
      x=ψz  : x ≡ ψ z 

Replace : (D : HOD) → (ψ : HOD  → HOD) → {C : HOD} → RCod C ψ  → HOD
Replace X ψ {C} rc = record { od = record { def = λ x → Replaced X (λ z → & (ψ (* z))) x  } ; odmax = osuc (& C)
   ; <odmax = rmax< } where
        rmax< :  {y : Ordinal} → Replaced X (λ z → & (ψ (* z))) y  → y o< osuc (& C)
        rmax< {y} lt = subst (λ k → k o< osuc (& C)) r01 ( ⊆→o≤ (RCod.≤COD rc) ) where 
            r01 : & (ψ ( * (Replaced.z lt ) )) ≡ y
            r01 = sym (Replaced.x=ψz lt )

replacement← : {ψ : HOD → HOD} (X x : HOD) →  X ∋ x → {C : HOD} → (rc : RCod C ψ) → Replace X ψ rc ∋ ψ x
replacement← {ψ} X x lt {C} rc = record { z = & x ; az = lt  ; x=ψz = cong (λ k → & (ψ k)) (sym *iso) }
replacement→ : {ψ : HOD → HOD} (X x : HOD) → {C : HOD} → (rc : RCod C ψ ) → (lt : Replace X ψ rc ∋ x) 
   →  ¬ ( (y : HOD) → ¬ (x =h= ψ y))
replacement→ {ψ} X x {C} rc lt eq = eq (* (Replaced.z lt)) (ord→== (Replaced.x=ψz lt)) 

--
-- If we have LEM, Replace' is equivalent to Replace
--

record RXCod (X COD : HOD) (ψ : (x : HOD) → X ∋ x → HOD)  : Set (suc n) where
 field
     ≤COD : ∀ {x : HOD } → (lt : X ∋ x) → ψ x lt ⊆ COD 

record Replaced1 (A : HOD) (ψ : (x : Ordinal ) → odef A x → Ordinal ) (x : Ordinal ) : Set n where
   field
      z : Ordinal
      az : odef A z
      x=ψz  : x ≡ ψ z az

Replace' : (X : HOD) → (ψ : (x : HOD) → X ∋ x → HOD) → {C : HOD} → RXCod X C ψ  → HOD
Replace' X ψ {C} rc = record { od = record { def = λ x → Replaced1 X (λ z xz → & (ψ (* z) (subst (λ k → odef X k) (sym &iso) xz) )) x  } ; odmax = osuc (& C) ; <odmax = rmax< } where
        rmax< :  {y : Ordinal} → Replaced1 X (λ z xz → & (ψ (* z) (subst (λ k → odef X k) (sym &iso) xz) )) y  → y o< osuc (& C)
        rmax< {y} lt = subst (λ k → k o< osuc (& C)) r01 ( ⊆→o≤ (RXCod.≤COD rc (subst (λ k → odef X k) (sym &iso) (Replaced1.az lt) )))  where 
            r01 : & (ψ ( * (Replaced1.z lt ) ) (subst (λ k → odef X k) (sym &iso) (Replaced1.az lt) )) ≡ y
            r01 = sym (Replaced1.x=ψz lt )

cod-conv : (X : HOD) → (ψ : (x : HOD) → X ∋ x → HOD) → {C : HOD} → (rc : RXCod X C ψ   )
      → RXCod (* (& X)) C (λ y xy → ψ y (subst (λ k → k ∋ y) *iso xy))
cod-conv X ψ {C} rc = record { ≤COD = λ {x} lt → RXCod.≤COD rc (subst (λ k → odef k (& x)) *iso lt) }

Replace'-iso : {X Y : HOD} → {fx : (x : HOD) → X ∋ x → HOD} {fy : (x : HOD) → Y ∋ x → HOD}
    → {CX : HOD} → (rcx : RXCod X CX fx  ) → {CY : HOD} → (rcy : RXCod Y CY fy   )
      → X ≡ Y →  ( (x :  HOD) → (xx : X ∋ x ) → (yy : Y ∋ x ) → fx _ xx ≡ fy _ yy )
      → Replace' X fx rcx ≡ Replace' Y fy rcy
Replace'-iso {X} {X} {fx} {fy} _ _ refl eq  = ==→o≡ record { eq→ = ri0 ; eq← = ri1 } where
     ri0 : {x : Ordinal} → Replaced1 X (λ z xz → & (fx (* z) (subst (odef X) (sym &iso) xz))) x 
                         → Replaced1 X (λ z xz → & (fy (* z) (subst (odef X) (sym &iso) xz))) x
     ri0 {x} record { z = z ; az = az ; x=ψz = x=ψz } = record { z = z ; az = az ; x=ψz = trans x=ψz (cong (&) ( eq _ xz xz ))  } where
         xz : X ∋ * z
         xz = subst (λ k → odef X k ) (sym &iso) az
     ri1 : {x : Ordinal} → Replaced1 X (λ z xz → & (fy (* z) (subst (odef X) (sym &iso) xz))) x 
                         → Replaced1 X (λ z xz → & (fx (* z) (subst (odef X) (sym &iso) xz))) x
     ri1 {x} record { z = z ; az = az ; x=ψz = x=ψz } = record { z = z ; az = az ; x=ψz = trans x=ψz (cong (&) (sym ( eq _ xz xz )))  } where
         xz : X ∋ * z
         xz = subst (λ k → odef X k ) (sym &iso) az

Replace'-iso1 : (X : HOD) → (ψ : (x : HOD) → X ∋ x → HOD) → {C : HOD} → (rc : RXCod X C ψ   )
      → Replace' (* (& X)) (λ y xy → ψ y (subst (λ k → k ∋ y ) *iso xy) ) (cod-conv X ψ rc)
         ≡ Replace' X ( λ y xy → ψ y xy ) rc 
Replace'-iso1 X ψ rc = Replace'-iso {* (& X)} {X} {λ y xy → ψ y (subst (λ k → k ∋ y ) *iso xy) } { λ y xy → ψ y xy } 
    (cod-conv X ψ rc) rc 
    *iso (λ x xx yx → fi00 x xx yx ) where
      fi00 : (x : HOD ) → (xx : (* (& X)) ∋ x ) → (yx : X ∋ x) →  ψ x (subst (λ k → k ∋ x) *iso xx) ≡ ψ x yx
      fi00 x xx yx = cong (λ k → ψ x k ) ( HE.≅-to-≡ ( ∋-irr {X} {& x} (subst (λ k → k ∋ x) *iso xx) yx ) )

-- replacement←1 : {ψ : HOD → HOD} (X x : HOD) →  X ∋ x → Replace1 X ψ ∋ ψ x
-- replacement←1 {ψ} X x lt = record { z = & x ; az = lt  ; x=ψz = cong (λ k → & (ψ k)) (sym *iso) }
-- replacement→1 : {ψ : HOD → HOD} (X x : HOD) → (lt : Replace1 X ψ ∋ x) → ¬ ( (y : HOD) → ¬ (x =h= ψ y))
-- replacement→1 {ψ} X x lt eq = eq (* (Replaced.z lt)) (ord→== (Replaced.x=ψz lt)) 

_∈_ : ( A B : HOD  ) → Set n
A ∈ B = B ∋ A

Power : HOD  → HOD
Power A =  record { od = record { def = λ x → ( z : Ordinal) → odef (* x) z → odef A z  } ; odmax = osuc (& A) 
       ; <odmax = p00  } where
   p00 :  {y : Ordinal} → ((z : Ordinal) → odef (* y) z → odef A z) → y o< osuc (& A)
   p00 {y} y⊆A = p01 where
         p01 : y o≤ & A
         p01 = subst (λ k → k o≤ & A) &iso ( ⊆→o≤ (λ {x} yx → y⊆A x yx ))

power→ :  ( A t : HOD) → Power A ∋ t → {x : HOD} → t ∋ x → A ∋ x
power→ A t P∋t {x} t∋x = P∋t (& x) (subst (λ k → odef k (& x) ) (sym *iso) t∋x )

power← :  (A t : HOD) → ({x : HOD} → (t ∋ x → A ∋ x)) → Power A ∋ t
power← A t t⊆A z xz = subst (λ k → odef A k ) &iso ( t⊆A  (subst₂ (λ j k → odef j k) *iso (sym &iso) xz ))

Power∋∅ : {S : HOD} → odef (Power S) o∅
Power∋∅ z xz = ⊥-elim (¬x<0 (subst (λ k → odef k z) o∅≡od∅ xz)  )

Intersection : (X : HOD ) → HOD   -- ∩ X
Intersection X = record { od = record { def = λ x → (x o≤ & X ) ∧ ( {y : Ordinal} → odef X y → odef (* y) x )} ; odmax = osuc (& X) ; <odmax = λ lt → proj1 lt } 

empty : (x : HOD  ) → ¬  (od∅ ∋ x)
empty x = ¬x<0


-- ｛_｝ : ZFSet → ZFSet
-- ｛ x ｝ = ( x ,  x )     -- better to use (x , x) directly

data Omega-d  : ( x : Ordinal  ) → Set n where
    iφ :  Omega-d o∅
    isuc : {x : Ordinal  } →   Omega-d  x  →
            Omega-d  (& ( Union (* x , (* x , * x ) ) ))

-- ω can be diverged in our case, since we have no restriction on the corresponding ordinal of a pair.
-- We simply assumes Omega-d y has a maximum.
--
-- This means that many of OD may not be HODs because of the & mapping divergence.
-- We should have some axioms to prevent this .
--

Omega-od : OD
Omega-od = record { def = λ x → Omega-d x } 

o∅<x : {x : Ordinal} → o∅ o≤ x
o∅<x {x} with trio< o∅ x
... | tri< a ¬b ¬c = o<→≤ a
... | tri≈ ¬a b ¬c = o≤-refl0 b
... | tri> ¬a ¬b c = ⊥-elim (¬x<0 c)

¬0=ux : {x : HOD} → ¬ o∅ ≡ & (Union ( x , ( x ,  x)))
¬0=ux {x} eq = ⊥-elim ( o<¬≡ eq (ordtrans≤-< o∅<x (subst (λ k → k o< & (Union (x , (x , x)))) &iso (c<→o< lemma ) ))) where
    lemma : Own (x , (x , x)) (& ( * (& x )))
    lemma = record { owner = _ ; ao = case2 refl ; ox = subst₂ (λ j k → odef j k ) (sym *iso) (sym &iso) (case1 refl) }

ux-2cases : {x y : HOD } → Union ( x , ( x ,  x)) ∋ y → ( x ≡ y ) ∨ ( x ∋ y )
ux-2cases {x} {y} record { owner = owner ; ao = (case1 eq) ; ox = ox } = case2 (subst (λ k → odef k (& y)) (trans (cong (*) eq) *iso) ox)
ux-2cases {x} {y} record { owner = owner ; ao = (case2 eq) ; ox = ox } with subst (λ k → odef k (& y))  (trans (cong (*) eq) *iso) ox
... | case1 eq = case1 (sym (&≡&→≡ eq))
... | case2 eq = case1 (sym (&≡&→≡ eq))

ux-transitve  : {x y : HOD} → x ∋ y →  Union ( x , ( x ,  x)) ∋ y 
ux-transitve {x} {y} ox  = record { owner = _ ; ao = case1 refl ; ox = subst (λ k → odef k (& y)) (sym *iso) ox }

--
-- Possible Ordinal Limit
--

--        our Ordinals is greater than Union ( x , ( x ,  x)) transitive closure
--
record ODAxiom-ho< : Set (suc n) where
 field
    omega : Ordinal  
    ho< : {x : Ordinal } → Omega-d x →  x o< omega

postulate
    odaxion-ho< : ODAxiom-ho< 

open ODAxiom-ho< odaxion-ho<

Omega : HOD
Omega = record { od = record { def = λ x → Omega-d x } ; odmax = omega ; <odmax = ho<}  

infinity∅ : Omega  ∋ od∅
infinity∅ = subst (λ k → odef Omega k ) lemma iφ where
    lemma : o∅ ≡ & od∅
    lemma =  let open ≡-Reasoning in begin
        o∅
        ≡⟨ sym &iso ⟩
        & ( * o∅ )
        ≡⟨ cong ( λ k → & k ) o∅≡od∅ ⟩
        & od∅
        ∎

infinity : (x : HOD) → Omega ∋ x → Omega ∋ Union (x , (x , x ))
infinity x lt = subst (λ k → odef Omega k ) lemma (isuc {& x} lt) where
    lemma :  & (Union (* (& x) , (* (& x) , * (& x))))
        ≡ & (Union (x , (x , x)))
    lemma = cong (λ k → & (Union ( k , ( k , k ) ))) *iso

pair→ : ( x y t : HOD  ) →  (x , y)  ∋ t  → ( t =h= x ) ∨ ( t =h= y )
pair→ x y t (case1 t≡x ) = case1 (subst₂ (λ j k → j =h= k ) *iso *iso (o≡→== t≡x ))
pair→ x y t (case2 t≡y ) = case2 (subst₂ (λ j k → j =h= k ) *iso *iso (o≡→== t≡y ))

pair← : ( x y t : HOD  ) → ( t =h= x ) ∨ ( t =h= y ) →  (x , y)  ∋ t
pair← x y t (case1 t=h=x) = case1 (cong (λ k → & k ) (==→o≡ t=h=x))
pair← x y t (case2 t=h=y) = case2 (cong (λ k → & k ) (==→o≡ t=h=y))

o<→c< :  {x y : Ordinal } → x o< y → (Ord x) ⊆ (Ord y)
o<→c< lt {z} ox = ordtrans ox lt

⊆→o< :  {x y : Ordinal } → (Ord x) ⊆ (Ord y) →  x o< osuc y
⊆→o< {x} {y}  lt with trio< x y
⊆→o< {x} {y}  lt | tri< a ¬b ¬c = ordtrans a <-osuc
⊆→o< {x} {y}  lt | tri≈ ¬a b ¬c = subst ( λ k → k o< osuc y) (sym b) <-osuc
⊆→o< {x} {y}  lt | tri> ¬a ¬b c with lt  (o<-subst c (sym &iso) refl )
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

extensionality0 : {A B : HOD } → ((z : HOD) → (A ∋ z) ⇔ (B ∋ z)) → A =h= B
eq→ (extensionality0 {A} {B} eq ) {x} d = odef-iso  {A} {B} (sym &iso) (proj1 (eq (* x))) d
eq← (extensionality0 {A} {B} eq ) {x} d = odef-iso  {B} {A} (sym &iso) (proj2 (eq (* x))) d

extensionality : {A B w : HOD  } → ((z : HOD ) → (A ∋ z) ⇔ (B ∋ z)) → (w ∋ A) ⇔ (w ∋ B)
proj1 (extensionality {A} {B} {w} eq ) d = subst (λ k → w ∋ k) ( ==→o≡ (extensionality0 {A} {B} eq) ) d
proj2 (extensionality {A} {B} {w} eq ) d = subst (λ k → w ∋ k) (sym ( ==→o≡ (extensionality0 {A} {B} eq) )) d

open import zf

record ODAxiom-sup : Set (suc n) where
 field
  sup-o  :  (A : HOD) → (     ( x : Ordinal ) → def (od A) x →  Ordinal ) →  Ordinal -- required in Replace
  sup-o≤ :  (A : HOD) → { ψ : ( x : Ordinal ) → def (od A) x →  Ordinal } 
     → ∀ {x : Ordinal } → (lt : def (od A) x ) → ψ x lt o≤  sup-o A ψ
 sup-c≤ :  (ψ : HOD → HOD) → {X x : HOD} → def (od X) (& x)  → & (ψ x) o≤ (sup-o X (λ y X∋y → & (ψ (* y))))
 sup-c≤ ψ {X} {x} lt = subst (λ k → & (ψ k) o< _ ) *iso (sup-o≤ X lt )

-- sup-o may contradict
--    If we have open monotonic function in Ordinal, there is no sup-o. 
--    for example, if we may have countable sequence of Ordinal, which contains some ordinal larger than any given Ordinal.
--    This happens when we have a coutable model. In this case, we have to have codomain restriction in  Replacement axiom.
--    that is, Replacement axiom does not create new ZF set.

open ODAxiom-sup

ZFReplace : ODAxiom-sup → HOD  → (HOD  → HOD) → HOD
ZFReplace os X ψ = record { od = record { def = λ x → Replaced X (λ z → & (ψ (* z))) x  } ; odmax = rmax ; <odmax = rmax< } where
        rmax : Ordinal
        rmax = osuc ( sup-o os X (λ y X∋y → & (ψ (* y) )) )
        rmax< :  {y : Ordinal} → Replaced X (λ z → & (ψ (* z))) y  → y o< rmax
        rmax< {y} lt = subst (λ k → k o< rmax) r01 ( sup-o≤ os X (Replaced.az lt) ) where
            r01 : & (ψ ( * (Replaced.z lt ) )) ≡ y
            r01 = sym (Replaced.x=ψz lt )

zf-replacement← : (os : ODAxiom-sup) → {ψ : HOD → HOD} (X x : HOD) →  X ∋ x → ZFReplace os X ψ ∋ ψ x
zf-replacement← os {ψ} X x lt = record { z = & x ; az = lt  ; x=ψz = cong (λ k → & (ψ k)) (sym *iso) }
zf-replacement→ : (os : ODAxiom-sup ) → {ψ : HOD → HOD} (X x : HOD) → (lt : ZFReplace os X ψ ∋ x) → ¬ ( (y : HOD) → ¬ (x =h= ψ y))
zf-replacement→ os {ψ} X x lt eq = eq (* (Replaced.z lt)) (ord→== (Replaced.x=ψz lt)) 

isZF : (os : ODAxiom-sup) → IsZF HOD _∋_  _=h=_ od∅ _,_ Union Power Select (ZFReplace os) Omega
isZF os = record {
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
    ;   replacement← = zf-replacement← os
    ;   replacement→ = λ {ψ} → zf-replacement→ os {ψ}
    }

HOD→ZF : ODAxiom-sup → ZF
HOD→ZF os  = record {
    ZFSet = HOD
    ; _∋_ = _∋_
    ; _≈_ = _=h=_
    ; ∅  = od∅
    ; _,_ = _,_
    ; Union = Union
    ; Power = Power
    ; Select = Select
    ; Replace = ZFReplace os
    ; infinite = Omega
    ; isZF = isZF os
 }


