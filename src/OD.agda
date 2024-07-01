{-# OPTIONS --cubical-compatible --safe #-}
open import Level
open import Ordinals
import HODBase
module OD {n : Level } (O : Ordinals {n} ) (HODAxiom : HODBase.ODAxiom O) where

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

open HODBase.HOD 
open HODBase.OD 

open _∧_
open _∨_
open Bool

open  HODBase._==_

open HODBase.ODAxiom HODAxiom  

HOD =  HODBase.HOD O 
OD  =  HODBase.OD O 
Ords  =  HODBase.Ords O 
_==_  =  HODBase._==_ O 
==-refl = HODBase.==-refl  O
==-trans = HODBase.==-trans O
==-sym = HODBase.==-sym O
⇔→== = HODBase.⇔→== O
==-Setoid = HODBase.==-Setoid O
--  use like this    open import Relation.Binary.Reasoning.Setoid ==-Setoid

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

                                                            
record AxiomOfChoice : Set (suc n) where
 field                      
  -- mimimul and x∋minimal is an Axiom of choice                
  minimal : (x : HOD  ) → ¬ (od x == od od∅ )→ HOD                                
  -- this should be ¬ (x =h= od∅ )→ ∃ ox → x ∋ Ord ox  ( minimum of x )
  x∋minimal : (x : HOD  ) → ( ne : ¬ (od x == od od∅ ) ) → odef x ( & ( minimal x ne ) )
  -- minimality (proved by ε-induction with LEM)
  minimal-1 : (x : HOD  ) → ( ne : ¬ (od x == od od∅ ) ) → (y : HOD ) → ¬ ( odef (minimal x ne) (& y)) ∧ (odef x (&  y) )

-- _c<_ : ( x a : HOD  ) → Set n
-- x c< a = a ∋ x

d→∋ : ( a : HOD  ) { x : Ordinal} → odef a x → a ∋ (* x)
d→∋ a lt = subst (λ k → odef a k ) (sym &iso) lt

-- odef-subst :  {Z : HOD } {X : Ordinal  }{z : HOD } {x : Ordinal  }→ odef Z X → Z ≡ z  →  X ≡ x  →  odef z x
-- odef-subst df refl refl = df

otrans : {a x y : Ordinal  } → odef (Ord a) x → odef (Ord x) y → odef (Ord a) y
otrans x<a y<x = ordtrans y<x x<a

-- If we have reverse of c<→o<, everything becomes Ordinal
∈→c<→HOD=Ord : ( o<→c< : {x y : Ordinal  } → x o< y → odef (* y) x ) → {x : HOD } →  od x == od (Ord (& x))
∈→c<→HOD=Ord o<→c< {x} = record { eq→ = lemma1 ; eq← = lemma2 }  where
   lemma1 : {y : Ordinal} → odef x y → odef (Ord (& x)) y
   lemma1 {y} lt = subst ( λ k → k o< & x ) &iso (c<→o< {* y} {x} (d→∋ x lt))
   lemma2 : {y : Ordinal} → odef (Ord (& x)) y → odef x y
   lemma2 {y} lt = eq→  *iso (o<→c< {y} {& x} lt )

-- avoiding lv != Zero error
orefl : { x : HOD  } → { y : Ordinal  } → & x ≡ y → & x ≡ y
orefl refl = refl

==-iso : { x y : HOD  } → od (* (& x)) == od (* (& y))  →  od x == od y
==-iso  {x} {y} eq = record {
      eq→ = λ {z} d →  eq→  *iso ( eq→ eq (eq←  *iso d) )  ;
      eq← = λ {z} d →  eq→  *iso ( eq← eq (eq←  *iso d) )  }

-- =-iso :  {x y : HOD  } → (od x == od y) ≡ (od (* (& x)) == od y)
-- =-iso  {_} {y} = cong ( λ k → od k == od y ) ? -- (==-sym *iso)

ord→== : { x y : HOD  } → & x ≡  & y →  od x == od y
ord→==  {x} {y} eq = ==-iso (lemma (& x) (& y) (orefl eq)) where
   lemma : ( ox oy : Ordinal  ) → ox ≡ oy →  od (* ox) == od (* oy)
   lemma ox ox  refl = ==-refl

o≡→== : { x y : Ordinal  } → x ≡  y →  od (* x) == od (* y)
o≡→==  {x} {.x} refl = ==-refl

*≡*→≡ : { x y : Ordinal  } → * x ≡ * y →  x ≡ y
*≡*→≡ eq = subst₂ (λ j k → j ≡ k ) &iso &iso ( cong (&) eq )

&≡&*& : {x : HOD} → & x ≡ & (* (& x))
&≡&*& = (==→o≡ (==-sym *iso) )

--- &≡&→≡ : { x y : HOD  } → & x ≡  & y →  x ≡ y
--  &≡&→≡ eq = ? -- subst₂ (λ j k → j ≡ k ) *iso *iso ( cong (*) eq )

o∅==od∅ : od ( * (o∅ )) == od od∅
o∅==od∅  = lemma where
     lemma0 :  {x : Ordinal} → odef (* o∅) x → odef od∅ x
     lemma0 {x} lt with c<→o< {* x} {* o∅} (subst (λ k → odef (* o∅) k ) (sym &iso) lt)
     ... | t = subst₂ (λ j k → j o< k ) &iso &iso t
     lemma1 :  {x : Ordinal} → odef od∅ x → odef (* o∅) x
     lemma1 {x} lt = ⊥-elim (¬x<0 lt)
     lemma : od (* o∅) == od od∅
     lemma = record { eq→ = lemma0 ; eq← = lemma1 }

ord-od∅ : & (od∅ ) ≡ o∅
ord-od∅  = trans (==→o≡ (==-sym o∅==od∅)) &iso  

≡o∅→=od∅  : {x : HOD} → & x ≡ o∅ → od x == od od∅
≡o∅→=od∅ {x} eq = record { eq→ = λ {y} lt → ⊥-elim ( ¬x<0 {y} (subst₂ (λ j k → j o< k ) &iso eq ( c<→o< {* y} {x} (d→∋ x lt))))
    ; eq← = λ {y} lt → ⊥-elim ( ¬x<0 lt )}

=od∅→≡o∅  : {x : HOD} → od x == od od∅ → & x ≡ o∅
=od∅→≡o∅ {x} eq = trans (==→o≡ {x} {od∅} eq)  ord-od∅ 

≡od∅→=od∅  : {x : HOD} → x ≡ od∅ → od x == od od∅
≡od∅→=od∅ {x} eq = ≡o∅→=od∅ (subst (λ k → & x  ≡ k ) ord-od∅ ( cong & eq ) )

∅0 : record { def = λ x →  Lift n ⊥ } == od od∅
eq→ ∅0 {w} (lift ())
eq← ∅0 {w} lt = lift (¬x<0 lt)

∅< : { x y : HOD  } → odef x (& y ) → ¬ (  od x  == od od∅  )
∅<  {x} {y} d eq with eq→ (==-trans eq (==-sym ∅0) ) d
∅<  {x} {y} d eq | lift ()

¬x∋y→x≡od∅  : { x : HOD  } → ({y : Ordinal } → ¬ odef x y ) → (& x) ≡ & od∅ 
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
⊆→o≤→c<→o< peq ⊆→o≤ {x} {y} y∋x | tri≈ ¬a b ¬c = ⊥-elim ( o<¬≡ (peq {x}) (pair<y (eq← (ord→== b) y∋x ) ) ) 
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
ε-induction {ψ} ind x = ε-induction-hod _ {& x} <-osuc x <-osuc where
     induction2 : (x₁ : Ordinal) →
            ((y : Ordinal) → y o< x₁ → (y₁ : HOD) → & y₁ o< osuc y → ψ y₁) →
            (y : HOD) → & y o< osuc x₁ → ψ y
     induction2 x prev y y≤x = ind (λ {y₁} lt → prev (& y₁) (lemma1 y₁ lt)  y₁ <-osuc  ) where
         lemma1 : (y₁ : HOD) → y ∋ y₁ →  & y₁ o< x
         lemma1 y₁ lt with trio< (& y₁) x
         ... | tri< a ¬b ¬c = a
         ... | tri> ¬a ¬b c = ⊥-elim (o≤> (ordtrans (c<→o< lt)  y≤x)  c )
         ... | tri≈ ¬a b ¬c with osuc-≡< y≤x
         ... | case1 y=x = subst (λ k → & y₁ o< k ) y=x (c<→o< lt)
         ... | case2 y<x = ⊥-elim ( o<¬≡ b ( (ordtrans (c<→o< lt) y<x)  )) 
     ε-induction-hod : (ox : Ordinal) { oy : Ordinal } → oy o< ox → (y : HOD) → & y o< osuc oy  → ψ y
     ε-induction-hod ox {oy} lt = TransFinite {λ oy → (y : HOD) → & y o< osuc oy →  ψ y} induction2 oy 

-- we cannot prove this...
-- ε-induction0 : { ψ : HOD  → Set n}
--    → ( {x : HOD } → ({ y : HOD } →  x ∋ y → ψ y ) → ψ x )
--    → (x : HOD ) → ψ x

-- Open supreme upper bound leads a contradition, so we use domain restriction on sup
¬open-sup : ( sup-o : (Ordinal →  Ordinal ) → Ordinal) → ((ψ : Ordinal →  Ordinal ) → (x : Ordinal) → ψ x  o<  sup-o ψ ) → ⊥
¬open-sup sup-o sup-o< = o<> <-osuc (sup-o< next-ord (sup-o next-ord)) where
   next-ord : Ordinal → Ordinal
   next-ord x = osuc x

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
union→ X z u xx =  record { owner = & u ; ao = proj1 xx ; ox = eq← *iso (proj2 xx) } 
union← :  (X z : HOD) (X∋z : Union X ∋ z) →  ¬  ( (u : HOD ) → ¬ ((X ∋  u) ∧ (u ∋ z )))
union← X z UX∋z not = ⊥-elim ( not (* (Own.owner UX∋z)) ⟪ subst (λ k → odef X k) (sym &iso) ( Own.ao UX∋z) , Own.ox UX∋z ⟫  )

--
--
--

ψiso :  {ψ : HOD  → Set n} {x y : HOD } → ψ x → x ≡ y   → ψ y
ψiso {ψ} t refl = t

record RCod (COD : HOD) (ψ : HOD → HOD)  : Set (suc n) where
 field
     ≤COD : ∀ {x : HOD } → ψ x ⊆ COD 
     ψ-eq : ∀ {x y : HOD } → od x == od y  → ψ x =h= ψ y 

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
replacement← {ψ} X x lt {C} rc = record { z = & x ; az = lt  ; x=ψz = ==→o≡ (RCod.ψ-eq rc (==-sym *iso) ) }
replacement→ : {ψ : HOD → HOD} (X x : HOD) → {C : HOD} → (rc : RCod C ψ ) → (lt : Replace X ψ rc ∋ x) 
   →  ¬ ( (y : HOD) → ¬ (x =h= ψ y))
replacement→ {ψ} X x {C} rc lt eq = eq (* (Replaced.z lt)) (ord→== (Replaced.x=ψz lt)) 

--
-- If we have LEM, Replace' is equivalent to Replace
--
-- we should remove Replace' and Replace'-iso1?
-- the reason why we need Replace' is we cannot have Dec on X ∋ x without LEM.

record RXCod (X COD : HOD) (ψ : (x : HOD) → X ∋ x → HOD)  : Set (suc n) where
 field
     ≤COD : ∀ {x : HOD } → (lt : X ∋ x) → ψ x lt ⊆ COD 
     ψ-eq : ∀ {x : HOD } → (lt lt1 : X ∋ x) → ψ x lt =h= ψ x lt1

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
      → RXCod (* (& X)) C (λ y xy → ψ y (eq→ *iso xy)) 
cod-conv X ψ {C} rc = record { ≤COD = λ {x} lt → RXCod.≤COD rc (eq→ *iso lt ) 
        ; ψ-eq = λ {x} lt lt1 → RXCod.ψ-eq rc (eq→ *iso lt) (eq→ *iso lt1) } 

Replace'-iso : {X Y : HOD} → {fx : (x : HOD) → X ∋ x → HOD} {fy : (x : HOD) → Y ∋ x → HOD}
    → {CX : HOD} → (rcx : RXCod X CX fx  ) → {CY : HOD} → (rcy : RXCod Y CY fy   )
      → X ≡ Y →  ( (x :  HOD) → (xx : X ∋ x ) → (yy : Y ∋ x ) → fx _ xx ≡ fy _ yy )
      → od (Replace' X fx rcx ) == od (Replace' Y fy rcy)
Replace'-iso {X} {X} {fx} {fy} _ _ refl eq  = record { eq→ = ri0 ; eq← = ri1 } where
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
      → od (Replace' (* (& X)) (λ y xy → ψ y (eq→ *iso xy) ) (cod-conv X ψ rc))
         == od ( Replace' X ( λ y xy → ψ y xy ) rc )
Replace'-iso1 X ψ rc = record { eq→ = ri0 ; eq← = ri1 } where
      ri0 : {x : Ordinal} → Replaced1 (* (& X))
            (λ z xz → & (ψ (* z) (eq→ *iso (subst (odef (* (& X))) (sym &iso) xz)))) x →
            Replaced1 X (λ z xz → & (ψ (* z) (subst (odef X) (sym &iso) xz))) x
      ri0 {x} record { z = z ; az = az ; x=ψz = x=ψz } = record { z = z ; az = eq→  *iso az 
          ; x=ψz = trans x=ψz (==→o≡ (RXCod.ψ-eq rc _ _ )) } 
      ri1 : {x : Ordinal} → 
            Replaced1 X (λ z xz → & (ψ (* z) (subst (odef X) (sym &iso) xz))) x →
              Replaced1 (* (& X)) (λ z xz → & (ψ (* z) (eq→ *iso (subst (odef (* (& X))) (sym &iso) xz)))) x 
      ri1 {x} record { z = z ; az = az ; x=ψz = x=ψz } = record { z = z ; az = eq←  *iso az 
          ; x=ψz = trans x=ψz (==→o≡  (RXCod.ψ-eq rc _ _ ))  } 

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
power→ A t P∋t {x} t∋x = P∋t (& x) (eq← *iso t∋x )

power← :  (A t : HOD) → ({x : HOD} → (t ∋ x → A ∋ x)) → Power A ∋ t
power← A t t⊆A z xz = subst (λ k → odef A k ) &iso ( t⊆A  (subst (λ  k → odef t k) (sym &iso) (eq→ *iso xz )))

Power∋∅ : {S : HOD} → odef (Power S) o∅
Power∋∅ z xz = ⊥-elim (¬x<0 ( eq→ o∅==od∅ xz)  )

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
    lemma = record { owner = _ ; ao = case2 refl ; ox = eq← *iso (subst (λ k → odef (x , x)  k) (sym &iso) (case1 refl)) }

ux-2cases : {x y : HOD } → Union ( x , ( x ,  x)) ∋ y → ( & x ≡ & y ) ∨ ( x ∋ y )
ux-2cases {x} {y} record { owner = owner ; ao = (case1 eq) ; ox = ox } 
    = case2 (eq→ *iso (subst (λ k → odef k (& y)) (cong (*) eq)  ox ))
ux-2cases {x} {y} record { owner = owner ; ao = (case2 eq) ; ox = ox } with eq→ *iso (subst (λ k → odef k (& y))  (cong (*) eq) ox)
... | case1 y=x = case1 (sym y=x)
... | case2 y=x = case1 (sym y=x)

ux-transitve  : {x y : HOD} → x ∋ y →  Union ( x , ( x ,  x)) ∋ y 
ux-transitve {x} {y} ox  = record { owner = _ ; ao = case1 refl ; ox = eq← *iso ox }

--
-- Possible Ordinal Limit
--

--        our Ordinals is greater than Union ( x , ( x ,  x)) transitive closure
--
record ODAxiom-ho< : Set (suc n) where
 field
    omega : Ordinal  
    ho< : {x : Ordinal } → Omega-d x →  x o< omega

-- postulate
--    odaxion-ho< : ODAxiom-ho< 

-- open ODAxiom-ho< odaxion-ho<

Omega : ODAxiom-ho< → HOD
Omega ho< = record { od = record { def = λ x → Omega-d x } ; odmax = ODAxiom-ho<.omega ho< ; <odmax = λ lt → ODAxiom-ho<.ho< ho< lt }  

infinity∅ : (ho< : ODAxiom-ho<) →  Omega ho<  ∋ od∅
infinity∅ ho< = subst (λ k → odef (Omega ho<) k ) lemma iφ where
    lemma : o∅ ≡ & od∅
    lemma =  sym ord-od∅ 

Omega-iso : {x : HOD } →  od (Union (* (& x) , (* (& x) , * (& x)))) == od (Union (x , (x , x)))
Omega-iso {x} = record { eq→ = lemma2 ; eq← = lemma3 } where
  lemma2 :  {y : Ordinal} → Own (* (& x) , (* (& x) , * (& x))) y → Own (x , (x , x)) y
  lemma2 {y} record { owner = owner ; ao = case1 ao ; ox = ox } = record { owner = owner ; ao = case1 lemma4 ; ox = ox }  where
      lemma4 : owner ≡ & x
      lemma4 = trans ao ( ==→o≡ *iso )
  lemma2 {y} record { owner = owner ; ao = case2 ao ; ox = ox } = record { owner = owner ; ao = case2 lemma4 ; ox = ox }  where
      lemma4 : owner ≡ & (x , x) 
      lemma4 = trans ao ( ==→o≡ record { eq→ = lemma5 _ ; eq← = lemma6 _ } ) where
          lemma5 : (x₁ : Ordinal) → (x₁ ≡ & (* (& x))) ∨ (x₁ ≡ & (* (& x))) → (x₁ ≡ & x) ∨ (x₁ ≡ & x)
          lemma5 y (case1 eq) = case1 (trans eq (sym (==→o≡ (==-sym *iso) ) ))
          lemma5 y (case2 eq) = case1 (trans eq (sym (==→o≡ (==-sym *iso) ) ))
          lemma6 : (x₁ : Ordinal) → (x₁ ≡ & x) ∨ (x₁ ≡ & x) → (x₁ ≡ & (* (& x))) ∨ (x₁ ≡ & (* (& x))) 
          lemma6 y (case1 eq) = case1 (trans eq ((==→o≡ (==-sym *iso) ) ))
          lemma6 y (case2 eq) = case1 (trans eq ((==→o≡ (==-sym *iso) ) ))
  lemma3 :  {y : Ordinal}  → Own (x , (x , x)) y → Own (* (& x) , (* (& x) , * (& x))) y
  lemma3 {y} record { owner = owner ; ao = (case1 ao) ; ox = ox } = record { owner = owner 
        ; ao = case1 (trans ao (==→o≡ (==-sym *iso) )) ; ox = ox }
  lemma3 {y} record { owner = owner ; ao = (case2 ao) ; ox = ox } = record { owner = owner 
        ; ao = case2 (trans ao (==→o≡ record { eq→ = lemma5 _ ; eq← = lemma4 _  }))  ; ox = ox } where
       lemma4 : (x₁ : Ordinal) → (x₁ ≡ & (* (& x))) ∨ (x₁ ≡ & (* (& x))) → (x₁ ≡ & x) ∨ (x₁ ≡ & x)
       lemma4 y (case1 eq) = case1 ( trans eq (sym (==→o≡ (==-sym *iso) ) ))
       lemma4 y (case2 eq) = case1 ( trans eq (sym (==→o≡ (==-sym *iso) ) ))
       lemma5 : (x₁ : Ordinal) → (x₁ ≡ & x) ∨ (x₁ ≡ & x) → (x₁ ≡ & (* (& x))) ∨ (x₁ ≡ & (* (& x)))
       lemma5 y (case1 eq) = case1 ( trans eq ((==→o≡ (==-sym *iso) ) ))
       lemma5 y (case2 eq) = case1 ( trans eq ((==→o≡ (==-sym *iso) ) ))

infinity : (ho< : ODAxiom-ho<) → (x : HOD) → Omega ho< ∋ x → Omega ho< ∋ Union (x , (x , x ))
infinity ho< x lt = subst (λ k → odef (Omega ho<) k ) (==→o≡ Omega-iso) (isuc {& x} lt) 

pair→ : ( x y t : HOD  ) →  (x , y)  ∋ t  → ( t =h= x ) ∨ ( t =h= y )
pair→ x y t (case1 t≡x ) = case1 ( ord→== t≡x ) 
pair→ x y t (case2 t≡y ) = case2 ( ord→== t≡y )

pair← : ( x y t : HOD  ) → ( t =h= x ) ∨ ( t =h= y ) →  (x , y)  ∋ t
pair← x y t (case1 t=h=x) = case1 (==→o≡ t=h=x)  
pair← x y t (case2 t=h=y) = case2 (==→o≡ t=h=y)

pair-iso : {x y : HOD } →  (* (& x) , * (& y)) =h= (x , y)
pair-iso {x} {y} = record { eq→ = lem01 ; eq← = lem00  } where
  lem00 :  {z : Ordinal} →  (z ≡ & x) ∨ (z ≡ & y) → (z ≡ & (* (& x))) ∨ (z ≡ & (* (& y)))
  lem00 {z} (case1 z=x) = case1 (trans z=x ((==→o≡ (==-sym *iso) ) ))
  lem00 {z} (case2 z=y) = case2 (trans z=y ((==→o≡ (==-sym *iso) ) ))
  lem01 :  {z : Ordinal}  → (z ≡ & (* (& x))) ∨ (z ≡ & (* (& y))) →  (z ≡ & x) ∨ (z ≡ & y)
  lem01 {z} (case1 z=x) = case1 (trans z=x (sym (==→o≡ (==-sym *iso) ) ))
  lem01 {z} (case2 z=y) = case2 (trans z=y (sym (==→o≡ (==-sym *iso) ) ))

o<→c< :  {x y : Ordinal } → x o< y → (Ord x) ⊆ (Ord y)
o<→c< lt {z} ox = ordtrans ox lt

⊆→o< :  {x y : Ordinal } → (Ord x) ⊆ (Ord y) →  x o< osuc y
⊆→o< {x} {y}  lt with trio< x y
⊆→o< {x} {y}  lt | tri< a ¬b ¬c = ordtrans a <-osuc
⊆→o< {x} {y}  lt | tri≈ ¬a b ¬c = subst ( λ k → k o< osuc y) (sym b) <-osuc
⊆→o< {x} {y}  lt | tri> ¬a ¬b c with lt  (o<-subst c (sym &iso) refl )
... | ttt = ⊥-elim ( o<¬≡ refl (o<-subst ttt &iso refl ))

open import zf

Select : (X : HOD  ) → (ψ : (x : HOD  ) → Set n )  ( zψ : ZPred HOD _∋_ _=h=_ ψ ) → HOD
Select X ψ zψ = record { od = record { def = λ x →  ( odef X x ∧ ψ ( * x )) } ; odmax = odmax X ; <odmax = λ y → <odmax X (proj1 y) }

selection : {ψ : HOD → Set n} → { zψ : ZPred HOD _∋_ _=h=_ ψ } → { X y : HOD} →   ((X ∋ y) ∧ ψ y) ⇔ (Select X ψ zψ ∋ y)
selection {ψ} {zψ} {X} {y}   = ⟪
     ( λ cond → ⟪ proj1 cond , peq  (proj2 cond) (==-sym *iso)  ⟫ )
  ,  ( λ select → ⟪ proj1 select  , peq (proj2 select) *iso  ⟫ )
  ⟫ where
     peq : {x y : HOD } →  ψ x →  od x == od y  → ψ y
     peq {x} {y} fx eq = proj1 (ZPred.ψ-cong zψ x y eq) fx

selection-in-domain : {ψ : HOD → Set n} { zψ : ZPred HOD _∋_ _=h=_ ψ } {X y : HOD} → Select X ψ zψ ∋ y → X ∋ y
selection-in-domain {ψ} {zψ} {X} {y} lt = proj1 ((proj2 (selection {ψ} {zψ} {X}  )) lt)

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
proj1 (extensionality {A} {B} {w} eq ) d = subst (λ k → odef w k) (==→o≡ (extensionality0 {A} {B} eq)) d
proj2 (extensionality {A} {B} {w} eq ) d = subst (λ k → odef w k) (sym (==→o≡ (extensionality0 {A} {B} eq))) d

ZFReplace : HOD  → ( ψ : HOD  → HOD) →  ( ZFunc HOD _∋_ _=h=_ ψ )→ HOD
ZFReplace X ψ zfψ = record { od = record { def = λ x → Replaced X (λ z → & (ψ (* z))) x  } ; odmax = & (ZFunc.cod zfψ) ; <odmax = rmax< } where
        rmax< :  {y : Ordinal} → Replaced X (λ z → & (ψ (* z))) y → y o< & (ZFunc.cod zfψ)
        rmax< {y} lt = subst (λ k → k o< & (ZFunc.cod zfψ) ) r01 (c<→o< (ZFunc.cod∋ψ zfψ (* (Replaced.z lt)) ) ) where
            r01 : & (ψ ( * (Replaced.z lt ) )) ≡ y
            r01 = sym (Replaced.x=ψz lt )

zf-replacement← :  {ψ : HOD → HOD} → {zfψ :  ZFunc HOD _∋_ _=h=_ ψ } → (X x : HOD) →  X ∋ x → ZFReplace X ψ zfψ ∋ ψ x
zf-replacement← {ψ} {zfψ} X x lt = record { z = & x ; az = lt  ; x=ψz = ==→o≡  (ZFunc.ψ-cong zfψ _ _ (==-sym *iso)  ) }
zf-replacement→ : {ψ : HOD → HOD} → {zfψ : ZFunc HOD _∋_ _=h=_ ψ } → (X x : HOD) 
     → (lt : ZFReplace X ψ zfψ ∋ x) → ¬ ( (y : HOD) → ¬ (x =h= ψ y))
zf-replacement→ {ψ} {zfψ} X x lt eq = eq (* (Replaced.z lt)) (ord→== (Replaced.x=ψz lt)) 

isZF :  (ho< : ODAxiom-ho< ) → IsZF HOD _∋_  _=h=_ od∅ _,_ Union Power Select ZFReplace (Omega ho<)
isZF ho< = record {
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
    ;   infinity∅ = infinity∅ ho<
    ;   infinity = infinity ho<
    ;   selection = λ {X} {ψ} {zψ} {y} → selection {X} {ψ} {zψ} {y} 
    ;   replacement← = λ {ψ} {zfψ} → zf-replacement← {ψ} {zfψ} 
    ;   replacement→ = λ {ψ} {zfψ} → zf-replacement→ {ψ} {zfψ} 
    }

HOD→ZF : ODAxiom-ho< → ZF
HOD→ZF ho< = record {
    ZFSet = HOD
    ; _∋_ = _∋_
    ; _≈_ = _=h=_
    ; ∅  = od∅
    ; _,_ = _,_
    ; Union = Union
    ; Power = Power
    ; Select = Select
    ; Replace = ZFReplace 
    ; infinite = Omega ho<
    ; isZF = isZF ho<
 }


