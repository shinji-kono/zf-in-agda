{-# OPTIONS --cubical-compatible --safe #-}
open import Level
open import Ordinals
open import logic
open import Relation.Nullary

open import Level
open import Ordinals
import HODBase
import OD
open import Relation.Nullary
module PFOD {n : Level } (O : Ordinals {n} ) (HODAxiom : HODBase.ODAxiom O)  (ho< : OD.ODAxiom-ho< O HODAxiom )
       (AC : OD.AxiomOfChoice O HODAxiom ) where


open import  Relation.Binary.PropositionalEquality hiding ( [_] )
open import Data.Empty

import OrdUtil

open Ordinals.Ordinals  O
open Ordinals.IsOrdinals isOrdinal
import ODUtil

open import logic
open import nat

open OrdUtil O
open ODUtil O HODAxiom  ho<

open _∧_
open _∨_
open Bool

open  HODBase._==_

open HODBase.ODAxiom HODAxiom  
open OD O HODAxiom

open HODBase.HOD

open AxiomOfChoice AC
open import ODC O HODAxiom AC as ODC

open import Level
open import Ordinals

import filter 

open import Relation.Nullary 
-- open import Relation.Binary hiding ( _⇔_ )
open import Data.Empty 
open import Relation.Binary.PropositionalEquality
open import Data.Nat renaming ( zero to Zero ; suc to Suc ;  ℕ to Nat ; _⊔_ to _n⊔_ ) 
import BAlgebra 

-- open BAlgebra O
open import ZProduct O HODAxiom ho<


-------
--    the set of finite partial functions from ω to 2
--
--

open import Data.List hiding (filter)
open import Data.Maybe 


data Hω2 :  (i : Nat) ( x : Ordinal  ) → Set n where
  hφ :  Hω2 0 o∅
  h0 : {i : Nat} {x : Ordinal  } → Hω2 i x  →
    Hω2 (Suc i) (& (Union (< nat→ω i , od∅ >  ,  * x )))
  h1 : {i : Nat} {x : Ordinal  } → Hω2 i x  →
    Hω2 (Suc i) (& (Union (< nat→ω i , nat→ω 1 > ,  * x )))
  he : {i : Nat} {x : Ordinal  } → Hω2 i x  →
    Hω2 (Suc i) x

record  Hω2r (x : Ordinal) : Set n where
  field
    count : Nat
    hω2 : Hω2 count x

open Hω2r

hw⊆POmega :  {x : Ordinal} → Hω2r x → odef (Power (Power (Omega ho<))) x
hw⊆POmega {x} r = odmax1 (Hω2r.count r) (Hω2r.hω2 r) where
    odmax1 : {y : Ordinal} (i : Nat)  →  Hω2 i y → odef (Power (Power (Omega ho<) )) y
    odmax1 0 hφ z xz = ⊥-elim ( ¬x<0 (eq→  o∅==od∅  xz ))
    odmax1 (Suc i) (h0 {_} {y} hw) = pf01 where
        pf00 : odef ( Power (Power (Omega ho<))) y
        pf00 = odmax1 i hw
        pf01 : odef (Power (Power (Omega ho<))) (& (Union (< nat→ω i , nat→ω 0 > , * y)))
        pf01 z xz with eq→  *iso xz
        ... | record { owner = owner ; ao = case1 refl ; ox = ox } = pf02 where
             pf02 : (w : Ordinal) → odef (* z) w → Omega-d w
             pf02 w zw with eq→  *iso ox  
             ... | case2 refl with eq→ *iso zw
             ... | case1 refl = ω∋nat→ω {i}
             ... | case2 refl = ω∋nat→ω {0}
             pf02 w zw | case1 refl with eq→  *iso zw
             ... | case1 refl = ω∋nat→ω {i}
             ... | case2 refl = ω∋nat→ω {i} 
        ... | record { owner = owner ; ao = case2 refl ; ox = ox } = pf02 where
             pf03 : odef ( Power (Power (Omega ho<))) y
             pf03 = odmax1 i hw
             pf02 : (w : Ordinal) → odef (* z) w → Omega-d w
             pf02 w zw = odmax1 i hw _ (subst (λ k → odef (* k) z) (&iso) ox)  _ zw
    odmax1 (Suc i) (h1 {_} {y} hw) = pf01 where
        pf00 : odef ( Power (Power (Omega ho<))) y
        pf00 = odmax1 i hw
        pf01 : odef (Power (Power (Omega ho<))) (& (Union (< nat→ω i , nat→ω 1 > , * y)))
        pf01 z xz with eq→ *iso xz
        ... | record { owner = owner ; ao = case1 refl ; ox = ox } = pf02 where
             pf02 : (w : Ordinal) → odef (* z) w → Omega-d w
             pf02 w zw with eq→ *iso ox  
             ... | case2 refl with eq→ *iso zw
             ... | case1 refl = ω∋nat→ω {i}
             ... | case2 refl = ω∋nat→ω {1}
             pf02 w zw | case1 refl with eq→ *iso zw
             ... | case1 refl = ω∋nat→ω {i}
             ... | case2 refl = ω∋nat→ω {i}
        ... | record { owner = owner ; ao = case2 refl ; ox = ox } = pf02 where
             pf03 : odef ( Power (Power (Omega ho<))) y
             pf03 = odmax1 i hw
             pf02 : (w : Ordinal) → odef (* z) w → Omega-d w
             pf02 w zw = odmax1 i hw _ (subst (λ k → odef (* k) z) (&iso) ox)  _ zw
    odmax1 (Suc i) (he {_} {y} hw) = pf00 where
        pf00 : odef ( Power (Power (Omega ho<))) y
        pf00 = odmax1 i hw

--
-- Set of limited partial function of Omega
--
HODω2 :  HOD
HODω2 = record { od = record { def = λ x → Hω2r x } ; odmax = & (Power (Power (Omega ho<)))
  ; <odmax = λ lt → odef< (hw⊆POmega  lt) } 

HODω2⊆Omega : {x : HOD} → HODω2 ∋ x → x ⊆ Power  (Omega ho<) 
HODω2⊆Omega {x} hx {z} wz = hw⊆POmega hx _ (eq← *iso wz)

record HwStep : Set n where
   field 
     x : Ordinal
     i : Nat
     isHw : Hω2 i x

data Two : Set where
  i0 : Two
  i1 : Two

3→Hω2 : List (Maybe Two) → HOD
3→Hω2 t = * (HwStep.x (list→hod t))  where
   list→hod : List (Maybe Two) → HwStep
   list→hod []  = record { x = o∅ ; i = 0 ; isHw = hφ }
   list→hod (just i0 ∷ t)  = record { x = & (Union ( < nat→ω (HwStep.i pf01) , od∅ >  , * x )) 
            ; i = Suc (HwStep.i pf01) ; isHw = h0 (HwStep.isHw pf01) } where 
        pf01 : HwStep
        pf01 = list→hod t 
        x = HwStep.x pf01
   list→hod (just i1 ∷ t)  = record { x = & (Union ( < nat→ω (HwStep.i pf01) , nat→ω 1 >  , * x )) 
            ; i = Suc (HwStep.i pf01) ; isHw = h1 (HwStep.isHw pf01) } where 
        pf01 : HwStep
        pf01 = list→hod t 
        x = HwStep.x pf01
   list→hod (nothing ∷ t)  = list→hod t 

Hω2→3 : (x :  HOD) → HODω2 ∋ x → List (Maybe Two) 
Hω2→3 x = lemma where
   lemma : { y : Ordinal } →  Hω2r y → List (Maybe Two)
   lemma record { count = 0 ; hω2 = hφ } = []
   lemma record { count = (Suc i) ; hω2 = (h0 hω3) } = just i0 ∷ lemma record { count = i ; hω2 =  hω3 }
   lemma record { count = (Suc i) ; hω2 = (h1 hω3) } = just i0 ∷ lemma record { count = i ; hω2 =  hω3 }
   lemma record { count = (Suc i) ; hω2 = (he hω3) } = nothing ∷ lemma record { count = i ; hω2 =  hω3 }

ω→2 : HOD
ω→2 = Power (Omega ho<)

ω2→f : (x : HOD) → ω→2 ∋ x → Nat → Two
ω2→f x lt n with ∋-p x (nat→ω n)
ω2→f x lt n | yes p = i1
ω2→f x lt n | no ¬p = i0

fω→2-sel : ( f : Nat → Two ) (x : HOD) → Set n
fω→2-sel f x = (Omega ho< ∋ x) ∧ ( (lt : odef (Omega ho<) (&  x) ) → f (ω→nat x lt) ≡ i1 )

open import zf

fω→2-wld : ( f : Nat → Two ) → ZPred HOD _∋_ _=h=_ (fω→2-sel f)
fω→2-wld f = record { ψ-cong = f00 } where
     f01 : (x y : HOD) (ltx : odef (Omega ho<) (& x)) (lty : odef (Omega ho<) (& y)) → x =h= y →  f (ω→nat x ltx) ≡ i1  → f (ω→nat y lty) ≡ i1
     f01 x y ltx lty x=y feq = subst (λ k → f k ≡ i1 ) (ω→nato-cong ltx lty (==→o≡ x=y) ) feq
     f00 :  (x y : HOD) → x =h= y → (fω→2-sel f x ) ⇔ (fω→2-sel f y)
     proj1 (f00 x y x=y) fs = ⟪ subst (λ k → odef (Omega ho<)  k) (==→o≡ x=y)       (proj1 fs)  , (λ lt → f01 x y (proj1 fs) lt x=y (f02 fs)) ⟫ where
         f02 : (fs : fω→2-sel f x ) →  f (ω→nat x (proj1 fs)) ≡ i1   -- work around for cubical bug?
         f02 ⟪ wx , wx→eq ⟫ = wx→eq wx
     proj2 (f00 x y x=y) fs = ⟪ subst (λ k → odef (Omega ho<)  k) (sym (==→o≡ x=y)) (proj1 fs)  , (λ lt → f01 y x (proj1 fs) lt (==-sym x=y) (f02 fs)) ⟫ where
         f02 : (fs : fω→2-sel f y ) →  f (ω→nat y (proj1 fs)) ≡ i1
         f02 ⟪ wy , wy→eq ⟫ = wy→eq wy

fω→2 : (Nat → Two) → HOD
fω→2 f = Select (Omega ho<) (fω→2-sel f) (fω→2-wld f) 

ω2∋f : (f : Nat → Two) → ω→2 ∋ fω→2 f
ω2∋f f = power← (Omega ho<) (fω→2 f) (λ {x} lt →  proj1 ((proj2 (selection {fω→2-sel f} {fω→2-wld f} {Omega ho<} {x} )) lt))

ω→2f≡i1 : (X i : HOD) → (iω : (Omega ho<) ∋ i) → (lt : ω→2 ∋ X ) → ω2→f X lt (ω→nat i iω)  ≡ i1 → X ∋ i
ω→2f≡i1 X i iω lt eq with ∋-p X (nat→ω (ω→nat i iω))
ω→2f≡i1 X i iω lt eq | yes p = subst (λ k → odef X k) (==→o≡ (nat→ω-iso iω )) p

ω2→f-iso : (X : HOD) → ( lt : ω→2 ∋ X ) → fω→2 ( ω2→f X lt )  =h= X
eq→ (ω2→f-iso X lt) {x} ⟪ ωx , ⟪ ωx1 , iso ⟫ ⟫ = le00 where
    le00 : odef X x
    le00 = subst (λ k → odef X k) &iso ( ω→2f≡i1 _ _ ωx1 lt  (iso ωx1)  )
eq← (ω2→f-iso X lt) {x} Xx = ⟪ subst (λ k → odef (Omega ho<) k) &iso le02  , ⟪ le02 , le01 ⟫ ⟫ where
    le02 : (Omega ho<) ∋ * x
    le02 = power→ (Omega ho<) _ lt (subst (λ k → odef X k) (sym &iso) Xx) 
    le01 : (wx : odef (Omega ho<) (& (* x))) → ω2→f X lt (ω→nat (* x) wx) ≡ i1
    le01 wx   with ∋-p  X (nat→ω (ω→nat _ wx) )
    ... | yes p  = refl
    ... | no ¬p  = ⊥-elim ( ¬p (subst (λ k → odef X k ) le03 Xx )) where
        le03 :  x ≡ & (nat→ω (ω→nato wx))
        le03 = trans (sym &iso) (sym (==→o≡ ( nat→ω-iso wx ) ))

¬i1→i0 : {x : Two} → ¬ (x ≡ i1 ) → x ≡ i0 
¬i1→i0 {i0} ne = refl
¬i1→i0 {i1} ne = ⊥-elim ( ne refl )

fω→2-iso : (f : Nat → Two) → (x : Nat ) → ω2→f ( fω→2 f ) (ω2∋f f) x ≡  f x
fω→2-iso f x = le01 x  where
    le01 : (x : Nat) → ω2→f (fω→2 f) (ω2∋f f) x ≡ f x
    le01 x with  ∋-p (fω→2 f) (nat→ω x) 
    le01 x | yes p = subst (λ k → i1 ≡ f k ) (ω→nat-iso0 x (proj1 (proj2 p)) (==-trans *iso *iso)) (sym ((proj2 (proj2 p)) le02)) where
        le02 :  Omega-d (& (* (& (nat→ω x))))
        le02 = proj1 (proj2 p )
    le01 x | no ¬p = sym ( ¬i1→i0 le04 ) where
        le04 : ¬ f x ≡ i1
        le04 fx=1 = ¬p ⟪ ω∋nat→ω {x} , ⟪ subst (λ k → Omega-d k) (sym &iso) (ω∋nat→ω {x})  , le05 ⟫ ⟫ where
            le05 : (lt : Omega-d (& (* (& (nat→ω x))))) → f (ω→nato lt) ≡ i1
            le05 lt = trans (cong f (ω→nat-iso0 x lt (==-trans *iso *iso))) fx=1

