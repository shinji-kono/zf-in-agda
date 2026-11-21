{-# OPTIONS --cubical-compatible --safe #-}
open import Level hiding (zero ; suc)
open import Ordinals
open import logic
open import Relation.Nullary

open import Ordinals
import HODBase
import OD
open import Data.Nat.Properties

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

open import Level hiding ( suc ; zero )
open import Ordinals

open import filter O HODAxiom ho< AC 

open import Relation.Nullary 
-- open import Relation.Binary hiding ( _⇔_ )
open import Data.Empty 
open import Relation.Binary.PropositionalEquality
open import Data.Nat -- renaming ( zero to Zero ; suc to suc ;  ℕ to Nat ; _⊔_ to _n⊔_ ) 
import BAlgebra 

-- open BAlgebra O
open import ZProduct O HODAxiom ho<


-------
--    the set of finite partial functions from ω to 2
--    H(ω , 2)
--

open import Data.List hiding (filter)
open import Data.Maybe 


data Hω2 :  (i : ℕ) ( x : Ordinal  ) → Set n where
  hφ :  Hω2 0 o∅
  h0 : {i : ℕ} {x : Ordinal  } → Hω2 i x  →
    Hω2 (suc i) (& (Union (< nat→ω i , od∅ >  ,  * x )))
  h1 : {i : ℕ} {x : Ordinal  } → Hω2 i x  →
    Hω2 (suc i) (& (Union (< nat→ω i , nat→ω 1 > ,  * x )))
  he : {i : ℕ} {x : Ordinal  } → Hω2 i x  →
    Hω2 (suc i) x

record  Hω2r (x : Ordinal) : Set n where
  field
    count : ℕ
    hω2 : Hω2 count x

--  [] and [ nothing ] are the same, it has the same Ordimal

open Hω2r

hw⊆POmega :  {x : Ordinal} → Hω2r x → odef (Power (Power (Omega ho<))) x
hw⊆POmega {x} record { count = count ; hω2 = hw2 } = odmax1 count hw2 where
   odmax1 : {y : Ordinal} (i : ℕ)  →  Hω2 i y → odef (Power (Power (Omega ho<) )) y
   odmax1 .0 hφ z xz = ⊥-elim ( ¬x<0 (eq→  o∅==od∅  xz ))
   odmax1 (suc i) (h0 {_} {y} hw) = pf01 where
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
   odmax1 (suc i) (h1 {_} {y} hw) = pf01 where
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
   odmax1 (suc i) (he {_} {y} hw) = pf00 where
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
     i : ℕ
     isHw : Hω2 i x

data Two : Set where
  i0 : Two
  i1 : Two

list→hod : List (Maybe Two) → HwStep
list→hod []  = record { x = o∅ ; i = 0 ; isHw = hφ }
list→hod (just i0 ∷ t)  = record { x = & (Union ( < nat→ω (HwStep.i pf01) , od∅ >  , * x )) 
        ; i = suc (HwStep.i pf01) ; isHw = h0 (HwStep.isHw pf01) } where 
    pf01 : HwStep
    pf01 = list→hod t 
    x = HwStep.x pf01
list→hod (just i1 ∷ t)  = record { x = & (Union ( < nat→ω (HwStep.i pf01) , nat→ω 1 >  , * x )) 
        ; i = suc (HwStep.i pf01) ; isHw = h1 (HwStep.isHw pf01) } where 
    pf01 : HwStep
    pf01 = list→hod t 
    x = HwStep.x pf01
list→hod (nothing ∷ t)  = list→hod t 

list→hod-len : (x : List (Maybe Two)) → HwStep.i (list→hod x) ≤ length x  
list→hod-len [] = refl-≤
list→hod-len (just i0 ∷ x) = s≤s (list→hod-len x)
list→hod-len (just i1 ∷ x) = s≤s (list→hod-len x)
list→hod-len (nothing ∷ x) = ≤-trans  (list→hod-len x ) a≤sa 

3→Hω2 : List (Maybe Two) → HOD
3→Hω2 t = * (HwStep.x (list→hod t))  

Hω2→3 : (x :  HOD) → HODω2 ∋ x → List (Maybe Two) 
Hω2→3 x = lemma where
   lemma : { y : Ordinal } →  Hω2r y → List (Maybe Two)
   lemma  record { count = zero ; hω2 = hw } = lem01 _ zero hw refl where
       lem01 : (y : Ordinal ) → (i : ℕ) → Hω2 i y → i ≡ zero → List (Maybe Two)
       lem01 o∅ 0 hφ eq = []
       lem01 _ .(suc _) (h0 hw) ()
       lem01 _ .(suc _) (h1 hw) ()
       lem01 _ .(suc _) (he hw) ()
   lemma {y} record { count = suc count ; hω2 = hw } = lem01 _ _ hw refl where
       lem01 : (y : Ordinal ) → (i : ℕ) → Hω2 i y → i ≡ suc count → List (Maybe Two)
       lem01 _ _ hφ ()
       lem01 _ (suc i) (h0 hw) eq = just i0 ∷ lemma record { count = i ; hω2 =  hw }
       lem01 _ (suc i) (h1 hw) eq = just i1 ∷ lemma record { count = i ; hω2 =  hw }
       lem01 y (suc i) (he hw) eq = nothing ∷ lemma record { count = i ; hω2 =  hw }

ω→2 : HOD
ω→2 = Power (Omega ho<)

ω2→f : (x : HOD) → ω→2 ∋ x → ℕ → Two
ω2→f x lt n with ODC.∋-p x (nat→ω n)
ω2→f x lt n | yes0 p = i1
ω2→f x lt n | no0 ¬p = i0

fω→2-sel : ( f : ℕ → Two ) (x : HOD) → Set n
fω→2-sel f x = (Omega ho< ∋ x) ∧ ( (lt : odef (Omega ho<) (&  x) ) → f (ω→nat x lt) ≡ i1 )

open import zf

fω→2-wld : ( f : ℕ → Two ) → ZPred HOD _∋_ _=h=_ (fω→2-sel f)
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

fω→2 : (ℕ → Two) → HOD
fω→2 f = Select (Omega ho<) (fω→2-sel f) (fω→2-wld f) 

ω2∋f : (f : ℕ → Two) → ω→2 ∋ fω→2 f
ω2∋f f = power← (Omega ho<) (fω→2 f) (λ {x} lt →  proj1 ((proj2 (selection {fω→2-sel f} {fω→2-wld f} {Omega ho<} {x} )) lt))

ω→2f≡i1 : (X i : HOD) → (iω : (Omega ho<) ∋ i) → (lt : ω→2 ∋ X ) → ω2→f X lt (ω→nat i iω)  ≡ i1 → X ∋ i
ω→2f≡i1 X i iω lt eq with ODC.∋-p X (nat→ω (ω→nat i iω))
ω→2f≡i1 X i iω lt eq | yes0 p = subst (λ k → odef X k) (==→o≡ (nat→ω-iso iω )) p
ω→2f≡i1 X i iω lt () | no0 n

ω2→f-iso : (X : HOD) → ( lt : ω→2 ∋ X ) → fω→2 ( ω2→f X lt )  =h= X
eq→ (ω2→f-iso X lt) {x} ⟪ ωx , ⟪ ωx1 , iso ⟫ ⟫ = le00 where
    le00 : odef X x
    le00 = subst (λ k → odef X k) &iso ( ω→2f≡i1 _ _ ωx1 lt  (iso ωx1)  )
eq← (ω2→f-iso X lt) {x} Xx = ⟪ subst (λ k → odef (Omega ho<) k) &iso le02  , ⟪ le02 , le01 ⟫ ⟫ where
    le02 : (Omega ho<) ∋ * x
    le02 = power→ (Omega ho<) _ lt (subst (λ k → odef X k) (sym &iso) Xx) 
    le01 : (wx : odef (Omega ho<) (& (* x))) → ω2→f X lt (ω→nat (* x) wx) ≡ i1
    le01 wx   with ODC.∋-p  X (nat→ω (ω→nat _ wx) )
    ... | yes0 p  = refl
    ... | no0 ¬p  = ⊥-elim ( ¬p (subst (λ k → odef X k ) le03 Xx )) where
        le03 :  x ≡ & (nat→ω (ω→nato wx))
        le03 = trans (sym &iso) (sym (==→o≡ ( nat→ω-iso wx ) ))

¬i1→i0 : {x : Two} → ¬ (x ≡ i1 ) → x ≡ i0 
¬i1→i0 {i0} ne = refl
¬i1→i0 {i1} ne = ⊥-elim ( ne refl )

fω→2-iso : (f : ℕ → Two) → (x : ℕ ) → ω2→f ( fω→2 f ) (ω2∋f f) x ≡  f x
fω→2-iso f x = le01 x  where
    le01 : (x : ℕ) → ω2→f (fω→2 f) (ω2∋f f) x ≡ f x
    le01 x with  ODC.∋-p (fω→2 f) (nat→ω x) 
    le01 x | yes0 p = subst (λ k → i1 ≡ f k ) (ω→nat-iso0 x (proj1 (proj2 p)) (==-trans *iso *iso)) (sym ((proj2 (proj2 p)) le02)) where
        le02 :  Omega-d (& (* (& (nat→ω x))))
        le02 = proj1 (proj2 p )
    le01 x | no0 ¬p = sym ( ¬i1→i0 le04 ) where
        le04 : ¬ f x ≡ i1
        le04 fx=1 = ¬p ⟪ ω∋nat→ω {x} , ⟪ subst (λ k → Omega-d k) (sym &iso) (ω∋nat→ω {x})  , le05 ⟫ ⟫ where
            le05 : (lt : Omega-d (& (* (& (nat→ω x))))) → f (ω→nato lt) ≡ i1
            le05 lt = trans (cong f (ω→nat-iso0 x lt (==-trans *iso *iso))) fx=1

--
-- H(ω x ω, 2)
--   { P | Func p ∧ (dom p ⊆ ω x ω) ∧ (finite (dom p) ∧ ran p ⊆ 2) }
-- it is ordered by p ≤ q iff q ⊆ p
--
-- List (Maybe (List (Maybe Two)))

data Hww2 :  (i : ℕ) ( x : Ordinal  ) → Set n where
  hjφ :  Hww2 0 o∅
  hj : {i j : ℕ} {x y : Ordinal  } → Hω2 j y → Hww2 i x  
    → Hww2 (suc i) (& (Union (< nat→ω i , * y >  ,  * x )))

-- [ [] , x ] and x are different here. we may add ¬ (y  ≡ o∅ )

record  Hww2r (x : Ordinal) : Set n where
  field
    count : ℕ
    hww2 : Hww2 count x

open Hww2r

hww2⊆POmega :  {x : Ordinal} → Hww2r x → odef (Power (Power (Omega ho< ∪ (Power (Power (Omega ho<)))))) x
hww2⊆POmega {x} record { count = count ; hww2 = lt } = odmax1 count lt  where
   A : HOD
   A = (Omega ho<) ∪ (Power (Power (Omega ho<)))
   odmax1 : {y : Ordinal} (i : ℕ)  →  Hww2 i y → odef (Power (Power A )) y
   odmax1 {y} zero lt = odmax3 where
      odmax2 : (i :  ℕ  ) → i ≡ 0 →  Hww2 i y → y ≡ o∅
      odmax2 i eq hjφ = refl
      odmax2 i () (hj _ _ )
      odmax3 : odef (Power (Power A )) y
      odmax3 = subst (λ k → odef (Power (Power A)) k ) (sym (odmax2 zero refl lt)) (Power∋∅ {Power A}) 
   odmax1 {y} (suc i) lt  z xz = odmax2 _ refl lt where
      odmax2 : (j :  ℕ  ) → j ≡ suc i →  Hww2 j y → odef (Power A ) z
      odmax2 j () hjφ 
      odmax2 j j=si (hj {i2} {j2} {x2} {y2} lt1 lt2 ) w lt3 = odmax3 (eq→ *iso xz ) where
          odmax3 :  odef (Union (< nat→ω i2 , * y2 > , * x2 )) z → odef A w
          odmax3 record { owner = _ ; ao = case1 refl ; ox = ox } = odmax10 where 
              odmax10 : odef (Omega ho<) w ∨ odef (Power (Power (Omega ho<))) w
              odmax10 with eq→ *iso ox 
              ... | case1 refl = case1 (odmax5 (eq→ *iso lt3  )) where
                 odmax5 : odef (nat→ω i2 , nat→ω i2) w → Omega-d w 
                 odmax5 (case1 refl) = ω∋nat→ω {i2 } 
                 odmax5 (case2 refl) = ω∋nat→ω {i2 }
              ... | case2 refl with eq→ *iso lt3  
              ... | case1 refl = case1 (ω∋nat→ω {i2 }  )
              ... | case2 refl = case2 (subst (λ k → odef (Power (Power (Omega ho<))) k ) (sym &iso)  (hw⊆POmega  record { count = j2 ; hω2 = lt1 }  ) )
          odmax3 record { owner = owner ; ao = case2 refl ; ox = ox } = odmax10  where
              odmax10 : odef (Omega ho<) w ∨ odef (Power (Power (Omega ho<))) w
              odmax10 with eq→ *iso xz 
              ... | record { owner = ow ; ao = case1 refl ; ox = oz } = odmax11  where
                 odmax11 : odef (Omega ho<) w ∨ odef (Power (Power (Omega ho<))) w
                 odmax11 with eq→ *iso oz
                 ... | case1 refl = case1 (odmax12 (eq→ *iso lt3) ) where
                    odmax12 : odef (nat→ω i2 , nat→ω i2) w → Omega-d w 
                    odmax12 (case1 refl) = ω∋nat→ω {i2 } 
                    odmax12 (case2 refl) = ω∋nat→ω {i2 }
                 ... | case2 refl = (odmax12 (eq→ *iso lt3 )) where
                    odmax12 : odef (nat→ω i2 , * y2 ) w → Omega-d w ∨ odef (Power (Power (Omega ho<))) w
                    odmax12 (case1 refl) = case1 ( ω∋nat→ω {i2 }  )
                    odmax12 (case2 refl) = case2 (subst (λ k → odef (Power (Power (Omega ho<))) k ) (sym &iso)  (hw⊆POmega  record { count = j2 ; hω2 = lt1 }  ) )
              ... | record { owner = ow ; ao = case2 refl ; ox = _ } = odmax12  where
                 odmax12 :  odef (Omega ho<) w ∨ odef (Power (Power (Omega ho<))) w
                 odmax12 = odmax1 i2 lt2 _ (subst (λ k → odef (* k) z) (&iso) ox)  _ lt3

HODww2 :  HOD
HODww2 = record { od = record { def = λ x → Hww2r x } ; odmax = & (Power (Power (Omega ho< ∪ (Power (Power (Omega ho<))))))  
  ; <odmax = λ lt → odef< ( hww2⊆POmega lt) } 

record Hww2Step : Set n where
   field 
     x : Ordinal
     i : ℕ
     isHw : Hww2 i x

list→hodw2 : List (Maybe (List (Maybe Two) ) ) → Hww2Step
list→hodw2 []  = record { x = o∅ ; i = 0 ; isHw = hjφ }
list→hodw2 (just (nothing ∷ t2) ∷ ts)  = list→hodw2 ts
list→hodw2 (just (just t1 ∷ t2) ∷ ts)  = record { x = & (Union ( < nat→ω (Hww2Step.i pf01) , * y >  , * ( Hww2Step.x pf01  ))) 
        ; i = suc (Hww2Step.i pf01) ; isHw = hj hw (Hww2Step.isHw pf01)  } where 
    pf01 : Hww2Step
    pf01 = list→hodw2 ts 
    t = just t1 ∷ t2
    y = HwStep.x (list→hod t)
    j = HwStep.i (list→hod t)
    hw = HwStep.isHw (list→hod t)
list→hodw2 (just [] ∷ ts)  = record { x = Hww2Step.x pf01 ; i = Hww2Step.i pf01 ; isHw = Hww2Step.isHw pf01 } where
   pf01 : Hww2Step
   pf01 = list→hodw2 ts
list→hodw2 (nothing ∷ ts)  = record { x = Hww2Step.x pf01 ; i = Hww2Step.i pf01 ; isHw = Hww2Step.isHw pf01 } where
   pf01 : Hww2Step
   pf01 = list→hodw2 ts

3→Hωw2 : List (Maybe (List (Maybe Two) ) ) → HOD
3→Hωw2 t = * (Hww2Step.x (list→hodw2 t))  

Hωw2→3 : (x :  HOD) → HODww2 ∋ x → List (Maybe (List (Maybe Two) ) )
Hωw2→3 x h = lemma (& x) h where
  lemma : ( y : Ordinal ) →  Hww2r y → List (Maybe (List (Maybe Two) ) )
  lemma x record { count = zero ; hww2 = hw } = lem01 _ zero hw refl  where
       lem01 : (y : Ordinal ) → (i : ℕ) → Hww2 i y → i ≡ zero → List (Maybe (List (Maybe Two)))
       lem01 y i hjφ eq = []
       lem01 y i (hj x hw  ) ()
  lemma x record { count = suc count ; hww2 = hw } = lem01 _ _ hw refl where 
       lem01 : (y : Ordinal ) → (i : ℕ) → Hww2 i y → i ≡ suc count → List (Maybe (List (Maybe Two)))
       lem01 y i hjφ ()
       lem01 y i (hj {i2} {j2} {x2} {y2} x hw1  ) eq = just lem07 ∷ lemma _ record { count = i2 ; hww2 =  hw1 } where
          lem08 : Hω2r (& (* y2 ))  -- I don't know why
          lem08 = record { count = j2 ; hω2 = subst (λ k → Hω2 j2 k ) (sym &iso) x } 
          lem07 : List (Maybe Two)
          lem07 = Hω2→3 _ lem08

-- Hωw2→3-cong : (x y :  HOD) → (hx : HODww2 ∋ x) (hy : HODww2 ∋ y) → x =h= y →  Hωw2→3 x hx  = Hωw2→3 y hy  
-- Hωw2→3-cong  = ?

--Hωw2→3-iso : (x :  HOD) → (hx : HODww2 ∋ x ) → 3→Hωw2 (Hωw2→3 x hx )  =h= x
--Hωw2→3-iso  = ?
--
--

-- Hw2isFilter : Filter {HODω2} {ω→2}  hw⊆POmega
-- Hw2isFilter = record { filter = ? ; f⊆L = ? ; filter1 = ? ; filter2 = ? }

-- Hw2isFilter1 : Filter {?} {?}  ?
-- Hw2isFilter1 = record { filter = HODω2 ; f⊆L = ? ; filter1 = ? ; filter2 = ? }
--
-- Hw2isFilter : Filter {HODω2} {?}  ?
-- Hw2isFilter = record { filter = ? ; f⊆L = ? ; filter1 = ? ; filter2 = ? }
