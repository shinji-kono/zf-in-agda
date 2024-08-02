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
module filter {n : Level } (O : Ordinals {n} ) (HODAxiom : HODBase.ODAxiom O)  (ho< : OD.ODAxiom-ho< O HODAxiom )
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

-- import BAlgebra 
-- open BAlgebra O
-- 
-- L is a boolean algebra, but we don't assume this explicitly
--
--     NEG : {p : HOD} → L ∋ p → L ∋ (P ＼ p)
--     CAP : {p q : HOD} → L ∋ p → L ∋ q → L ∋ (p ∩ q )
--
-- Kunen p.76 and p.53, we use ⊆
record Filter { L P : HOD  } (LP : L ⊆ Power P) : Set (suc n) where
   field
       filter  : HOD   
       f⊆L     : filter ⊆ L
       filter1 : { p q : HOD } →  L ∋ q → filter ∋ p →  p ⊆ q  → filter ∋ q
       filter2 : { p q : HOD } → filter ∋ p →  filter ∋ q  → L ∋ (p ∩ q) → filter ∋ (p ∩ q)

open Filter

record prime-filter { L P : HOD } {LP : L ⊆ Power P} (F : Filter {L} {P} LP) : Set (suc (suc n)) where
   field
       proper  : ¬ (filter F ∋ od∅)
       prime   : {p q : HOD } → L ∋ p → L ∋ q → filter F ∋ (p ∪ q) → ( filter F ∋ p ) ∨ ( filter F ∋ q )

record ultra-filter { L P : HOD } {LP : L ⊆ Power P} (F : Filter {L} {P} LP) : Set (suc (suc n)) where
   field
       proper  : ¬ (filter F ∋ od∅)
       ultra   : {p : HOD } → L ∋ p → L ∋  ( P ＼ p) → ( filter F ∋ p ) ∨ (  filter F ∋ ( P ＼ p) )

∈-filter : {L P p : HOD} →  {LP : L ⊆ Power P}  → (F : Filter {L} {P} LP ) → filter F ∋ p → L ∋ p 
∈-filter {L} {p} {LP} F lt = ( f⊆L F) lt 

⊆-filter : {L P p q : HOD } →  {LP : L ⊆ Power P } → (F : Filter {L} {P} LP) →  L ∋ q → q ⊆ P
⊆-filter {L} {P} {p} {q} {LP} F lt = power→⊆ P q ( LP lt )

∪-lemma1 : {L p q : HOD } → (p ∪ q)  ⊆ L → p ⊆ L
∪-lemma1 {L} {p} {q} lt p∋x = lt (case1 p∋x) 

∪-lemma2 : {L p q : HOD } → (p ∪ q)  ⊆ L → q ⊆ L
∪-lemma2 {L} {p} {q} lt p∋x = lt (case2 p∋x) 

q∩q⊆q : {p q : HOD } → (q ∩ p) ⊆ q 
q∩q⊆q lt = proj1 lt 

∩→≡1 : {p q : HOD } → p ⊆ q → (q ∩ p) =h= p
∩→≡1 {p} {q} p⊆q =  record { eq→ = c00 ; eq← = c01 } where
    c00 : {x : Ordinal} → odef (q ∩ p) x → odef p x
    c00 {x} qpx = proj2 qpx
    c01 : {x : Ordinal} → odef p x → odef (q ∩ p) x 
    c01 {x} px = ⟪ p⊆q px , px  ⟫

∩→≡2 : {p q : HOD } → q ⊆ p → (q ∩ p) =h= q
∩→≡2 {p} {q} q⊆p =  record { eq→ = c00 ; eq← = c01 } where
    c00 : {x : Ordinal} → odef (q ∩ p) x → odef q x
    c00 {x} qpx = proj1 qpx
    c01 : {x : Ordinal} → odef q x → odef (q ∩ p) x 
    c01 {x} qx = ⟪ qx , q⊆p qx  ⟫


-----
--
--  ultra filter is prime
--

filter-lemma1 :  {P L : HOD} → (LP : L ⊆ Power P)
     → ({p : HOD} → L ∋ p → L ∋ (P ＼ p))
     → ({p q : HOD} → L ∋ p → L ∋ q → L ∋ (p ∩ q ))
     → (F : Filter {L} {P} LP) → ultra-filter F  → prime-filter F 
filter-lemma1 {P} {L} LNEG NEG CAP F u = record {
         proper = ultra-filter.proper u
       ; prime = lemma3
    } where
  lemma3 : {p q : HOD} → L ∋ p → L ∋ q  → filter F ∋ (p ∪ q) → ( filter F ∋ p ) ∨ ( filter F ∋ q )
  lemma3 {p} {q} Lp Lq lt with ultra-filter.ultra u Lp (NEG Lp)
  ... | case1 p∈P  = case1 p∈P 
  ... | case2 ¬p∈P = case2 (filter1 F {q ∩ (P ＼ p)} Lq lemma7 lemma8) where
    lemma5 : ((p ∪ q ) ∩ (P ＼ p)) =h=  (q ∩ (P ＼ p))
    lemma5 = record { eq→ = λ {x} lt → ⟪ lemma4 x lt , proj2 lt  ⟫
       ;  eq← = λ {x} lt → ⟪  case2 (proj1 lt) , proj2 lt ⟫
      } where
         lemma4 : (x : Ordinal ) → odef ((p ∪ q) ∩ (P ＼ p)) x → odef q x
         lemma4 x lt with proj1 lt
         lemma4 x lt | case1 px = ⊥-elim ( proj2 (proj2 lt) px )
         lemma4 x lt | case2 qx = qx
    lemma9 : L ∋ ((p ∪ q ) ∩ (P ＼ p))
    lemma9 = subst (λ k → odef L k ) (sym (==→o≡ lemma5)) (CAP Lq (NEG Lp))
    lemma6 : filter F ∋ ((p ∪ q ) ∩ (P ＼ p))
    lemma6 = filter2 F lt ¬p∈P  lemma9
    lemma7 : filter F ∋ (q ∩ (P ＼ p))
    lemma7 =  subst (λ k → odef (filter F)  k ) (==→o≡ lemma5 ) lemma6
    lemma8 : (q ∩ (P ＼ p)) ⊆ q
    lemma8 lt = proj1 lt

-----
--
--  if Filter {L} {P} contains L, prime filter is ultra
--

U-F=∅→F⊆U : {L F U : HOD} → U ⊆ L  →  ((x : Ordinal) →  ¬ ( odef F x ∧ ( ¬ odef U x ))) → F ⊆ U
U-F=∅→F⊆U {L} {F} {U} U⊆L not = gt02  where
    gt02 : { x : Ordinal } → odef F x → odef U x
    gt02 {x} fx with ODC.∋-p U (* x)
    ... | yes0 y = subst (λ k → odef U k ) &iso y
    ... | no0  n = ⊥-elim ( not x ⟪ fx , subst (λ k → ¬ odef U k ) &iso n ⟫ )

filter-lemma2 :  {P L : HOD} → (LP : L ⊆ Power P)
       → ({p : HOD} → L ∋ p → L ∋ ( P ＼ p))
       → (F : Filter {L} {P} LP)  → filter F ∋ P → prime-filter F → ultra-filter F
filter-lemma2 {P} {L} LP NEG F f∋P prime = record {
         proper = prime-filter.proper prime
       ; ultra = λ {p}  L∋p _ → prime-filter.prime prime L∋p (NEG  L∋p) (lemma p (p⊆L  L∋p ))  
   } where
        p⊆L : {p : HOD} → L ∋ p  → p ⊆ P
        p⊆L {p} lt = power→⊆ P p ( LP lt )
        p+1-p=1 : {p : HOD} → p ⊆ P  → P =h= (p ∪ (P ＼ p)) 
        eq→ (p+1-p=1 {p} p⊆P) {x} lt with ODC.decp (odef p x)
        eq→ (p+1-p=1 {p} p⊆P) {x} lt | yes0 p∋x = case1 p∋x
        eq→ (p+1-p=1 {p} p⊆P) {x} lt | no0 ¬p = case2 ⟪ lt , ¬p ⟫
        eq← (p+1-p=1 {p} p⊆P) {x} ( case1 p∋x ) = subst (λ k → odef P k ) &iso (p⊆P ( subst (λ k → odef p k) (sym &iso) p∋x  )) 
        eq← (p+1-p=1 {p} p⊆P) {x} ( case2 ¬p  ) = proj1 ¬p
        lemma : (p : HOD) → p ⊆ P   →  filter F ∋ (p ∪ (P ＼ p))
        lemma p p⊆P = subst (λ k → odef (filter F ) k ) (==→o≡ (p+1-p=1 {p} p⊆P)) f∋P 

record Ideal   {L P : HOD } (LP : L ⊆ Power P) : Set (suc n) where
   field
       ideal : HOD   
       i⊆L :  ideal ⊆ L 
       ideal1 : { p q : HOD } →  L ∋ q  → ideal ∋ p →  q ⊆ p  → ideal ∋ q
       ideal2 : { p q : HOD } → ideal ∋ p →  ideal ∋ q  → L ∋ (p ∪ q) → ideal ∋ (p ∪ q)

open Ideal


proper-ideal : {L P : HOD} → (LP : L ⊆ Power P) → (P : Ideal {L} {P} LP ) → {p : HOD} → Set n
proper-ideal {L} {P} LP I = ideal I ∋ od∅

prime-ideal : {L P : HOD} → (LP : L ⊆ Power P) → Ideal {L} {P} LP → ∀ {p q : HOD } → Set n
prime-ideal {L} {P} LP I {p} {q} =  ideal I ∋ ( p ∩ q) → ( ideal I ∋ p ) ∨ ( ideal I ∋ q )

open import Relation.Binary.Definitions

record MaximumFilter {L P : HOD} (LP : L ⊆ Power P) (F : Filter {L} {P} LP) : Set (suc n) where
    field
       mf : Filter {L} {P} LP
       F⊆mf : filter F ⊆ filter mf
       proper  : ¬ (filter mf ∋ od∅)
       is-maximum : ( f : Filter {L} {P} LP ) →  ¬ (filter f ∋ od∅)  → filter F ⊆ filter f →  ¬ ( filter mf  ⊂ filter f  )

record Fp {L P : HOD} (LP : L ⊆ Power P)  (F : Filter {L} {P} LP) (mx : MaximumFilter {L} {P} LP F ) (p x : Ordinal ) : Set n where
    field 
       y : Ordinal 
       mfy : odef (filter (MaximumFilter.mf mx)) y
       y-p⊂x : ( * y ＼ * p ) ⊆ * x

max→ultra : {L P : HOD} (LP : L ⊆ Power P) 
       → ({p q : HOD} → L ∋ p → L ∋ q → L ∋ (p ∩ q))
       → (F0 : Filter {L} {P} LP) → {y : Ordinal } → odef (filter F0) y 
       → (mx : MaximumFilter {L} {P} LP F0 ) → ultra-filter ( MaximumFilter.mf mx )
max→ultra {L} {P} LP CAP F0 {y} mfy mx = record { proper = MaximumFilter.proper mx ; ultra = ultra } where
    mf = MaximumFilter.mf mx
    ultra : {p : HOD} → L ∋ p → L ∋ (P ＼ p) → (filter mf ∋ p) ∨ (filter mf ∋ (P ＼ p))
    ultra {p} Lp Lnp with ODC.∋-p (filter mf) p 
    ... | yes0 y = case1 y
    ... | no0 np = case2 (eq→ F=mf F∋P-p ) where  
         F : HOD  
         F = record { od = record { def = λ x →  odef L x ∧ Fp {L} {P} LP F0 mx (& p) x } 
            ; odmax = & L ; <odmax = λ lt → odef< (proj1 lt) } 
         mu01 :  {r : HOD} {q : HOD} → L ∋ q → F ∋ r → r ⊆ q → F ∋ q
         mu01 {r} {q} Lq ⟪ Lr , record { y = y ; mfy = mfy ; y-p⊂x = y-p⊂x } ⟫ r⊆q = ⟪ Lq , record { y = y ; mfy = mfy ; y-p⊂x = mu03 } ⟫ where
            mu05 : (* y ＼ p) ⊆ r
            mu05 ⟪ yx , ¬px ⟫  =  eq→  *iso (y-p⊂x ⟪ yx , (λ np → ¬px (eq→  *iso np ) ) ⟫ ) 
            mu04 :  (* y ＼ * (& p)) ⊆ * (& q)
            mu04 {x} ⟪ yx , npx ⟫ = eq← *iso (r⊆q (mu05 ⟪ yx , (λ px1 → npx (eq← *iso px1 )) ⟫ ) )
            mu03 :  (* y ＼ * (& p)) ⊆ * (& q)
            mu03 = mu04 
         mu02 : {r : HOD} {q : HOD} → F ∋ r → F ∋ q → L ∋ (r ∩ q) → F ∋ (r ∩ q)
         mu02 {r} {q} ⟪ Lr , record { y = ry ; mfy = mfry ; y-p⊂x = ry-p⊂x } ⟫ 
          ⟪ Lq , record { y = qy ; mfy = mfqy ; y-p⊂x = qy-p⊂x } ⟫  Lrq = ⟪ Lrq , record { y = & (* qy  ∩ * ry) ; mfy = mu20 ; y-p⊂x = mu22 } ⟫ where
            mu21 : L ∋ (* qy ∩ * ry)
            mu21 = CAP (subst (λ k → odef L k ) (sym &iso) (f⊆L mf mfqy)) (subst (λ k → odef L k ) (sym &iso) (f⊆L mf mfry)) 
            mu20 : odef (filter mf) (& (* qy ∩ * ry))
            mu20 = filter2 mf (subst (λ k → odef (filter mf) k) (sym &iso) mfqy) (subst (λ k → odef (filter mf) k) (sym &iso) mfry)  mu21
            mu24 : ((* qy ∩ * ry) ＼ * (& p)) ⊆ (r ∩ q)
            mu24 {x} ⟪ qry , npx ⟫ = ⟪ eq→ *iso ( ry-p⊂x ⟪ proj2 qry , npx ⟫ ) , eq→ *iso ( qy-p⊂x ⟪ proj1 qry , npx ⟫ ) ⟫
            mu22 : (* (& (* qy ∩ * ry)) ＼ * (& p)) ⊆ * (& (r ∩ q))
            mu22 {x} ⟪ qry , px ⟫ = eq← *iso ( mu24 ⟪ eq→ *iso qry  , px ⟫ )
         FisFilter : Filter {L} {P} LP
         FisFilter = record { filter = F ; f⊆L = λ {x} lt → proj1 lt  ; filter1 = mu01 ; filter2 = mu02 }
         FisGreater : {x : Ordinal } → odef (filter (MaximumFilter.mf mx))  x → odef (filter FisFilter ) x
         FisGreater {x} mfx = ⟪ f⊆L mf mfx , record { y = x ; mfy = mfx ; y-p⊂x = mu03 }  ⟫ where
             mu03 : (* x ＼ * (& p)) ⊆ * x
             mu03 {z} ⟪ xz , _ ⟫ = xz
         F∋P-p : F ∋ (P ＼ p )
         F∋P-p = ⟪ Lnp , record { y = y ; mfy = mxy ; y-p⊂x = mu30 }  ⟫  where
             mxy : odef (filter (MaximumFilter.mf mx)) y
             mxy = MaximumFilter.F⊆mf mx mfy
             mu30 : (* y ＼ * (& p)) ⊆ * (& (P ＼ p))
             mu30 {z} ⟪ yz , ¬pz ⟫ = eq← *iso ⟪ Pz , ( λ pz → ¬pz ( eq← *iso pz ))  ⟫  where
                 Pz : odef P z
                 Pz = LP (f⊆L mf mxy ) _ yz
         FisProper : ¬ (filter FisFilter ∋ od∅)    -- if F contains p, p is in mf which contract np
         FisProper ⟪ L0 , record { y = z ; mfy = mfz ; y-p⊂x = z-p⊂x } ⟫ = 
           ⊥-elim ( np (filter1 mf Lp (subst (λ k → odef (filter mf) k) (sym &iso) mfz) mu31) ) where
             mu31 : * z ⊆ p
             mu31 {x} zx with ODC.decp (odef p x)
             ... | yes0 px = px
             ... | no0 npx = ⊥-elim ( ¬x<0 ( eq→  *iso (z-p⊂x ⟪ zx , (λ px → npx ( eq→  *iso px) ) ⟫ ) ) )
         F0⊆F : filter F0 ⊆ F
         F0⊆F {x} fx = ⟪ f⊆L F0 fx , record { y = _ ; mfy = MaximumFilter.F⊆mf mx fx ; y-p⊂x = mu42 } ⟫ where
             mu42 : (* x ＼ * (& p)) ⊆ * x
             mu42 {z} ⟪ xz , ¬p ⟫ = xz
         F=mf : F =h= filter mf
         F=mf with osuc-≡< ( ⊆→o≤ FisGreater )
         ... | case1 eq = ord→== (sym eq) 
         ... | case2 lt = ⊥-elim ( MaximumFilter.is-maximum mx FisFilter FisProper F0⊆F ⟪ lt , FisGreater ⟫ )


ultra→max : {L P : HOD} (LP : L ⊆ Power P) → ({p : HOD} 
       → L ∋ p → L ∋ ( P ＼ p)) 
       → ({p q : HOD} → L ∋ p → L ∋ q → L ∋ (p ∩ q))
       → (U : Filter {L} {P} LP) → ultra-filter U → MaximumFilter LP U
ultra→max {L} {P} LP NEG CAP U u  = record { mf = U ; F⊆mf = λ x → x ; proper = ultra-filter.proper u ; is-maximum = is-maximum } where 
  is-maximum : (F : Filter {L} {P} LP) → (¬ (filter F ∋ od∅)) → filter U ⊆ filter F  → (U⊂F : filter U  ⊂ filter F ) → ⊥
  is-maximum F Prop F⊆U ⟪ U<F , U⊆F ⟫   = Prop f0 where
     GT : HOD
     GT = record { od = record { def = λ x → odef (filter F) x ∧ (¬ odef (filter U) x) } ; odmax = & L ; <odmax = um02 } where
         um02 : {y : Ordinal } → odef (filter F) y ∧ (¬ odef (filter U) y) → y o< & L
         um02 {y} Fy = odef< ( f⊆L F (proj1 Fy ) )
     GT≠∅ :  ¬ (GT =h= od∅)
     GT≠∅ eq = ⊥-elim (U≠F ( ==→o≡ ((⊆→= {filter U} {filter F}) U⊆F  gt02 )   ) ) where
        U≠F : ¬ ( & (filter U) ≡ & (filter F ))
        U≠F eq  = o<¬≡ eq U<F
        gt01 : (x : Ordinal) → ¬ ( odef (filter F) x ∧ (¬ odef (filter U) x))
        gt01 x not = ¬x<0 ( eq→ eq not )
        gt02 : filter F ⊆ filter U
        gt02 {x} fx = U-F=∅→F⊆U {filter U} {filter F} {filter U} (λ x → x) gt01 fx
     p : HOD
     p = minimal GT GT≠∅
     ¬U∋p : ¬ ( filter U ∋ p )
     ¬U∋p = proj2 (x∋minimal GT GT≠∅)
     L∋p : L ∋  p
     L∋p = f⊆L F ( proj1 (x∋minimal GT GT≠∅))
     um00 : ¬ odef (filter U) (& p)
     um00 = proj2 (x∋minimal GT GT≠∅)
     L∋-p : L ∋  ( P ＼ p )
     L∋-p = NEG L∋p
     U∋-p : filter U ∋  ( P ＼ p )
     U∋-p with ultra-filter.ultra u {p} L∋p L∋-p
     ... | case1 ux = ⊥-elim ( ¬U∋p ux )
     ... | case2 u-x = u-x
     F∋p : filter F ∋ p
     F∋p = proj1 (x∋minimal GT GT≠∅)
     F∋-p : filter F ∋ ( P ＼ p )
     F∋-p = U⊆F U∋-p 
     f0 : filter F ∋ od∅
     f0 = subst (λ k → odef (filter F) k ) (==→o≡ ff0 ) ( filter2 F F∋p F∋-p ( CAP L∋p L∋-p) ) where
         ff0 : (p ∩ (P ＼ p)) =h= od∅
         ff0 = record { eq→ = λ {x} lt → ⊥-elim (proj2 (proj2 lt ) (proj1 lt)) 
                     ;  eq← = λ {x} lt → ⊥-elim ( ¬∅∋ (subst (λ k → odef od∅ k) (sym &iso) lt )) }

--  if there is a filter , there is a ultra filter under the axiom of choise
--        Zorn Lemma

record IsFilter { L P : HOD  } (LP : L ⊆ Power P) (filter : Ordinal ) : Set n where
   field
       f⊆L     : (* filter) ⊆ L
       filter1 : { p q : Ordinal } → odef L q → odef (* filter) p →  (* p) ⊆ (* q)  → odef (* filter) q
       filter2 : { p q : Ordinal } → odef (* filter)  p →  odef (* filter) q  → odef L (& ((* p) ∩ (* q))) → odef (* filter) (& ((* p) ∩ (* q)))
       proper : ¬ (odef (* filter ) o∅)

Filter-is-Filter : { L P : HOD  } (LP : L ⊆ Power P) → (F : Filter {L} {P} LP) → (proper : ¬ (filter F) ∋ od∅ ) → IsFilter {L} {P} LP (& (filter F))
Filter-is-Filter {L} {P} LP F proper = record { 
       f⊆L     = λ {x} lt →  f⊆L F (eq→  *iso  lt ) 
     ; filter1 = λ {p} {q} Lq Fp p⊆q → eq←  *iso (subst (λ k → odef (filter F) k )  &iso 
         (filter1 F (subst (λ k → odef L k) (sym &iso) Lq) (subst (λ k → odef (filter F) k) (sym &iso) (eq→ *iso Fp ) ) p⊆q ))
     ; filter2 = λ {p} {q} Fp Fq Lpq → eq← *iso (filter2 F 
         (subst (λ k → odef (filter F) k) (sym &iso) (eq→ *iso Fp )) 
         (subst (λ k → odef (filter F) k) (sym &iso) (eq→ *iso Fq )) 
         Lpq )
     ; proper  = λ lt → proper (eq→ *iso (subst (λ k → odef (* (& (filter F))) k) (sym ord-od∅) lt )) 
   }  
