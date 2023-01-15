{-# OPTIONS --allow-unsolved-metas #-} 

open import Level
open import Ordinals
module filter {n : Level } (O : Ordinals {n})   where

open import zf
open import logic
import OD 

open import Relation.Nullary 
open import Data.Empty 
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality
import BAlgebra 

open BAlgebra O

open inOrdinal O
open OD O
open OD.OD
open ODAxiom odAxiom

import OrdUtil
import ODUtil
open Ordinals.Ordinals  O
open Ordinals.IsOrdinals isOrdinal
open Ordinals.IsNext isNext
open OrdUtil O
open ODUtil O


import ODC
open ODC O

open _∧_
open _∨_
open Bool

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
       prime   : {p q : HOD } → L ∋ p → L ∋ q  → L ∋ (p ∪ q) →  filter F ∋ (p ∪ q) → ( filter F ∋ p ) ∨ ( filter F ∋ q )

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

∩→≡1 : {p q : HOD } → p ⊆ q → (q ∩ p) ≡ p
∩→≡1 {p} {q} p⊆q =  ==→o≡ record { eq→ = c00 ; eq← = c01 } where
    c00 : {x : Ordinal} → odef (q ∩ p) x → odef p x
    c00 {x} qpx = proj2 qpx
    c01 : {x : Ordinal} → odef p x → odef (q ∩ p) x 
    c01 {x} px = ⟪ p⊆q px , px  ⟫

∩→≡2 : {p q : HOD } → q ⊆ p → (q ∩ p) ≡ q
∩→≡2 {p} {q} q⊆p =  ==→o≡ record { eq→ = c00 ; eq← = c01 } where
    c00 : {x : Ordinal} → odef (q ∩ p) x → odef q x
    c00 {x} qpx = proj1 qpx
    c01 : {x : Ordinal} → odef q x → odef (q ∩ p) x 
    c01 {x} qx = ⟪ qx , q⊆p qx  ⟫

open HOD

-----
--
--  ultra filter is prime
--

filter-lemma1 :  {P L : HOD} → (LP : L ⊆ Power P)
     → ({p : HOD} → L ∋ p → L ∋ (P ＼ p))
     → ({p q : HOD} → L ∋ p → L ∋ q → L ∋ (p ∩ q ))
     → (F : Filter {L} {P} LP) → ultra-filter F  → prime-filter F 
filter-lemma1 {P} {L} LP NG IN F u = record {
         proper = ultra-filter.proper u
       ; prime = lemma3
    } where
  lemma3 : {p q : HOD} → L ∋ p → L ∋ q  → L ∋ (p ∪ q) → filter F ∋ (p ∪ q) → ( filter F ∋ p ) ∨ ( filter F ∋ q )
  lemma3 {p} {q} Lp Lq _ lt with ultra-filter.ultra u Lp (NG Lp)
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
    lemma9 = subst (λ k → L ∋ k ) (sym (==→o≡ lemma5)) (IN Lq (NG Lp))
    lemma6 : filter F ∋ ((p ∪ q ) ∩ (P ＼ p))
    lemma6 = filter2 F lt ¬p∈P  lemma9
    lemma7 : filter F ∋ (q ∩ (P ＼ p))
    lemma7 =  subst (λ k → filter F ∋ k ) (==→o≡ lemma5 ) lemma6
    lemma8 : (q ∩ (P ＼ p)) ⊆ q
    lemma8 lt = proj1 lt

-----
--
--  if Filter {L} {P} contains L, prime filter is ultra
--

filter-lemma2 :  {P L : HOD} → (LP : L ⊆ Power P)
       → ({p : HOD} → L ∋ p → L ∋ ( P ＼ p))
       → (F : Filter {L} {P} LP)  → filter F ∋ P → prime-filter F → ultra-filter F
filter-lemma2 {P} {L} LP Lm F f∋P prime = record {
         proper = prime-filter.proper prime
       ; ultra = λ {p}  L∋p _ → prime-filter.prime prime L∋p (Lm  L∋p) (lemma10 L∋p ((f⊆L F) f∋P) ) (lemma p (p⊆L  L∋p ))  
   } where
        open _==_
        p⊆L : {p : HOD} → L ∋ p  → p ⊆ P
        p⊆L {p} lt = power→⊆ P p ( LP lt )
        p+1-p=1 : {p : HOD} → p ⊆ P  → P =h= (p ∪ (P ＼ p)) 
        eq→ (p+1-p=1 {p} p⊆P) {x} lt with ODC.decp O (odef p x)
        eq→ (p+1-p=1 {p} p⊆P) {x} lt | yes p∋x = case1 p∋x
        eq→ (p+1-p=1 {p} p⊆P) {x} lt | no ¬p = case2 ⟪ lt , ¬p ⟫
        eq← (p+1-p=1 {p} p⊆P) {x} ( case1 p∋x ) = subst (λ k → odef P k ) &iso (p⊆P ( subst (λ k → odef p k) (sym &iso) p∋x  )) 
        eq← (p+1-p=1 {p} p⊆P) {x} ( case2 ¬p  ) = proj1 ¬p
        lemma : (p : HOD) → p ⊆ P   →  filter F ∋ (p ∪ (P ＼ p))
        lemma p p⊆P = subst (λ k → filter F ∋ k ) (==→o≡ (p+1-p=1 {p} p⊆P)) f∋P 
        lemma10 : {p : HOD} → L ∋ p → L ∋ P → L ∋ (p ∪ (P ＼ p))
        lemma10 {p} L∋p lt = subst (λ k → L ∋ k ) (==→o≡ (p+1-p=1 {p} (p⊆L L∋p))) lt

record Dense  {L P : HOD } (LP : L ⊆ Power P)  : Set (suc n) where
   field
       dense : HOD
       d⊆P :  dense ⊆ L
       dense-f : {p : HOD} → L ∋ p  → HOD
       dense-d :  { p : HOD} → (lt : L ∋ p) → dense ∋ dense-f lt
       dense-p :  { p : HOD} → (lt : L ∋ p) → (dense-f lt) ⊆ p  

record Ideal   {L P : HOD } (LP : L ⊆ Power P) : Set (suc n) where
   field
       ideal : HOD   
       i⊆L :  ideal ⊆ L 
       ideal1 : { p q : HOD } →  L ∋ q  → ideal ∋ p →  q ⊆ p  → ideal ∋ q
       ideal2 : { p q : HOD } → ideal ∋ p →  ideal ∋ q  → ideal ∋ (p ∪ q)

open Ideal

proper-ideal : {L P : HOD} → (LP : L ⊆ Power P) → (P : Ideal {L} {P} LP ) → {p : HOD} → Set n
proper-ideal {L} {P} LP I = ideal I ∋ od∅

prime-ideal : {L P : HOD} → (LP : L ⊆ Power P) → Ideal {L} {P} LP → ∀ {p q : HOD } → Set n
prime-ideal {L} {P} LP I {p} {q} =  ideal I ∋ ( p ∩ q) → ( ideal I ∋ p ) ∨ ( ideal I ∋ q )

open import Relation.Binary.Definitions

record GenericFilter {L P : HOD} (LP : L ⊆ Power P) (M : HOD) : Set (suc n) where
    field
       genf : Filter {L} {P} LP
       generic : (D : Dense {L} {P} LP ) → M ∋ Dense.dense D → ¬ ( (Dense.dense D ∩ Filter.filter genf ) ≡ od∅ )

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
    ultra {p} Lp Lnp with ODC.∋-p O (filter mf) p 
    ... | yes y = case1 y
    ... | no np = case2 (subst (λ k → k ∋ (P ＼ p)) F=mf F∋P-p) where
         F : HOD  
         F = record { od = record { def = λ x →  odef L x ∧ Fp {L} {P} LP F0 mx (& p) x } 
            ; odmax = & L ; <odmax = λ lt → odef< (proj1 lt) } 
         mu01 :  {r : HOD} {q : HOD} → L ∋ q → F ∋ r → r ⊆ q → F ∋ q
         mu01 {r} {q} Lq ⟪ Lr , record { y = y ; mfy = mfy ; y-p⊂x = y-p⊂x } ⟫ r⊆q = ⟪ Lq , record { y = y ; mfy = mfy ; y-p⊂x = mu03 } ⟫ where
            mu05 : (* y ＼ p) ⊆ r
            mu05 = subst₂ (λ j k → (* y ＼ j ) ⊆ k ) *iso *iso y-p⊂x
            mu04 :  (* y ＼ * (& p)) ⊆ * (& q)
            mu04 {x} ⟪ yx , npx ⟫ = subst (λ k → odef k x ) (sym *iso) (r⊆q (mu05 ⟪ yx , (λ px1 → npx (subst (λ k → odef k x) (sym *iso) px1 )) ⟫ )  )
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
            mu24 {x} ⟪ qry , npx ⟫ = ⟪ subst (λ k → odef k x) *iso ( ry-p⊂x ⟪ proj2 qry , npx ⟫ )  
               , subst (λ k → odef k x) *iso ( qy-p⊂x ⟪ proj1 qry , npx ⟫ )   ⟫
            mu23 : ((* qy ∩ * ry) ＼ * (& p) ) ⊆ (r ∩ q)
            mu23 = mu24 
            mu22 : (* (& (* qy ∩ * ry)) ＼ * (& p)) ⊆ * (& (r ∩ q))
            mu22 = subst₂ (λ j k → (j ＼ * (& p)) ⊆ k ) (sym *iso) (sym *iso) mu23
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
             mu30 {z} ⟪ yz , ¬pz ⟫ = subst (λ k → odef k z) (sym *iso) ( ⟪ Pz , (λ pz → ¬pz (subst (λ k → odef k z) (sym *iso) pz ))  ⟫  ) where
                 Pz : odef P z
                 Pz = LP (f⊆L mf mxy ) _ yz
         FisProper : ¬ (filter FisFilter ∋ od∅)    -- if F contains p, p is in mf which contract np
         FisProper ⟪ L0 , record { y = z ; mfy = mfz ; y-p⊂x = z-p⊂x } ⟫ = 
           ⊥-elim ( np (filter1 mf Lp (subst (λ k → odef (filter mf) k) (sym &iso) mfz) mu31) ) where
             mu31 : * z ⊆ p
             mu31 {x} zx with ODC.decp O (odef p x)
             ... | yes px = px
             ... | no npx = ⊥-elim ( ¬x<0 (subst (λ k → odef k x) *iso (z-p⊂x ⟪ zx , (λ px → npx (subst (λ k → odef k x) *iso px) ) ⟫ ) ) )
         F0⊆F : filter F0 ⊆ F
         F0⊆F {x} fx = ⟪ f⊆L F0 fx , record { y = _ ; mfy = MaximumFilter.F⊆mf mx fx ; y-p⊂x = mu42 } ⟫ where
             mu42 : (* x ＼ * (& p)) ⊆ * x
             mu42 {z} ⟪ xz , ¬p ⟫ = xz
         F=mf : F ≡ filter mf
         F=mf with osuc-≡< ( ⊆→o≤ FisGreater )
         ... | case1 eq = &≡&→≡ (sym eq)
         ... | case2 lt = ⊥-elim ( MaximumFilter.is-maximum mx FisFilter FisProper F0⊆F ⟪ lt , FisGreater ⟫ )

open _==_

ultra→max : {L P : HOD} (LP : L ⊆ Power P) → ({p : HOD} 
       → L ∋ p → L ∋ ( P ＼ p)) 
       → ({p q : HOD} → L ∋ p → L ∋ q → L ∋ (p ∩ q))
       → (U : Filter {L} {P} LP) → ultra-filter U → MaximumFilter LP U
ultra→max {L} {P} LP NG CAP U u  = record { mf = U ; F⊆mf = λ x → x ; proper = ultra-filter.proper u ; is-maximum = is-maximum } where 
  is-maximum : (F : Filter {L} {P} LP) → (¬ (filter F ∋ od∅)) → filter U ⊆ filter F  → (U⊂F : filter U  ⊂ filter F ) → ⊥
  is-maximum F Prop F⊆U ⟪ U<F , U⊆F ⟫   = Prop f0 where
     GT : HOD
     GT = record { od = record { def = λ x → odef (filter F) x ∧ (¬ odef (filter U) x) } ; odmax = & L ; <odmax = um02 } where
         um02 : {y : Ordinal } → odef (filter F) y ∧ (¬ odef (filter U) y) → y o< & L
         um02 {y} Fy = odef< ( f⊆L F (proj1 Fy ) )
     GT≠∅ :  ¬ (GT =h= od∅)
     GT≠∅ eq = ⊥-elim (U≠F ( ==→o≡ ((⊆→= {filter U} {filter F}) U⊆F (U-F=∅→F⊆U {filter F} {filter U} gt01)))) where
         U≠F : ¬ ( filter U ≡ filter F )
         U≠F eq = o<¬≡ (cong (&) eq) U<F
         gt01 : (x : Ordinal) → ¬ ( odef (filter F) x ∧ (¬ odef (filter U) x))
         gt01 x not = ¬x<0 ( eq→ eq not )
     p : HOD
     p = ODC.minimal O GT GT≠∅
     ¬U∋p : ¬ ( filter U ∋ p )
     ¬U∋p = proj2 (ODC.x∋minimal O GT GT≠∅)
     L∋p : L ∋  p
     L∋p = f⊆L F ( proj1 (ODC.x∋minimal O GT GT≠∅))
     um00 : ¬ odef (filter U) (& p)
     um00 = proj2 (ODC.x∋minimal O GT GT≠∅)
     L∋-p : L ∋  ( P ＼ p )
     L∋-p = NG L∋p
     U∋-p : filter U ∋  ( P ＼ p )
     U∋-p with ultra-filter.ultra u {p} L∋p L∋-p
     ... | case1 ux = ⊥-elim ( ¬U∋p ux )
     ... | case2 u-x = u-x
     F∋p : filter F ∋ p
     F∋p = proj1 (ODC.x∋minimal O GT GT≠∅)
     F∋-p : filter F ∋ ( P ＼ p )
     F∋-p = U⊆F U∋-p 
     f0 : filter F ∋ od∅
     f0 = subst (λ k → odef (filter F) k ) (trans (cong (&) ∩-comm) (cong (&) [a-b]∩b=0 ) ) ( filter2 F F∋p F∋-p ( CAP L∋p L∋-p) )

--  if there is a filter , there is a ultra filter under the axiom of choise
--        Zorn Lemma

import zorn 

open import Relation.Binary

PO : IsStrictPartialOrder _≡_ _⊂_ 
PO = record { isEquivalence = record { refl = refl ; sym = sym ; trans = trans }
   ; trans = λ {a} {b} {c} → trans-⊂ {a} {b} {c}
   ; irrefl = λ x=y x<y → o<¬≡ (cong (&) x=y) (proj1 x<y)
   ; <-resp-≈ =  record { fst = ( λ {x} {y} {y1} y=y1 xy1 → subst (λ k → x ⊂ k) y=y1 xy1  )
                        ; snd = (λ {x} {x1} {y} x=x1 x1y → subst (λ k → k ⊂ x) x=x1 x1y ) } }

open zorn O _⊂_ PO

open import  Relation.Binary.Structures

record IsFilter { L P : HOD  } (LP : L ⊆ Power P) (filter : Ordinal ) : Set n where
   field
       f⊆L     : (* filter) ⊆ L
       filter1 : { p q : Ordinal } → odef L q → odef (* filter) p →  (* p) ⊆ (* q)  → odef (* filter) q
       filter2 : { p q : Ordinal } → odef (* filter)  p →  odef (* filter) q  → odef L (& ((* p) ∩ (* q))) → odef (* filter) (& ((* p) ∩ (* q)))
       proper : ¬ (odef (* filter ) o∅)

Filter-is-Filter : { L P : HOD  } (LP : L ⊆ Power P) → (F : Filter {L} {P} LP) → (proper : ¬ (filter F) ∋ od∅ ) → IsFilter {L} {P} LP (& (filter F))
Filter-is-Filter {L} {P} LP F proper = record { 
       f⊆L     = subst (λ k → k ⊆ L ) (sym *iso) (f⊆L F)
     ; filter1 = λ {p} {q} Lq Fp p⊆q → subst₂ (λ j k → odef j k ) (sym *iso) &iso 
        ( filter1 F (subst (λ k → odef L k) (sym &iso) Lq) (subst₂ (λ j k → odef j k ) *iso (sym &iso) Fp) p⊆q  )
     ; filter2 = λ {p} {q} Fp Fq Lpq → subst₂ (λ j k → odef j k ) (sym *iso) refl ( filter2 F (subst₂ (λ j k → odef j k ) *iso (sym &iso) Fp)
         (subst₂ (λ j k → odef j k ) *iso (sym &iso) Fq) Lpq )
     ; proper  = subst₂ (λ j k → ¬ odef j k ) (sym *iso) ord-od∅ proper 
   }

-- all filter contains F
F⊆X : { L P : HOD  } (LP : L ⊆ Power P) → Filter {L} {P} LP  → HOD
F⊆X {L} {P} LP F = record { od = record { def = λ x → IsFilter {L} {P} LP x ∧ ( filter F ⊆ * x)  } ; odmax = osuc (& L)
      ; <odmax = λ {x} lt → fx00 lt } where
      fx00 : {x : Ordinal } → IsFilter LP x ∧ filter F ⊆ * x → x o< osuc (& L)
      fx00 {x} lt = subst (λ k → k o< osuc (& L)) &iso ( ⊆→o≤ (IsFilter.f⊆L (proj1 lt ))  )

F→Maximum : {L P : HOD} (LP : L ⊆ Power P) → ({p : HOD} → L ∋ p → L ∋ ( P ＼ p)) → ({p q : HOD} → L ∋ p → L ∋ q → L ∋ (p ∩ q))
      → (F : Filter {L} {P} LP) → o∅ o< & L →  {y : Ordinal } → odef (filter F) y →  (¬ (filter F ∋ od∅)) → MaximumFilter {L} {P} LP F
F→Maximum {L} {P} LP NEG CAP F 0<L {y} 0<F Fprop = record { mf = mf ; F⊆mf = subst (λ k → filter F ⊆ k ) (sym *iso) mf52  
         ; proper = subst (λ k → ¬ ( odef (filter mf ) k)) (sym ord-od∅) ( IsFilter.proper imf)  ; is-maximum = mf50 }  where
      FX : HOD
      FX = F⊆X {L} {P} LP F
      oF = & (filter F)
      mf11 : { p q : Ordinal } → odef L q → odef (* oF) p →  (* p) ⊆ (* q)  → odef (* oF) q
      mf11 {p} {q} Lq Fp p⊆q = subst₂ (λ j k → odef j k ) (sym *iso) &iso ( filter1 F (subst (λ k → odef L k) (sym &iso) Lq) 
             (subst₂ (λ j k → odef j k ) *iso (sym &iso)  Fp) p⊆q )
      mf12 : { p q : Ordinal } → odef (* oF)  p →  odef (* oF) q  → odef L (& ((* p) ∩ (* q))) → odef (* oF) (& ((* p) ∩ (* q)))
      mf12 {p} {q} Fp Fq Lpq = subst (λ k → odef k (& ((* p) ∩ (* q))) ) (sym *iso) 
        ( filter2 F (subst₂ (λ j k → odef j k ) *iso (sym &iso)  Fp) (subst₂ (λ j k → odef j k ) *iso (sym &iso)  Fq) Lpq)
      FX∋F : odef FX (& (filter F))
      FX∋F = ⟪ record { f⊆L = subst (λ k → k ⊆ L) (sym *iso) (f⊆L F) ; filter1 = mf11 ; filter2 = mf12 
        ; proper = subst₂ (λ j k →  ¬ (odef j k) ) (sym *iso) ord-od∅ Fprop  }  
          , subst (λ k → filter F ⊆ k ) (sym *iso) ( λ x → x ) ⟫ 
      -- 
      -- if filter B (which contains F) is transitive, Union B is also a filter which contains F
      --   and this is a SUP
      -- 
      SUP⊆ : (B : HOD) → B ⊆ FX → IsTotalOrderSet B → SUP FX B
      SUP⊆ B B⊆FX OB with trio< (& B) o∅ 
      ... | tri< a ¬b ¬c = ⊥-elim (¬x<0 a )
      ... | tri≈ ¬a b ¬c = record { sup = filter F ; isSUP = record { ax = FX∋F ; x≤sup = λ {y} zy → ⊥-elim (o<¬≡ (sym b) (∈∅< zy))  } } 
      ... | tri> ¬a ¬b 0<B = record { sup = Union B ; isSUP = record { ax = mf13 ; x≤sup = mf40 } } where
          mf20 : HOD
          mf20 = ODC.minimal O B (λ eq → (o<¬≡ (cong (&) (sym (==→o≡ eq))) (subst (λ k → k o< & B) (sym ord-od∅) 0<B )))
          mf18 : odef B (& mf20 )
          mf18 = ODC.x∋minimal O B (λ eq → (o<¬≡ (cong (&) (sym (==→o≡ eq))) (subst (λ k → k o< & B) (sym ord-od∅) 0<B )))
          mf16 : Union B ⊆ L
          mf16 record { owner = b ; ao = Bb ; ox = bx } = IsFilter.f⊆L ( proj1 ( B⊆FX Bb )) bx
          mf17 : {p q : Ordinal} → odef L q → odef (* (& (Union B))) p → * p ⊆ * q → odef (* (& (Union B))) q
          mf17 {p} {q} Lq bp p⊆q with subst (λ k → odef k p ) *iso bp
          ... | record { owner = owner ; ao = ao ; ox = ox } = subst (λ k → odef k q) (sym *iso) 
                record { owner = owner ; ao = ao ; ox = IsFilter.filter1 mf30 Lq ox p⊆q } where
              mf30 : IsFilter {L} {P} LP owner
              mf30 = proj1 ( B⊆FX ao ) 
          mf31 : {p q : Ordinal} → odef (* (& (Union B))) p → odef (* (& (Union B))) q → odef L (& ((* p) ∩ (* q))) → odef (* (& (Union B))) (& ((* p) ∩ (* q)))
          mf31 {p} {q} bp bq Lpq with subst (λ k → odef k p ) *iso bp | subst (λ k → odef k q ) *iso bq
          ... | record { owner = bp ; ao = Bbp ; ox = bbp } | record { owner = bq ; ao = Bbq ; ox = bbq } 
             with OB (subst (λ k → odef B k) (sym &iso) Bbp) (subst (λ k → odef B k) (sym &iso) Bbq)
          ... | tri< bp⊂bq ¬b ¬c = subst₂ (λ j k → odef j k ) (sym  *iso) refl record { owner = bq ; ao = Bbq ; ox = mf36 } where
              mf36 : odef (* bq) (& ((* p) ∩ (* q)))
              mf36 = IsFilter.filter2 mf30 (proj2 bp⊂bq bbp) bbq Lpq where
                  mf30 : IsFilter {L} {P} LP bq
                  mf30 = proj1 ( B⊆FX Bbq ) 
          ... | tri≈ ¬a bq=bp ¬c = subst₂ (λ j k → odef j k ) (sym  *iso) refl record { owner = bp ; ao = Bbp ; ox = mf36 } where
              mf36 : odef (* bp) (& ((* p) ∩ (* q)))
              mf36 = IsFilter.filter2 mf30 bbp (subst (λ k → odef k q) (sym bq=bp) bbq) Lpq where
                  mf30 : IsFilter {L} {P} LP bp
                  mf30 = proj1 ( B⊆FX Bbp ) 
          ... | tri> ¬a ¬b bq⊂bp = subst₂ (λ j k → odef j k ) (sym  *iso) refl record { owner = bp ; ao = Bbp ; ox = mf36 } where
              mf36 : odef (* bp) (& ((* p) ∩ (* q)))
              mf36 = IsFilter.filter2 mf30 bbp (proj2 bq⊂bp bbq) Lpq where
                  mf30 : IsFilter {L} {P} LP bp
                  mf30 = proj1 ( B⊆FX Bbp ) 
          mf32 : ¬ odef (Union B) o∅
          mf32 record { owner = owner ; ao = bo ; ox = o0 } with proj1 ( B⊆FX bo ) 
          ... | record { f⊆L = f⊆L ; filter1 = filter1 ; filter2 = filter2 ; proper = proper } = ⊥-elim ( proper o0 )
          mf14 : IsFilter LP (& (Union B)) 
          mf14 = record { f⊆L = subst (λ k → k ⊆ L) (sym *iso) mf16 ; filter1 = mf17 ; filter2 = mf31 ; proper = subst (λ k → ¬ odef k o∅) (sym *iso) mf32 } 
          mf15 :  filter F ⊆ Union B
          mf15 {x} Fx = record { owner = & mf20 ; ao = mf18 ; ox = subst (λ k → odef k x) (sym *iso) (mf22 Fx) } where
               mf22 : odef (filter F) x → odef mf20 x
               mf22 Fx = subst (λ k → odef k x) *iso ( proj2 (B⊆FX mf18) Fx )
          mf13 : odef FX (& (Union B))
          mf13 = ⟪ mf14  , subst (λ k → filter F ⊆ k ) (sym *iso) mf15  ⟫
          mf42 : {z : Ordinal} → odef B z → * z ⊆  Union B
          mf42 {z} Bz {x} zx = record { owner  = _ ; ao = Bz ; ox = zx }
          mf40 : {z : Ordinal} → odef B z → (z ≡ & (Union B)) ∨ ( * z ⊂ * (& (Union B)) )
          mf40 {z} Bz with B⊆FX Bz
          ... | ⟪ filterz , F⊆z ⟫ with osuc-≡< ( ⊆→o≤ {* z} {Union B} (mf42 Bz) )
          ... | case1 eq = case1 (trans (sym &iso) eq )
          ... | case2 lt = case2 ⟪ subst₂ (λ j k → j o< & k ) refl (sym *iso) lt  , subst (λ  k → * z ⊆ k) (sym *iso)  (mf42 Bz)  ⟫
      mx : Maximal  FX
      mx = Zorn-lemma (∈∅< FX∋F) SUP⊆  
      imf : IsFilter {L} {P} LP (& (Maximal.maximal mx))
      imf = proj1 (Maximal.as mx)
      mf00 : (* (& (Maximal.maximal mx))) ⊆ L
      mf00 = IsFilter.f⊆L imf   
      mf01 : { p q : HOD } →  L ∋ q → (* (& (Maximal.maximal mx))) ∋ p →  p ⊆ q  → (* (& (Maximal.maximal mx))) ∋ q
      mf01 {p} {q} Lq Fq p⊆q = IsFilter.filter1 imf Lq Fq 
              (λ {x} lt → subst (λ k → odef k x) (sym *iso) ( p⊆q (subst (λ k → odef k x) *iso lt ) ))
      mf02 : { p q : HOD } → (* (& (Maximal.maximal mx))) ∋ p → (* (& (Maximal.maximal mx)))  ∋ q  → L ∋ (p ∩ q) 
          → (* (& (Maximal.maximal mx))) ∋ (p ∩ q)
      mf02 {p} {q} Fp Fq Lpq = subst₂ (λ j k → odef (* (& (Maximal.maximal mx))) (& (j ∩ k ))) *iso *iso (
          IsFilter.filter2 imf Fp Fq (subst₂ (λ j k → odef L (& (j ∩ k ))) (sym *iso) (sym *iso) Lpq ))
      mf : Filter {L} {P} LP
      mf = record { filter = * (& (Maximal.maximal mx)) ; f⊆L = mf00  
         ; filter1 = mf01  
         ; filter2 = mf02 }
      mf52 : filter F ⊆ Maximal.maximal mx
      mf52 = subst (λ k → filter F ⊆ k ) *iso (proj2 mf53) where
         mf53 : FX ∋ Maximal.maximal mx 
         mf53 = Maximal.as mx 
      mf50 : (f : Filter LP) → ¬ (filter f ∋ od∅) → filter F ⊆ filter f → ¬ (* (& (zorn.Maximal.maximal mx)) ⊂ filter f)
      mf50 f proper F⊆f = subst (λ k → ¬ ( k ⊂ filter f )) (sym *iso) (Maximal.¬maximal<x mx ⟪ Filter-is-Filter {L} {P} LP f proper  , mf51 ⟫ ) where
         mf51 : filter F ⊆ * (& (filter f))
         mf51 = subst (λ k → filter F ⊆ k ) (sym *iso) F⊆f 

F→ultra : {L P : HOD} (LP : L ⊆ Power P) → (NEG : {p : HOD} → L ∋ p → L ∋ ( P ＼ p)) → (CAP : {p q : HOD} → L ∋ p → L ∋ q → L ∋ (p ∩ q))
      → (F : Filter {L} {P} LP) → (0<L : o∅ o< & L) →  {y : Ordinal} →  (0<F : odef (filter F) y) →  (proper : ¬ (filter F ∋ od∅)) 
      → ultra-filter ( MaximumFilter.mf (F→Maximum {L} {P} LP NEG CAP F 0<L 0<F proper ))
F→ultra {L} {P} LP NEG CAP F 0<L 0<F proper = max→ultra {L} {P} LP CAP F 0<F (F→Maximum {L} {P} LP NEG CAP F 0<L 0<F proper ) 


