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
import BAlgbra 

open BAlgbra O

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

-- Kunen p.76 and p.53, we use ⊆
record Filter  { L P : HOD  } (LP : L ⊆ Power P) : Set (suc n) where
   field
       filter  : HOD   
       f⊆L     : filter ⊆ L
       filter1 : { p q : HOD } →  L ∋ q → filter ∋ p →  p ⊆ q  → filter ∋ q
       filter2 : { p q : HOD } → filter ∋ p →  filter ∋ q  → L ∋ (p ∩ q) → filter ∋ (p ∩ q)

open Filter

record prime-filter { L P : HOD } {LP : L ⊆ Power P} (F : Filter LP) : Set (suc (suc n)) where
   field
       proper  : ¬ (filter F ∋ od∅)
       prime   : {p q : HOD } → L ∋ p → L ∋ q  → L ∋ (p ∪ q) →  filter F ∋ (p ∪ q) → ( filter F ∋ p ) ∨ ( filter F ∋ q )

record ultra-filter { L P : HOD } {LP : L ⊆ Power P} (F : Filter LP) : Set (suc (suc n)) where
   field
       proper  : ¬ (filter F ∋ od∅)
       ultra   : {p : HOD } → L ∋ p → L ∋  ( P ＼ p) → ( filter F ∋ p ) ∨ (  filter F ∋ ( P ＼ p) )

open _⊆_

∈-filter : {L P p : HOD} →  {LP : L ⊆ Power P}  → (F : Filter LP ) → filter F ∋ p → L ∋ p 
∈-filter {L} {p} {LP} F lt = incl ( f⊆L F) lt 

⊆-filter : {L P p q : HOD } →  {LP : L ⊆ Power P } → (F : Filter LP) →  L ∋ q → q ⊆ P
⊆-filter {L} {P} {p} {q} {LP} F lt = power→⊆ P q ( incl LP lt )

∪-lemma1 : {L p q : HOD } → (p ∪ q)  ⊆ L → p ⊆ L
∪-lemma1 {L} {p} {q} lt = record { incl = λ {x} p∋x → incl lt (case1 p∋x) }

∪-lemma2 : {L p q : HOD } → (p ∪ q)  ⊆ L → q ⊆ L
∪-lemma2 {L} {p} {q} lt = record { incl = λ {x} p∋x → incl lt (case2 p∋x) }

q∩q⊆q : {p q : HOD } → (q ∩ p) ⊆ q 
q∩q⊆q = record { incl = λ lt → proj1 lt } 

open HOD

-----
--
--  ultra filter is prime
--

filter-lemma1 :  {P L : HOD} → (LP : L ⊆ Power P)
     → ({p : HOD} → L ∋ p → L ∋ (P ＼ p))
     → ({p q : HOD} → L ∋ p → L ∋ q → L ∋ (p ∩ q ))
     → (F : Filter LP) → ultra-filter F  → prime-filter F 
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
    lemma8 = q∩q⊆q

-----
--
--  if Filter contains L, prime filter is ultra
--

filter-lemma2 :  {P L : HOD} → (LP : L ⊆ Power P)
       → ({p : HOD} → L ∋ p → L ∋ ( P ＼ p))
       → (F : Filter LP)  → filter F ∋ P → prime-filter F → ultra-filter F
filter-lemma2 {P} {L} LP Lm F f∋P prime = record {
         proper = prime-filter.proper prime
       ; ultra = λ {p}  L∋p _ → prime-filter.prime prime L∋p (Lm  L∋p) (lemma10 L∋p (incl (f⊆L F) f∋P) ) (lemma p (p⊆L  L∋p ))  
   } where
        open _==_
        p⊆L : {p : HOD} → L ∋ p  → p ⊆ P
        p⊆L {p} lt = power→⊆ P p ( incl LP lt )
        p+1-p=1 : {p : HOD} → p ⊆ P  → P =h= (p ∪ (P ＼ p)) 
        eq→ (p+1-p=1 {p} p⊆P) {x} lt with ODC.decp O (odef p x)
        eq→ (p+1-p=1 {p} p⊆P) {x} lt | yes p∋x = case1 p∋x
        eq→ (p+1-p=1 {p} p⊆P) {x} lt | no ¬p = case2 ⟪ lt , ¬p ⟫
        eq← (p+1-p=1 {p} p⊆P) {x} ( case1 p∋x ) = subst (λ k → odef P k ) &iso (incl p⊆P ( subst (λ k → odef p k) (sym &iso) p∋x  )) 
        eq← (p+1-p=1 {p} p⊆P) {x} ( case2 ¬p  ) = proj1 ¬p
        lemma : (p : HOD) → p ⊆ P   →  filter F ∋ (p ∪ (P ＼ p))
        lemma p p⊆P = subst (λ k → filter F ∋ k ) (==→o≡ (p+1-p=1 {p} p⊆P)) f∋P 
        lemma10 : {p : HOD} → L ∋ p → L ∋ P → L ∋ (p ∪ (P ＼ p))
        lemma10 {p} L∋p lt = subst (λ k → L ∋ k ) (==→o≡ (p+1-p=1 {p} (p⊆L L∋p))) lt

-----
--
--  if there is a filter , there is a ultra filter under the axiom of choise
--        Zorn Lemma

-- filter→ultra :  {P L : HOD} → (LP : L ⊆ Power P) → ({p : HOD} → L ∋ p → L ∋ ( P ＼ p)) → (F : Filter LP)  → ultra-filter F
-- filter→ultra {P} {L} LP Lm F = {!!}

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

proper-ideal : {L P : HOD} → (LP : L ⊆ Power P) → (P : Ideal LP ) → {p : HOD} → Set n
proper-ideal {L} {P} LP I = ideal I ∋ od∅

prime-ideal : {L P : HOD} → (LP : L ⊆ Power P) → Ideal LP → ∀ {p q : HOD } → Set n
prime-ideal {L} {P} LP I {p} {q} =  ideal I ∋ ( p ∩ q) → ( ideal I ∋ p ) ∨ ( ideal I ∋ q )


record GenericFilter {L P : HOD} (LP : L ⊆ Power P) (M : HOD) : Set (suc n) where
    field
       genf : Filter LP
       generic : (D : Dense LP ) → M ∋ Dense.dense D → ¬ ( (Dense.dense D ∩ Filter.filter genf ) ≡ od∅ )

record MaximumFilter {L P : HOD} (LP : L ⊆ Power P) : Set (suc n) where
    field
       mf : Filter LP
       proper  : ¬ (filter mf ∋ od∅)
       is-maximum : ( f : Filter LP ) →  ¬ (filter f ∋ od∅)  →  ¬ filter  mf ≡ filter f → ¬ ( filter mf  ⊆ filter f  )

max→ultra : {L P : HOD} (LP : L ⊆ Power P) → (mx : MaximumFilter LP ) → ultra-filter ( MaximumFilter.mf mx )
max→ultra {L} {P} LP mx = record { proper = MaximumFilter.proper mx ; ultra = ultra } where
    mf = MaximumFilter.mf mx
    ultra : {p : HOD} → L ∋ p → L ∋ (P ＼ p) → (filter mf ∋ p) ∨ (filter mf ∋ (P ＼ p))
    ultra {p} lp lnp with ∋-p (filter mf) p
    ... | yes y = case1 y
    ... | no np with ∋-p (filter mf) (P ＼ p) 
    ... | yes y = case2 y
    ... | no n-p = ⊥-elim (MaximumFilter.is-maximum mx FisFilter FisProper  {!!}  record { incl = FisGreater } ) where
         Y : (y : Ordinal) → (my : odef (filter mf) y ) → HOD
         Y y my = record { od = record { def = λ x → (x ≡ y) ∨ (x ≡ & p) } ; odmax = & L ; <odmax = {!!} }
         F : HOD
         F = record { od = record { def = λ x → (x ≡ & p) ∨ ((y : Ordinal) → (my : odef (filter mf) y ) → x ≡ & (Y y my) )  } ; odmax = & L ; <odmax = {!!} }
         FisFilter : Filter LP
         FisFilter = record { filter = F ; f⊆L = {!!} ; filter1 = {!!} ; filter2 = {!!} }
         FisGreater : {x : HOD} → filter (MaximumFilter.mf mx) ∋ x → filter FisFilter ∋ x
         FisGreater = {!!}
         FisProper : ¬ (filter FisFilter ∋ od∅)
         FisProper = {!!}

open _==_

open import Relation.Binary.Definitions

ultra→max : {L P : HOD} (LP : L ⊆ Power P) → ({p : HOD} → L ∋ p → L ∋ ( P ＼ p)) → ({p q : HOD} → L ∋ p → L ∋ q → L ∋ (p ∩ q))
       → (U : Filter LP) → ultra-filter U → MaximumFilter LP 
ultra→max {L} {P} LP NG CAP U u  = record { mf = U ; proper = ultra-filter.proper u ; is-maximum = is-maximum } where
  is-maximum : (F : Filter LP) → (¬ (filter F ∋ od∅)) → ( U≠F :  ¬ filter  U ≡ filter F ) →  (U⊆F : filter U  ⊆ filter F ) → ⊥
  is-maximum F Prop U≠F U⊆F  = Prop f0 where
     GT : HOD
     GT = record { od = record { def = λ x → odef (filter F) x ∧ (¬ odef (filter U) x) } ; odmax = {!!} ; <odmax = {!!} }
     GT≠∅ :  ¬ (GT =h= od∅)
     GT≠∅ eq = ⊥-elim (U≠F ( ==→o≡ (⊆→=  U⊆F (U-F=∅→F⊆U gt01)))) where
         gt01 : (x : Ordinal) → ¬ odef (filter F) x ∧ (¬ odef (filter U) x)
         gt01 x not = ¬x<0 ( eq→ eq not )
     p : HOD
     p = ODC.minimal O GT GT≠∅
     ¬U∋p : ¬ ( filter U ∋ p )
     ¬U∋p = proj2 (ODC.x∋minimal O GT GT≠∅)
     U∋-p : filter U ∋  ( P ＼ p )
     U∋-p with ultra-filter.ultra u {p} {!!} {!!}
     ... | case1 ux = ⊥-elim ( ¬U∋p ux )
     ... | case2 u-x = u-x
     F∋p : filter F ∋ p
     F∋p = proj1 (ODC.x∋minimal O GT GT≠∅)
     F∋-p : filter F ∋ ( P ＼ p )
     F∋-p = incl U⊆F U∋-p 
     f0 : filter F ∋ od∅
     f0 = subst (λ k → odef (filter F) k ) (trans (cong (&) ∩-comm) (cong (&) [a-b]∩b=0 ) ) ( filter2 F F∋p F∋-p ( CAP {!!} {!!}) )

_⊆'_ : ( A B : HOD ) → Set n
_⊆'_ A B = (x : Ordinal ) → odef A x → odef B x

import zorn 
open zorn O _⊆'_

MaximumSubset : {L P : HOD} 
      → o∅ o< & L →  o∅ o< & P → P ⊆ L
      → IsPartialOrderSet P 
      → ( (B : HOD) → B ⊆ P → IsTotalOrderSet B  → SUP P B  )
      → Maximal P 
MaximumSubset {L} {P} 0<L 0<P P⊆L PO SP  = Zorn-lemma 0<P PO SP

MaximumFilterExist : {L P : HOD} (LP : L ⊆ Power P) → ({p : HOD} → L ∋ p → L ∋ ( P ＼ p)) → ({p q : HOD} → L ∋ p → L ∋ q → L ∋ (p ∩ q))
      → (F : Filter LP) → o∅ o< & L →  o∅ o< & (filter F)  →  (¬ (filter F ∋ od∅)) → MaximumFilter LP 
MaximumFilterExist {L} {P} LP NEG CAP F 0<L 0<F Fprop = record { mf = {!!} ; proper = {!!} ; is-maximum = {!!} }  where
     mf01 : Maximal  P 
     mf01 = MaximumSubset  0<L {!!}  {!!} {!!} {!!} 


