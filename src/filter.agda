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

