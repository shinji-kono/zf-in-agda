{-# OPTIONS --cubical-compatible --safe #-}
open import Level renaming ( suc to Suc ; zero to Zero ; _⊔_ to _n⊔_ )
open import Ordinals
open import logic
open import Relation.Nullary

import HODBase
import OD
open import Relation.Nullary
module Forcing {n : Level } (O : Ordinals {n} ) (HODAxiom : HODBase.ODAxiom O)  (ho< : OD.ODAxiom-ho< O HODAxiom )
       (AC : OD.AxiomOfChoice O HODAxiom ) where

open import  Relation.Binary.PropositionalEquality hiding ( [_] )
open import Relation.Binary.Definitions
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
open import Ordinals

import filter

open import Relation.Nullary
-- open import Relation.Binary hiding ( _⇔_ )
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Data.Nat renaming ( _<_  to _n<_  ; _+_ to _n+_ ; _≤_ to _n≤_ )
open import BoolAlgebra
open import ZProduct O HODAxiom ho<
open import filter O HODAxiom ho< AC

import Relation.Binary.Reasoning.Setoid as EqHOD
open import bijection hiding ( b1 )

-- LDec : (L : HOD) (P : HOD) → P ⊆ L → (x : HOD) → Dec0 (x ∈ P)
-- LDec L P _ x = ∋-p P x

-- open import Data.Nat
open import ZEquiv O HODAxiom ho<

open HODElement
import BAlgebra 

open Bijection

--
-- Original Paper uses Boolean Algebra on a HOD Set
-- but we only have a definition of a filter on HOD Set
-- so we use Boolean Algebra on a subset of L
record HODBooleanAlgebra  (L : HOD) : Set (n Level.⊔ Level.suc n)  where
   field
     LDec : (Q : HOD) → Q ⊆ L → ( x : HOD ) → Dec0 ( x ∈ Q ) 
   open BAlgebra O  HODAxiom ho< L LDec 
   field
     H : HBAR L   -- L's cloen set
   ba : BooleanAlgebra {n} {n} (HODElement (HBAR.OS H))
   ba = HBA L LDec H
   bc : IsCompleteBooleanAlgebra  (HODElement (HBAR.OS H)) (HBA L LDec H)
   bc = HBAC L LDec H
   B : Set n
   B = HODElement (HBAR.OS H)
   OS : HOD
   OS = HBAR.OS H
   OS⊆PL : HBAR.OS H ⊆ Power L
   OS⊆PL = HBAR.OS⊆PL H
   o∩ : { p q : HOD } → OS ∋ p →  OS ∋ q      → OS ∋ (p ∩ q)
   o∩ = HBAR.o∩ H
   o∪ : { P : HOD }  →  P ⊆ OS                → OS ∋ Union P
   o∪ = HBAR.o∪ H
   o- : { p : HOD }  →  OS ∋ p                → OS ∋ ( L ＼ p )
   o- = HBAR.o- H


record CM : Set (Suc (Suc n)) where
  field
      countable : Bijection ℕ (Ordinals.Ordinal O) 

--
-- a_n  = ∧ An (An ≠ ∅ )
--
--

open HODBooleanAlgebra

-- ba0 : {P : HOD} → HODElement (Power P)
-- ba0 {P} = record { elt = ? ; A∋elt = ? }

-- we cannot have a bijection here. Only a part of subset of Boolean Algebra is in our HOD Set.
-- we are working on countable model, so only countable number of set of Power B is in M
--
record AN  (L : HOD) (PB : HODBooleanAlgebra L ) : Set n where
   field
      ip : ℕ → HODElement (Power (BAlgebra.HBAR.OS (H PB) ))
      ip-inject : (i j : ℕ ) → elt (ip i) ≡ elt (ip j ) → i ≡ j 
      ip=0 : elt (ip 0) ≡  o∅ 
   imap : ℕ → HODElement (Power (BAlgebra.HBAR.OS (H PB) ))
   imap i = ip (suc i)
   imap>0 : (i : ℕ) → ¬ ( elt (imap i) ≡ o∅ )
   imap>0 i eq = nat-<≡ (subst (λ k → k n≤ i) (ip-inject _ _ (trans ip=0 (sym eq)) ) z≤n )
   imap-ne : (i : ℕ) → od (* (elt (imap i))) == od od∅ → ⊥
   imap-ne i eq = imap>0 i (trans (sym &iso) (trans (==→o≡  eq) ord-od∅)  )

record OAn (L : HOD) (PB : HODBooleanAlgebra L ) (an : AN L PB) (oa : Ordinal) : Set n where
   field 
     i : ℕ 
     peq : oa ≡ elt (AN.imap an i)
   pa : odef (Power (BAlgebra.HBAR.OS (H PB))) oa
   pa = subst (λ k → odef (Power (BAlgebra.HBAR.OS (H PB))) k) (sym peq) ( A∋elt (AN.imap an i) )
     -- pan : BPred.pred (PAn L PB an i) record { elt = oa ; A∋elt = pa }
   poa : {x : Ordinal} → odef (* oa) x → odef (BAlgebra.HBAR.OS (H PB)) x
   poa {x} lt = pa _ lt 
   a : {x : Ordinal} → odef (* oa) x → HODBooleanAlgebra.B PB
   a {x} lt = record { elt = x ; A∋elt = poa lt }

-- { A ∈  M : ∅ ≠ A ⊆ B } = { A0 , A1, A2, ... An }
-- 
An : (L : HOD) → (PB : HODBooleanAlgebra L ) → AN L PB → HOD
An L PB an = record { od = record { def = λ x → OAn L PB an x } ; odmax = & (Power (BAlgebra.HBAR.OS (H PB))) ; <odmax = λ lt → odef< (OAn.pa lt) }

PAn : (L : HOD) → (PB : HODBooleanAlgebra L ) → AN L PB → ℕ → BPred (HODBooleanAlgebra.B PB) (ba PB)
PAn L PB an i = record { pred = λ p → odef (* (elt (AN.imap an i))) (elt p) 
   ; pcong = λ x y eq → ⟪ ( λ lt → subst (λ k → odef (* (elt (AN.imap an i))) k ) (*=h=*→≡ eq) lt ) 
      , ( λ lt → subst (λ k → odef (* (elt (AN.imap an i))) k ) (sym (*=h=*→≡ eq))  lt )  ⟫ }

-- ∧ an
∧An : (L : HOD) → (PB : HODBooleanAlgebra L ) → AN L PB → ℕ → B PB
∧An L PB an i = IsCompleteBooleanAlgebra.sup ( bc PB ) (PAn L PB an i)

record AAn (L : HOD) (PB : HODBooleanAlgebra L )  (bi : HODBooleanAlgebra.B PB) (an : AN L PB) : Set n where
   open BooleanAlgebra (ba PB)
   open IsBooleanAlgebra (BooleanAlgebra.isBooleanAlgebra (ba PB))
   field
     oan oa : Ordinal
     pan : odef (An L PB an) oan
     pa : odef (* oan) oa
   a : B PB 
   a = record { elt = oa ; A∋elt = OAn.poa pan pa }
   field
     eq1 :  b0 < ( bi x ( - a )) 

import Relation.Binary.Reasoning.Setoid as EqR


record Bni (L : HOD)  (PB : HODBooleanAlgebra L ) (an : AN L PB )  : Set n where
   open BooleanAlgebra (ba PB)
   open IsBooleanAlgebra (BooleanAlgebra.isBooleanAlgebra (ba PB))
   field
      b : HODBooleanAlgebra.B PB
      bnz : b0 < b
      -- abn : b0 < ( b + ( - (∧An L PB an i ) ) ) → AAn L PB b an 
   ai-is-sup : (y : B PB) → (i : ℕ) → (ay : odef (* (elt (AN.imap an i))) (elt y)) → y ≤ ∧An L PB an i 
   ai-is-sup y i ay = IsCompleteBooleanAlgebra.is-sup ( bc PB ) (PAn L PB an i) y  ay
   yy1 : (i : ℕ) → HOD
   yy1 i = minimal (* (elt (AN.imap an i))) (AN.imap-ne an i)
   ayy1 : (i : ℕ) → odef (* (elt (AN.imap an i))) (& (yy1 i))
   ayy1 i = x∋minimal (* (elt (AN.imap an i))) (AN.imap-ne an i)
   aion :  (i : ℕ) →  OAn L PB an (elt (AN.imap an i))
   aion i = record { i = i ; peq = refl } 
   pbb : odef (OS PB) (elt b) 
   pbb = A∋elt b
   yy0 : (i : ℕ) → HODBooleanAlgebra.B PB
   yy0 i = record { elt = & (yy1 i) ; A∋elt = A∋elt (AN.imap an i) _ (ayy1 i) }
   ai→a1 :  (i : ℕ) (yy :  (b x ( ∧An L PB an i )) ≈ b0) → AAn L PB b an 
   ai→a1 i yy = record { oa = _ ; oan = _ ; pan = aion  i ; pa = ayy1 i ; eq1 = lem10 } where
       bi = b
       ai = ∧An L PB an i 
       lem02 : b0 < bi  -- (¬ ( b0 ≈ bi )) ∧ ((b0 x bi) ≈ b0) 
       lem02 = bnz
       lem03 : (ai x bi) ≈ b0
       lem03 = btrans {ai x bi} {bi x ai} {b0} (x-sym {ai} {bi}) yy
       lem09 :  b0 ≈ (bi x (- ai)) →  b0 ≈ (bi x ai) →  b0 ≈ bi
       lem09 eq1 eq2 = begin
          b0 ≈⟨ bsym {b0 + b0} {b0} (+-idem {b0} ) ⟩
          b0 + b0 ≈⟨ +-resp {b0} {bi x (- ai)} {b0} {bi x ai} eq1 eq2 ⟩
          (bi x ai) + (bi x ( - ai )) ≈⟨ bsym { bi x (ai + ( - ai ))} { (bi x ai) + (bi x ( - ai ))} (x-dist {bi} {ai} { - ai}   ) ⟩
          bi x (ai + ( - ai )) ≈⟨ x-resp {ai + ( - ai )} {b1} {bi} {bi}  (a+-a1 {ai}) (brefl {bi}) ⟩
          bi x b1 ≈⟨ ax1 {bi} ⟩
          bi ∎ where open EqR bSetoid 
       abn : b0 < ( bi x ( - ai ) )
       abn = ⟪ (λ eq1 → ⊥-elim (proj1 bnz (lem09 eq1 (btrans {b0} {ai x bi} {bi x ai} (bsym {ai x bi} {b0} lem03) (x-sym  { ai} {bi}) )) ) ) , (
           begin
           b0 x ( bi x ( - ai )) ≈⟨ 0≤a ( bi x ( - ai )) ⟩
           b0 ∎ ) ⟫ where open EqR bSetoid 
       lem12 : (b x (- ∧An L PB an i)) ≤  (b x (- (yy0 i)))
       lem12 = x-monoˡ-< { - ∧An L PB an i } { - (yy0 i)} {b} ( neg-mono-≤ { yy0 i }{ ∧An L PB an i} (ai-is-sup (yy0 i ) i (ayy1 i) ) )  
       lem11 :  b0 ≈ (b x (- (yy0 i))) → b0 ≈ (b x (- ∧An L PB an i))
       lem11 eq = begin
           b0 ≈⟨ bsym {b x ( - ∧An L PB an i)} {b0} ( ≤0→≈ {b x (- ∧An L PB an i)} ( resp-≤ {b x (- ∧An L PB an i)} {b x (- (yy0 i))} {b x (- ∧An L PB an i)} {b0} (brefl {b x (- ∧An L PB an i)}) (bsym {b0} {b x (- (yy0 i))} eq) lem12  ) ) ⟩
           b x (- ∧An L PB an i) ∎ where open EqR bSetoid 
       lem10 :  b0 < ( b x ( - (yy0 i) ))
       lem10  = ⟪ (λ eq → ⊥-elim (proj1 abn (lem11 eq)  ) ) , (
             begin b0 ≤⟨ proj2 abn ⟩
             b x  (- ∧An L PB an i ) ≤⟨ x-monoˡ-< { - ∧An L PB an i } { - (yy0 i)} {b} ( neg-mono-≤ { yy0 i }{ ∧An L PB an i} (ai-is-sup (yy0 i) i (ayy1 i)) )  ⟩
             b x ( - (yy0 i) ) ∎ 
          ) ⟫ where
             open BA≤-Reasoning (ba PB)

b-ai→a1 :  (L : HOD)  (PB : HODBooleanAlgebra L ) (an : AN L PB )  
    (i : ℕ) (b : HODBooleanAlgebra.B PB) (bnz : BooleanAlgebra._<_ (ba PB) (BooleanAlgebra.b0 (ba PB)) b) (yy :  BooleanAlgebra._≈_ (ba PB) (( BooleanAlgebra._x_ (ba PB) b ( ∧An L PB an i ))) (BooleanAlgebra.b0 (ba PB))) 
      → AAn L PB b an 
b-ai→a1 L PB an i b bnz yy = record { oa = _ ; oan = _ ; pan = aion  i ; pa = ayy1 i ; eq1 = lem10 } where
   open BooleanAlgebra (ba PB)
   open IsBooleanAlgebra (BooleanAlgebra.isBooleanAlgebra (ba PB))
   ai-is-sup : (y : B PB) → (i : ℕ) → (ay : odef (* (elt (AN.imap an i))) (elt y)) → y ≤ ∧An L PB an i 
   ai-is-sup y i ay = IsCompleteBooleanAlgebra.is-sup ( bc PB ) (PAn L PB an i) y  ay
   yy1 : (i : ℕ) → HOD
   yy1 i = minimal (* (elt (AN.imap an i))) (AN.imap-ne an i)
   ayy1 : (i : ℕ) → odef (* (elt (AN.imap an i))) (& (yy1 i))
   ayy1 i = x∋minimal (* (elt (AN.imap an i))) (AN.imap-ne an i)
   aion :  (i : ℕ) →  OAn L PB an (elt (AN.imap an i))
   aion i = record { i = i ; peq = refl } 
   pbb : odef (OS PB) (elt b) 
   pbb = A∋elt b
   yy0 : (i : ℕ) → HODBooleanAlgebra.B PB
   yy0 i = record { elt = & (yy1 i) ; A∋elt = A∋elt (AN.imap an i) _ (ayy1 i) }
   bi = b
   ai = ∧An L PB an i 
   lem02 : b0 < bi  -- (¬ ( b0 ≈ bi )) ∧ ((b0 x bi) ≈ b0) 
   lem02 = bnz
   lem03 : (ai x bi) ≈ b0
   lem03 = btrans {ai x bi} {bi x ai} {b0} (x-sym {ai} {bi}) yy
   lem09 :  b0 ≈ (bi x (- ai)) →  b0 ≈ (bi x ai) →  b0 ≈ bi
   lem09 eq1 eq2 = begin
      b0 ≈⟨ bsym {b0 + b0} {b0} (+-idem {b0} ) ⟩
      b0 + b0 ≈⟨ +-resp {b0} {bi x (- ai)} {b0} {bi x ai} eq1 eq2 ⟩
      (bi x ai) + (bi x ( - ai )) ≈⟨ bsym { bi x (ai + ( - ai ))} { (bi x ai) + (bi x ( - ai ))} (x-dist {bi} {ai} { - ai}   ) ⟩
      bi x (ai + ( - ai )) ≈⟨ x-resp {ai + ( - ai )} {b1} {bi} {bi}  (a+-a1 {ai}) (brefl {bi}) ⟩
      bi x b1 ≈⟨ ax1 {bi} ⟩
      bi ∎ where open EqR bSetoid 
   abn : b0 < ( bi x ( - ai ) )
   abn = ⟪ (λ eq1 → ⊥-elim (proj1 bnz (lem09 eq1 (btrans {b0} {ai x bi} {bi x ai} (bsym {ai x bi} {b0} lem03) (x-sym  { ai} {bi}) )) ) ) , (
       begin
       b0 x ( bi x ( - ai )) ≈⟨ 0≤a ( bi x ( - ai )) ⟩
       b0 ∎ ) ⟫ where open EqR bSetoid 
   lem12 : (b x (- ∧An L PB an i)) ≤  (b x (- (yy0 i)))
   lem12 = x-monoˡ-< { - ∧An L PB an i } { - (yy0 i)} {b} ( neg-mono-≤ { yy0 i }{ ∧An L PB an i} (ai-is-sup (yy0 i ) i (ayy1 i) ) )  
   lem11 :  b0 ≈ (b x (- (yy0 i))) → b0 ≈ (b x (- ∧An L PB an i))
   lem11 eq = begin
       b0 ≈⟨ bsym {b x ( - ∧An L PB an i)} {b0} ( ≤0→≈ {b x (- ∧An L PB an i)} ( resp-≤ {b x (- ∧An L PB an i)} {b x (- (yy0 i))} {b x (- ∧An L PB an i)} {b0} (brefl {b x (- ∧An L PB an i)}) (bsym {b0} {b x (- (yy0 i))} eq) lem12  ) ) ⟩
       b x (- ∧An L PB an i) ∎ where open EqR bSetoid 
   lem10 :  b0 < ( b x ( - (yy0 i) ))
   lem10  = ⟪ (λ eq → ⊥-elim (proj1 abn (lem11 eq)  ) ) , (
         begin b0 ≤⟨ proj2 abn ⟩
         b x  (- ∧An L PB an i ) ≤⟨ x-monoˡ-< { - ∧An L PB an i } { - (yy0 i)} {b} ( neg-mono-≤ { yy0 i }{ ∧An L PB an i} (ai-is-sup (yy0 i) i (ayy1 i)) )  ⟩
         b x ( - (yy0 i) ) ∎ 
      ) ⟫ where
         open BA≤-Reasoning (ba PB)

record Bni2 (L : HOD)  (PB : HODBooleanAlgebra L ) (an : AN L PB ) (i : ℕ)  : Set n where
   open BooleanAlgebra (ba PB)
   open IsBooleanAlgebra (BooleanAlgebra.isBooleanAlgebra (ba PB))
   field
      b : (j : ℕ) → HODBooleanAlgebra.B PB
      bnz : (j : ℕ) → b0 < b j 
      bmono :  (j : ℕ) → j Data.Nat.≤ i → b j ≤ b i
      eq1 : (j : ℕ) → j Data.Nat.≤ i → (eq : ((b j) x (∧An L PB an j)) ≈ b0 )
          → (b (suc j)) ≡ ( (b j) x ( - (AAn.a (b-ai→a1 L PB an j (b j) (bnz j ) eq ) )))
      eq2 : (j : ℕ) → j Data.Nat.≤ i → (neq : ¬ (((b j) x (∧An L PB an j)) ≈ b0 ))
          → (b (suc j)) ≡  ( (b j) x (∧An L PB an i)  )

Bn1 : (L : HOD) → (PB : HODBooleanAlgebra L ) → (an : AN L PB ) → (i : ℕ) → Bni L PB an → Bni2 L PB an i
Bn1 = ?

get-b : (L : HOD)  (PB : HODBooleanAlgebra L ) (an : AN L PB ) →  Bni2 L PB an ? → Bni L PB an 
get-b = ?

bni2unique : (L : HOD) → (PB : HODBooleanAlgebra L ) → (an : AN L PB ) → (i j k : ℕ) → i Data.Nat.≤  j → (bi :  Bni2 L PB an i)→ (bj :  Bni2 L PB an j)
  → k Data.Nat.≤ i → Bni2.b bi k ≡ Bni2.b bj k 
bni2unique L PB an i j k i≤j bi bj k≤i = ?


record BnR (L : HOD) (PB : HODBooleanAlgebra L ) (an : AN L PB ) (bni : Bni L PB an) (x : Ordinal) : Set n where
    field
       i : ℕ 
       x=bi : x ≡ elt (Bni.b (get-b L PB an (Bn1 L PB an i bni ) ))
    pbb : odef (OS PB) x
    pbb = subst (λ k → odef (OS PB) k) (sym x=bi) ( A∋elt (Bni.b (get-b  L PB an (Bn1 L PB an i bni ) )) )

BnHOD : (L : HOD) → (PB : HODBooleanAlgebra L ) → (an : AN L PB ) (bni : Bni L PB an) → HOD
BnHOD L PB an bni = record { od = record { def = λ x → BnR L PB an bni x } ; odmax = & (OS PB) ; <odmax =  λ lt → odef< (BnR.pbb lt) } 

BnHOD⊆L : (L : HOD) → (PB : HODBooleanAlgebra L ) → (an : AN L PB ) (bni : Bni L PB an)  → BnHOD L PB an bni ⊆ Power L
BnHOD⊆L L PB an bni {x} lt z xz = OS⊆PL PB (BnR.pbb lt) _ xz 


bni-mono1 : (L : HOD) → (PB : HODBooleanAlgebra L ) → (an : AN L PB ) (bni : Bni L PB an) → (i : ℕ)
    → (* (elt (Bni.b (get-b L PB an (Bn1 L PB an (suc i) bni ) ) ))) ⊆  (* (elt (Bni.b (get-b L PB an (Bn1 L PB an i bni ) ) )))
bni-mono1 L PB an bni zero {z} lt = ?

bni-mono : (L : HOD) → (PB : HODBooleanAlgebra L ) → (an : AN L PB ) (bni : Bni L PB an) → (i j : ℕ) → i Data.Nat.≤ j
         → (* (elt (Bni.b ?  ))) ⊆  (* (elt (Bni.b ?  )))
bni-mono = ?

BnFilter : (L : HOD) → (PB : HODBooleanAlgebra L ) → (an : AN L PB ) (bni : Bni L PB an) → Filter  {OS PB} {L} (OS⊆PL PB) 
BnFilter L PB an bni = record { filter = BnHOD L PB an bni ; f⊆L =  BnR.pbb  ; filter1 = f1 ; filter2 = f2 } where
   f1 :  {p q : HOD} → OS PB ∋ q → BnHOD L PB an bni ∋ p → p ⊆ q → BnHOD L PB an bni ∋ q 
   f1 {p} {q} oq bp p⊆q = record { i = ? ; x=bi = ? } where
      lem00 : ?
      lem00 = ?
   f2 :  {p q : HOD} → BnHOD L PB an bni ∋ p → BnHOD L PB an bni ∋ q → OS PB ∋ (p ∩ q) → BnHOD L PB an bni ∋ (p ∩ q)
   f2 {p} {q} bp bq p∩q = record { i = ? ; x=bi = ? } where
      lem00 : ?
      lem00 = ?


