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

record Bni3 (L : HOD)  (PB : HODBooleanAlgebra L ) (an : AN L PB ) (i : ℕ)  : Set n where
   open BooleanAlgebra (ba PB)
   open IsBooleanAlgebra (BooleanAlgebra.isBooleanAlgebra (ba PB))
   field
      b : (j : ℕ) → j Data.Nat.< i → HODBooleanAlgebra.B PB
      bnz : (j : ℕ) → (lt : j Data.Nat.< i ) → b0 < b j lt
      bmono1 : (j : ℕ) → (lt : j Data.Nat.< i) →  b (suc j) ? ≤ b j lt
      -- abn : b0 < ( b + ( - (∧An L PB an i ) ) ) → AAn L PB b an 
   ai-is-sup : (y : B PB) → (i : ℕ) → (ay : odef (* (elt (AN.imap an i))) (elt y)) → y ≤ ∧An L PB an i 
   ai-is-sup y i ay = IsCompleteBooleanAlgebra.is-sup ( bc PB ) (PAn L PB an i) y  ay
   yy1 : (i : ℕ) → HOD
   yy1 i = minimal (* (elt (AN.imap an i))) (AN.imap-ne an i)
   ayy1 : (i : ℕ) → odef (* (elt (AN.imap an i))) (& (yy1 i))
   ayy1 i = x∋minimal (* (elt (AN.imap an i))) (AN.imap-ne an i)
   aion :  (i : ℕ) →  OAn L PB an (elt (AN.imap an i))
   aion i = record { i = i ; peq = refl } 
   pbb : odef (OS PB) (elt (b ? ? )) 
   pbb = A∋elt (b ? ? )
   yy0 : (i : ℕ) → HODBooleanAlgebra.B PB
   yy0 i = record { elt = & (yy1 i) ; A∋elt = A∋elt (AN.imap an i) _ (ayy1 i) }
   ai→a1 :  (i : ℕ) (yy :  (b ? ? x ( ∧An L PB an i )) ≈ b0) → AAn L PB (b ? ? ) an 
   ai→a1 i yy = record { oa = _ ; oan = _ ; pan = aion  i ; pa = ayy1 i ; eq1 = lem10 } where
       bi = b ? ?
       ai = ∧An L PB an i 
       lem02 : b0 < bi  -- (¬ ( b0 ≈ bi )) ∧ ((b0 x bi) ≈ b0) 
       lem02 = bnz ? ?
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
       abn = ⟪ (λ eq1 → ⊥-elim (proj1 (bnz ? ? ) (lem09 eq1 (btrans {b0} {ai x bi} {bi x ai} (bsym {ai x bi} {b0} lem03) (x-sym  { ai} {bi}) )) ) ) , (
           begin
           b0 x ( bi x ( - ai )) ≈⟨ 0≤a ( bi x ( - ai )) ⟩
           b0 ∎ ) ⟫ where open EqR bSetoid 
       lem12 : (b ? ? x (- ∧An L PB an i)) ≤  (b ? ? x (- (yy0 i)))
       lem12 = x-monoˡ-< { - ∧An L PB an i } { - (yy0 i)} {b ? ?} ( neg-mono-≤ { yy0 i }{ ∧An L PB an i} (ai-is-sup (yy0 i ) i (ayy1 i) ) )  
       lem11 :  b0 ≈ (b ? ? x (- (yy0 i))) → b0 ≈ (b ? ? x (- ∧An L PB an i))
       lem11 eq = begin
           b0 ≈⟨ bsym {b ? ? x ( - ∧An L PB an i)} {b0} ( ≤0→≈ {b ? ? x (- ∧An L PB an i)} ( resp-≤ {b ? ? x (- ∧An L PB an i)} {b ? ? x (- (yy0 i))} {b ? ? x (- ∧An L PB an i)} {b0} (brefl {b ? ? x (- ∧An L PB an i)}) (bsym {b0} {b ? ? x (- (yy0 i))} eq) lem12  ) ) ⟩
           b ? ? x (- ∧An L PB an i) ∎ where open EqR bSetoid 
       lem10 :  b0 < ( b ? ? x ( - (yy0 i) ))
       lem10  = ⟪ (λ eq → ⊥-elim (proj1 abn (lem11 eq)  ) ) , (
             begin b0 ≤⟨ proj2 abn ⟩
             b ? ? x  (- ∧An L PB an i ) ≤⟨ x-monoˡ-< { - ∧An L PB an i } { - (yy0 i)} {b ? ? } ( neg-mono-≤ { yy0 i }{ ∧An L PB an i} (ai-is-sup (yy0 i) i (ayy1 i)) )  ⟩
             b ? ? x ( - (yy0 i) ) ∎ 
          ) ⟫ where
             open BA≤-Reasoning (ba PB)

data Bni2 (L : HOD)  (PB : HODBooleanAlgebra L ) (an : AN L PB ) : Set n 

get-b : (L : HOD)  (PB : HODBooleanAlgebra L ) (an : AN L PB ) →  Bni2 L PB an → Bni L PB an 

--
--    empty-case ?
--
data Bni2 L PB an where 
   b-nil : (b : HODBooleanAlgebra.B PB) (bnz : BooleanAlgebra._<_ (ba PB) (BooleanAlgebra.b0 (ba PB)) b) → Bni2 L PB an 
   empty-case : (i : ℕ) → (bni : Bni2 L PB an) 
     →   (BooleanAlgebra._≈_ (ba PB) (BooleanAlgebra._x_ (ba PB) (Bni.b (get-b L PB an bni)) (∧An L PB an i) ) (BooleanAlgebra.b0 (ba PB))) 
     → Bni2 L PB an 
   conj-case : (i : ℕ) → (bni : Bni2 L PB an) 
     → ¬ ((BooleanAlgebra._≈_ (ba PB) (BooleanAlgebra._x_ (ba PB) (Bni.b (get-b L PB an bni)) (∧An L PB an i) ) (BooleanAlgebra.b0 (ba PB))) )
     → Bni2 L PB an 

get-b L PB an (b-nil b bnz) = record { b = b ; bnz = bnz }
get-b L PB an (empty-case i bni yy) = record { b = bi x ( - a ) ; bnz = AAn.eq1 (Bni.ai→a1 (get-b L PB an bni) i yy) } where
    open BooleanAlgebra (ba PB)
    open IsBooleanAlgebra (BooleanAlgebra.isBooleanAlgebra (ba PB))
    ai = ∧An L PB an i 
    bi = Bni.b (get-b L PB an bni)
    a =  AAn.a (Bni.ai→a1 (get-b L PB an bni) i yy)
get-b L PB an (conj-case i bni nn) = record { b = (BooleanAlgebra._x_ (ba PB) (Bni.b (get-b L PB an bni)) (∧An L PB an i) ) ; bnz = ⟪ (λ 0=ba → ⊥-elim (nn (bsym {b0} {bi x ai} 0=ba))) , 0≤a (bi x ai)  ⟫ } where
    open BooleanAlgebra (ba PB)
    open IsBooleanAlgebra (BooleanAlgebra.isBooleanAlgebra (ba PB))
    ai = ∧An L PB an i 
    bi = Bni.b (get-b L PB an bni)

Bn1 : (L : HOD) → (PB : HODBooleanAlgebra L ) → (an : AN L PB ) → (i : ℕ) → Bni L PB an → Bni2 L PB an
Bn1 L PB an zero bni = b-nil (Bni.b bni) (Bni.bnz bni)
Bn1 L PB an (suc i)  bni with p∨¬p (BooleanAlgebra._≈_ (ba PB) (BooleanAlgebra._x_ (ba PB) (Bni.b (get-b L PB an (Bn1 L PB an i bni ))) (∧An L PB an i) ) (BooleanAlgebra.b0 (ba PB))) 
... | case1 yy = empty-case i (Bn1 L PB an i bni ) yy 
... | case2 nn = conj-case  i (Bn1 L PB an i bni ) nn   

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

--   record Bn3  (L : HOD)  (PB : HODBooleanAlgebra L ) (an : AN L PB ) (i : ℕ) : Set n where
--      open BooleanAlgebra (ba PB)
--      open IsBooleanAlgebra (BooleanAlgebra.isBooleanAlgebra (ba PB))
--      field
--         bn : ℕ → B PB
--         0<bn : (j : ℕ) → j ≤ i → b0 < bn j
--         bmono : (j : ℕ) →  j ≤ i → bn (suc j) ⊆ bn j

-- Bn1-eq : (L : HOD) → (PB : HODBooleanAlgebra L ) → (an : AN L PB ) → (i j : ℕ) → i ≡ j → (bni : Bni L PB an )→ Bn0 L PB an i bni ≡ Bn1 L PB an j bni 
-- Bn1-eq = ?

-- cHOD : CM → Set (Level.suc n) 
-- cHOD cm = HODBase.HOD (CM.Odnl cm) 

-- codef : (cm : CM) (B : cHOD cm) → (x : Ordinals.Ordinal (CM.Odnl cm)) → Set n
-- codef cm B x = HODBase.OD.def (HODBase.HOD.od B) x

-- cmHOD : (cm : CM) → cHOD cm → HOD
-- cmHOD cm p = record { od = record { def = λ x → odef (Omega ?) x ∧ codef cm p ? } ; odmax = ? ; <odmax = ? }

-- cmGen : {m : Level} (cm : CM) (B : cHOD cm) → Filter ?
-- cmGen = ?

--   a : {m : Level} (cm : CM) (B : cHOD cm)
--      → (i : ℕ) → HOD
--   a {m} cm B i = ? -- record { od = record { def = λ x → ¬ (x ≡ o∅ ) ∧ ( * x  ⊆ ? ) } ; odmax = ? ; <odmax = ? }
--
--   b : {m : Level} (cm : CM) (B : cHOD cm)
--      → (i : ℕ) → HOD
--   b = ?
--
--   GenericFilter : {m : Level} (cm : CM) (B : cHOD cm)
--      → Filter ?
--   GenericFilter = ?
--
--   MaximumGenericFilter : {m : Level} (cm : CM) (B : cHOD cm) → ?
--   MaximumGenericFilter = ?
--
--   DensceGF : {m : Level} (cm : CM) (B : cHOD cm) → ?
--   DensceGF = ?
--
--   GenericFilter→HODAxiom : {m : Level} (cm : CM) (B : cHOD cm) → (F : Filter ? ) ( MX : ? ) ( dense : Dense ? ) → CM
--   GenericFilter→HODAxiom = ?


bni-cong : (L : HOD) → (PB : HODBooleanAlgebra L ) → (an : AN L PB ) (bni : Bni L PB an) (a b : Bni2 L PB an) → a ≡ b
    → (BooleanAlgebra._≈_ (ba PB) (Bni.b (get-b L PB an a  ))  (Bni.b (get-b L PB an b  ) ))
bni-cong L PB an bni a b refl = brefl {(Bni.b (get-b L PB an b  ) )} where
    open IsBooleanAlgebra (BooleanAlgebra.isBooleanAlgebra (ba PB))

bni-eq00 : (L : HOD) → (PB : HODBooleanAlgebra L ) → (an : AN L PB ) (bni : Bni L PB an) (a : Bni2 L PB an) 
    → (i0 i1 : ℕ) → (t0 t1 : Bni2 L PB an) 
    → (yy0 : (BooleanAlgebra._≈_ (ba PB) (BooleanAlgebra._x_ (ba PB) (Bni.b (get-b L PB an t0)) (∧An L PB an i0) ) (BooleanAlgebra.b0 (ba PB))) )
    → (yy1 : (BooleanAlgebra._≈_ (ba PB) (BooleanAlgebra._x_ (ba PB) (Bni.b (get-b L PB an t1)) (∧An L PB an i1) ) (BooleanAlgebra.b0 (ba PB))) )
    → empty-case i0 t0 yy0 ≡  empty-case i1 t1 yy1
    → (t0 ≡ t1) ∧ (i0 ≡ i1)
bni-eq00 L PB an bni _ _ _ _ _ _ _ eq = ?

bni-cong1 : (L : HOD) → (PB : HODBooleanAlgebra L ) → (an : AN L PB ) (bni : Bni L PB an) (a : Bni2 L PB an) 
    → (i : ℕ) → (t : Bni2 L PB an) 
    → (yy : (BooleanAlgebra._≈_ (ba PB) (BooleanAlgebra._x_ (ba PB) (Bni.b (get-b L PB an t)) (∧An L PB an i) ) (BooleanAlgebra.b0 (ba PB))) )
    → empty-case i t yy ≡  Bn1 L PB an (suc i) bni
    → t ≡ a
bni-cong1 L PB an bni a i t yy eq with Bn1 L PB an (suc i) bni in eq1
... | empty-case i₁ ttt x = ?


bni-mono2 : (L : HOD) → (PB : HODBooleanAlgebra L ) → (an : AN L PB ) (bni : Bni L PB an) → (i : ℕ)
    → (* (elt (Bni.b (get-b L PB an (Bn1 L PB an (suc i) bni ) ) ))) ⊆  (* (elt (Bni.b (get-b L PB an (Bn1 L PB an i bni ) ) )))
bni-mono2 L PB an bni i {z} = ? where
    lem00 : (L : HOD) → (PB : HODBooleanAlgebra L ) → (an : AN L PB ) (bni : Bni L PB an) → (i : ℕ) → Bn1 L PB an i bni ≡ ?
    lem00 L PB an bni zero = ?
    lem00 L PB an bni (suc i) with p∨¬p (BooleanAlgebra._≈_ (ba PB) (BooleanAlgebra._x_ (ba PB) (Bni.b (get-b L PB an (Bn1 L PB an i bni ))) (∧An L PB an i) )  
       (BooleanAlgebra.b0 (ba PB))) 
    ... | case1 rrr = {! !}
    ... | case2 rrr = {! !}


bni-mono1 : (L : HOD) → (PB : HODBooleanAlgebra L ) → (an : AN L PB ) (bni : Bni L PB an) → (i : ℕ)
    → (* (elt (Bni.b (get-b L PB an (Bn1 L PB an (suc i) bni ) ) ))) ⊆  (* (elt (Bni.b (get-b L PB an (Bn1 L PB an i bni ) ) )))
bni-mono1 L PB an bni zero {z} lt with Bn1 L PB an (suc zero) bni  in eq
... | b-nil b bnz = ?
... | empty-case i t yy = lem00 where
    open BooleanAlgebra (ba PB)
    open IsBooleanAlgebra (BooleanAlgebra.isBooleanAlgebra (ba PB))
    ai = ∧An L PB an i 
    bi = Bni.b (get-b L PB an t )
    a =  AAn.a (Bni.ai→a1 (get-b L PB an t) i yy )
    lem03 : (bi x ai ) ≈ b0
    lem03 = yy
    lem02 : odef (* (elt (bi x ( - a)))) z
    lem02 = lt
    lem00 : odef (* (elt (Bni.b bni))) z
    lem00 = ?
... | conj-case i t x₁ = {! !}
bni-mono1 L PB an bni (suc i) {z} lt with Bn1 L PB an (suc (suc i)) bni  in eq
... | b-nil b bnz = ?
... | empty-case j t yy = lem01 where
    open BooleanAlgebra (ba PB)
    open IsBooleanAlgebra (BooleanAlgebra.isBooleanAlgebra (ba PB))
    ai = ∧An L PB an j 
    bi = Bni.b (get-b L PB an t )
    a =  AAn.a (Bni.ai→a1 (get-b L PB an t) j yy )
    lem04 : (Bni.b (get-b L PB an (Bn1 L PB an (suc (suc i)) bni ) ) ) ≈ (bi x ( - a ))
    lem04 = begin
       Bni.b (get-b L PB an (Bn1 L PB an (suc (suc i)) bni ) ) ≈⟨ bni-cong L PB an bni _ _ eq ⟩
       Bni.b (get-b L PB an (empty-case j t yy )  ) ≈⟨ brefl {bi x (- a)} ⟩
       bi x ( - a ) ∎ where open EqR bSetoid
    lem06 : * (elt (bi x ( - a )) ) ⊆ * (elt bi ) 
    lem06 {z} lt = proj1 ( eq→  *iso  lt )
    lt1 : odef (* (elt (Bni.b (get-b L PB an (empty-case j t yy))))) z
    lt1 = lt
    bni-mono3 : (* (elt (Bni.b (get-b L PB an (Bn1 L PB an (suc i) bni ) ) ))) ⊆  (* (elt (Bni.b (get-b L PB an (Bn1 L PB an i bni ) ) )))
    bni-mono3 = bni-mono1 L PB an bni i 
    lem03 : (bi x ai ) ≈ b0
    lem03 = yy
    lem02 : odef (* (elt (bi x ( - a)))) z
    lem02 = lt
    lem08 : Bn1 L PB an (suc (suc i)) bni ≡ empty-case j t yy
    lem08 = eq 
    lem07 : (* ( elt (Bni.b (get-b L PB an t)))) =h= (* (elt (Bni.b (get-b L PB an (Bn1 L PB an (suc i) bni ) ))))
    lem07 = ?
    lem01 : odef (* (elt (Bni.b (get-b L PB an (Bn1 L PB an (suc i) bni ) ) ))) z
    lem01 = eq→ lem07 (lem06 lt)
... | conj-case j t nn = lem01  where
    open BooleanAlgebra (ba PB)
    open IsBooleanAlgebra (BooleanAlgebra.isBooleanAlgebra (ba PB))
    ai = ∧An L PB an j 
    bi = Bni.b (get-b L PB an t )
    -- a =  AAn.a (Bni.ai→a1 (get-b L PB an t) j yy )
    bni-mono3 : (* (elt (Bni.b (get-b L PB an (Bn1 L PB an (suc i) bni ) ) ))) ⊆  (* (elt (Bni.b (get-b L PB an (Bn1 L PB an i bni ) ) )))
    bni-mono3 = bni-mono1 L PB an bni i 
    lem08 : Bn1 L PB an (suc (suc i)) bni ≡ (conj-case j t nn)
    lem08 = eq 
    lem03 : ¬ ((bi x ai ) ≈ b0)
    lem03 = nn
    lem02 : odef (* (elt (bi + ai ))) z
    lem02 = ?
    lem01 : odef (* (elt (Bni.b (get-b L PB an (Bn1 L PB an (suc i) bni ) ) ))) z
    lem01 = ?
    lem04 : odef   (* (elt (Bni.b (get-b L PB an (conj-case j t nn))))) z
    lem04 = lt 

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


