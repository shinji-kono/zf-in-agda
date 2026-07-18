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
open import Data.Nat.Properties 
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
   open BooleanAlgebra ba 
   open IsBooleanAlgebra (BooleanAlgebra.isBooleanAlgebra ba )
   ⊆→≤  :　{ p q : HODElement (HBAR.OS H) } → * (elt p) ⊆ * (elt q) → p ≤ q
   ⊆→≤ {p} {q}  = proj1 ( HBA-⊆ L LDec H p q )
   ≤→⊆  :　{ p q : HODElement (HBAR.OS H) }  → p ≤ q → * (elt p) ⊆ * (elt q)
   ≤→⊆  {p} {q}  = proj2 ( HBA-⊆ L LDec H p q )


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

∧An-cong : (L : HOD) → (PB : HODBooleanAlgebra L ) → (an : AN L PB) → (i j : ℕ) → i ≡ j → BooleanAlgebra._≈_ (ba PB) (∧An L PB an i) (∧An L PB an j)
∧An-cong L PB an i j eq = lem00 where
   open BooleanAlgebra (ba PB)
   open IsBooleanAlgebra (BooleanAlgebra.isBooleanAlgebra (ba PB))
   lem00 : (∧An L PB an i) ≈ (∧An L PB an j)
   lem00 = subst (λ k → (∧An L PB an i) ≈ (∧An L PB an k) ) eq (brefl {∧An L PB an i})

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

ai→a1-cong :  (L : HOD)  (PB : HODBooleanAlgebra L ) (an : AN L PB )  
    (i j : ℕ) (bi bj : HODBooleanAlgebra.B PB) (bnzi : BooleanAlgebra._<_ (ba PB) (BooleanAlgebra.b0 (ba PB)) bi) 
       (bnzj : BooleanAlgebra._<_ (ba PB) (BooleanAlgebra.b0 (ba PB)) bj)
    (yyi :  BooleanAlgebra._≈_ (ba PB) (( BooleanAlgebra._x_ (ba PB) bi ( ∧An L PB an i ))) (BooleanAlgebra.b0 (ba PB)))  
    (yyj :  BooleanAlgebra._≈_ (ba PB) (( BooleanAlgebra._x_ (ba PB) bj ( ∧An L PB an j ))) (BooleanAlgebra.b0 (ba PB)))  
    →  i ≡ j
    →  BooleanAlgebra._≈_ (ba PB) (AAn.a (b-ai→a1 L PB an i bi bnzi yyi ) ) (AAn.a (b-ai→a1 L PB an j bj bnzj yyj ) )
ai→a1-cong L PB an i i bi bn bnzi bnzj yyi yyj refl = brefl {(AAn.a (b-ai→a1 L PB an i bi bnzi yyi ) )} where
   open BooleanAlgebra (ba PB)
   open IsBooleanAlgebra (BooleanAlgebra.isBooleanAlgebra (ba PB))

record Bni2 (L : HOD)  (PB : HODBooleanAlgebra L ) (an : AN L PB ) (bn0 : Bni L PB an) (i : ℕ)  : Set n where
   open BooleanAlgebra (ba PB)
   open IsBooleanAlgebra (BooleanAlgebra.isBooleanAlgebra (ba PB))
   field
      b : (j : ℕ) → HODBooleanAlgebra.B PB
      bnz : (j : ℕ) → b0 < b j 
      bzero : (j : ℕ) → j ≡ zero → b j ≡ Bni.b bn0
      bmono :  (j : ℕ) → j Data.Nat.≤ i → b i ≤ b j
      eq1 : (j : ℕ) → j Data.Nat.< i → (eq : ((b j) x (∧An L PB an j)) ≈ b0 )
          → (b (suc j)) ≈ ( (b j) x ( - (AAn.a (b-ai→a1 L PB an j (b j) (bnz j ) eq ) )))
      eq2 : (j : ℕ) → j Data.Nat.< i → (neq : ¬ (((b j) x (∧An L PB an j)) ≈ b0 ))
          → (b (suc j)) ≈  ( (b j) x (∧An L PB an j)  )
   bcong : (i j : ℕ) → i ≡ j →  b i ≈ b j
   bcong i j eq = subst ( λ k → b i ≈ b k ) eq ( brefl {b i} )
   bin2-lem00 : (a b : HODBooleanAlgebra.B PB) → (a x b) ≤ a
   bin2-lem00 a b = begin
      (a x b) x a ≈⟨ x-sym {a x b} {a} ⟩
      a x (a x b)  ≈⟨ x-assoc {a} {a} {b} ⟩
      (a x a) x b  ≈⟨ x-resp {b} {b} {a x a} {a} (brefl {b} ) (x-idem  {a}) ⟩
      a x b ∎ where open EqR bSetoid 
   bzero≈  : ( j : ℕ) → j ≡ zero → b j ≈ Bni.b bn0
   bzero≈ j eq = o≡→== (cong elt (bzero j eq))

Bn1 : (L : HOD) → (PB : HODBooleanAlgebra L ) → (an : AN L PB ) → (i : ℕ) → (bn0 : Bni L PB an) → Bni2 L PB an bn0 i
Bn1 L PB an zero bni = record { b = λ j → Bni.b bni ; bzero = λ _ eq → refl ; bnz = λ j → Bni.bnz bni ; bmono = λ j j≤0 →  x-idem {Bni.b bni}  ; eq1 = λ _ () ; eq2 = λ _ () } where
   open BooleanAlgebra (ba PB)
   open IsBooleanAlgebra (BooleanAlgebra.isBooleanAlgebra (ba PB))
Bn1 L PB an (suc i) bn0 = record { b = b ; bnz = bnz ; bmono = λ j j≤i → mono j (suc i) refl j≤i ; bzero = bzero 
       ; eq1 = λ j j<i eq → eq1 j (suc j) refl j<i eq 
       ; eq2 = λ j j<i ne → eq2 j (suc j) refl j<i ne  } where
   open BooleanAlgebra (ba PB)
   open IsBooleanAlgebra (BooleanAlgebra.isBooleanAlgebra (ba PB))
   obni : Bni2 L PB an bn0 i
   obni  = Bn1 L PB an i bn0
   bi : (j : ℕ) → HODBooleanAlgebra.B PB
   bi j with  p∨¬p ( (  (Bni2.b (Bn1 L PB an i bn0) i) x (∧An L PB an i)) ≈ b0 )
   ... | case1 eq = ( Bni2.b obni i) x ( - (AAn.a (b-ai→a1 L PB an i (Bni2.b obni i) (Bni2.bnz obni i ) eq ) ))
   ... | case2 ne = ( Bni2.b obni i) x (∧An L PB an i) 
   bnzi : (j : ℕ) → b0 < bi j 
   bnzi j with  p∨¬p ( (  (Bni2.b (Bn1 L PB an i bn0) i) x (∧An L PB an i)) ≈ b0 )
   ... | case1 eq = AAn.eq1 (b-ai→a1 L PB an i (Bni2.b obni i) (Bni2.bnz obni i ) eq ) 
   ... | case2 ne = ⟪ (λ eq → ne (bsym {b0} {( Bni2.b obni i) x (∧An L PB an i) } eq) ) , 0≤a (( Bni2.b obni i) x (∧An L PB an i) )  ⟫
   bi-cong : (j k : ℕ) → j ≡ k → bi j ≈ bi k
   bi-cong j k refl = brefl  {bi j}
   b : (j : ℕ) → HODBooleanAlgebra.B PB
   b j with Data.Nat.<-cmp j (suc i)
   ... | tri< a ¬b ¬c = Bni2.b obni j
   ... | tri≈ ¬a b ¬c = bi j 
   ... | tri> ¬a ¬b c = bi j 
   bnz : (j : ℕ) → b0 < b j
   bnz j with Data.Nat.<-cmp j (suc i)
   ... | tri< a ¬b ¬c = Bni2.bnz obni j
   ... | tri≈ ¬a b ¬c = bnzi j 
   ... | tri> ¬a ¬b c = bnzi j 
   bzero : (j : ℕ) → j ≡ zero → b j ≡ Bni.b bn0
   bzero j eq  with Data.Nat.<-cmp j (suc i)
   ... | tri< a ¬b ¬c = Bni2.bzero obni j eq
   ... | tri≈ ¬a b ¬c = ⊥-elim (⊥-elim (nat-≡< (sym eq) (subst (λ k → 1 n≤ k) (sym b) (s≤s z≤n)))) 
   ... | tri> ¬a ¬b c = ⊥-elim (⊥-elim (nat-≡< (sym eq) (≤-<-trans z≤n c))) 
   eq1 : (j k : ℕ) → k ≡ suc j → j Data.Nat.< suc i → (eq : ((b j) x (∧An L PB an j)) ≈ b0 )
          → (b k) ≈ ( (b j) x ( - (AAn.a (b-ai→a1 L PB an j (b j) (bnz j) eq ) )))
   eq1 j k k=sj lt eq with Data.Nat.<-cmp k (suc i)
   ... | tri< a ¬b ¬c = lem00  where 
       lem00 : (Bni2.b obni k) ≈ ( (b j) x ( - (AAn.a (b-ai→a1 L PB an j (b j ) (bnz j) eq ) )))
       lem00 with Data.Nat.<-cmp j (suc i)
       ... | tri< a₁ ¬b ¬c = subst (λ w → (Bni2.b obni w) 
            ≈ ( (Bni2.b obni j) x ( - (AAn.a (b-ai→a1 L PB an j (Bni2.b obni j ) (Bni2.bnz obni j) eq ) ))) ) (sym k=sj) 
               ( Bni2.eq1 obni j (sx≤py→x≤y (subst (λ w → w Data.Nat.< (suc i)) k=sj a)) eq )
       ... | tri≈ ¬a b ¬c = ⊥-elim ( nat-≤> (refl-≤≡ (sym b)) lt ) 
       ... | tri> ¬a ¬b c = ⊥-elim ( nat-≤> (<-trans (s≤s refl-≤) c) lt ) 
   ... | tri≈ ¬a b₁ ¬c = lem00 j refl eq where -- k ≡ suc i, k ≡ suc j
       lem00 : (m : ℕ) → m ≡ j → (eq2 : ((b m) x (∧An L PB an m)) ≈ b0 )→ (bi k ) ≈ ( (b m) x ( - (AAn.a (b-ai→a1 L PB an m (b m ) (bnz m) eq2 ) )))
       lem00 m m=j eq2 with Data.Nat.<-cmp m (suc i)
       ... | tri< a ¬b ¬c = lem03 where  
           i=m : i ≡ m
           i=m = trans (cong pred (trans (sym b₁) k=sj ) ) (sym m=j )
           lem03 : (bi k ) ≈ ( (Bni2.b obni m) x ( - (AAn.a (b-ai→a1 L PB an m (Bni2.b obni m ) (Bni2.bnz obni m) eq2 ) )))
           lem03 with  p∨¬p ( (  (Bni2.b (Bn1 L PB an i bn0) i) x (∧An L PB an i)) ≈ b0 )
           ... | case1 eq3 = begin
               ((Bni2.b obni i) x ( - (AAn.a (b-ai→a1 L PB an i (Bni2.b obni i ) (Bni2.bnz obni i) eq3 ) ))) 
                  ≈⟨ x-resp { - (AAn.a (b-ai→a1 L PB an i (Bni2.b obni i ) (Bni2.bnz obni i) eq3 ) )} 
                    { - (AAn.a (b-ai→a1 L PB an m (Bni2.b obni m ) (Bni2.bnz obni m) eq2 ) )}  {Bni2.b obni i} {Bni2.b obni m} 
                     (neg-resp {AAn.a (b-ai→a1 L PB an i (Bni2.b obni i ) (Bni2.bnz obni i) eq3 )} 
                        {AAn.a (b-ai→a1 L PB an m (Bni2.b obni m ) (Bni2.bnz obni m) eq2 )  } 
                         (ai→a1-cong L PB an _ _ (Bni2.b obni i) (Bni2.b obni m) (Bni2.bnz obni i) (Bni2.bnz obni m) eq3 eq2 i=m ))  (Bni2.bcong obni _ _ i=m )  ⟩
               ((Bni2.b obni m) x ( - (AAn.a (b-ai→a1 L PB an m (Bni2.b obni m ) (Bni2.bnz obni m) eq2 ) )))  ∎ where 
                  open EqR bSetoid
           ... | case2 ne = ⊥-elim ( ne ( begin
              (  (Bni2.b (Bn1 L PB an i bn0) i) x (∧An L PB an i)) ≈⟨ x-resp 
                  {∧An L PB an i} {∧An L PB an m} {Bni2.b (Bn1 L PB an i bn0) i} {Bni2.b (Bn1 L PB an i bn0) m} 
                  (∧An-cong L PB an _ _ i=m ) (Bni2.bcong (Bn1 L PB an i bn0) _ _ i=m ) ⟩
              (  (Bni2.b (Bn1 L PB an i bn0) m) x (∧An L PB an m)) ≈⟨ eq2 ⟩
              b0 ∎ ) ) where 
                  open EqR bSetoid
       ... | tri≈ ¬a b₁ ¬c = ⊥-elim ( nat-≡< b₁ (<-≤-trans (refl-≤≡ (cong suc m=j)) lt ) )
       ... | tri> ¬a ¬b c = ⊥-elim ( nat-≡< (trans (trans (sym b₁) k=sj ) (cong suc (sym m=j) )) (<-trans c a<sa) )
   ... | tri> ¬a ¬b c = ⊥-elim (nat-≤> (subst (λ k →  k n≤ suc i) (sym k=sj) lt ) c ) 
   eq2 : (j k : ℕ) → k ≡ suc j → j Data.Nat.< suc i → (ne : ¬ (((b j) x (∧An L PB an j)) ≈ b0 ))
          → (b k) ≈ ( (b j) x ( (∧An L PB an j)  ))
   eq2 j k k=sj lt ne with Data.Nat.<-cmp k (suc i)
   ... | tri< a ¬b ¬c = lem00  where 
       lem00 : (Bni2.b obni k) ≈ ( (b j) x ( (∧An L PB an j)  ))
       lem00 with Data.Nat.<-cmp j (suc i)
       ... | tri< a₁ ¬b ¬c = subst (λ w → (Bni2.b obni w) 
            ≈ ( (Bni2.b obni j) x (∧An L PB an j)) ) (sym k=sj) ( Bni2.eq2 obni j (sx≤py→x≤y (subst (λ w → w Data.Nat.< (suc i)) k=sj a)) ne )
       ... | tri≈ ¬a b ¬c = ⊥-elim ( nat-≤> (refl-≤≡ (sym b)) lt ) 
       ... | tri> ¬a ¬b c = ⊥-elim ( nat-≤> (<-trans (s≤s refl-≤) c) lt ) 
   ... | tri≈ ¬a b₁ ¬c = lem00 j refl ne where -- k ≡ suc i, k ≡ suc j
       lem00 : (m : ℕ) → m ≡ j → (eq2 : ¬ (((b m) x (∧An L PB an m)) ≈ b0 ))→ (bi k ) ≈ ( (b m) x  (∧An L PB an j) )
       lem00 m m=j neq2 with Data.Nat.<-cmp m (suc i)
       ... | tri< a ¬b ¬c = lem03 where  
           i=m : i ≡ m
           i=m = trans (cong pred (trans (sym b₁) k=sj ) ) (sym m=j )
           i=j : i ≡ j
           i=j = cong pred (trans (sym b₁) k=sj ) 
           lem03 : (bi k ) ≈ ( (Bni2.b obni m) x (∧An L PB an j) )
           lem03 with  p∨¬p ( (  (Bni2.b (Bn1 L PB an i bn0) i) x (∧An L PB an i)) ≈ b0 )
           ... | case1 eq3 = ⊥-elim (neq2 (begin 
              ((Bni2.b (Bn1 L PB an i bn0) m) x (∧An L PB an m)) ≈⟨ x-resp {∧An L PB an m} {∧An L PB an i} 
                     {Bni2.b (Bn1 L PB an i bn0) m} {Bni2.b (Bn1 L PB an i bn0) i}
                 (∧An-cong L PB an _ _ (sym i=m) )  (Bni2.bcong (Bn1 L PB an i bn0) _ _ (sym i=m) ) ⟩ 
              ((Bni2.b (Bn1 L PB an i bn0) i) x (∧An L PB an i)) ≈⟨ eq3 ⟩ 
              b0 ∎ )) where 
                 open EqR bSetoid
           ... | case2 ne3 = begin
               ((Bni2.b (Bn1 L PB an i bn0) i) x  (∧An L PB an i)) 
                 ≈⟨  x-resp {∧An L PB an i} {∧An L PB an j} {Bni2.b (Bn1 L PB an i bn0) i} {Bni2.b (Bn1 L PB an i bn0) m}  
                     (∧An-cong L PB an _ _ i=j ) (Bni2.bcong (Bn1 L PB an i bn0) _ _ i=m ) ⟩
              ( (Bni2.b (Bn1 L PB an i bn0) m) x  (∧An L PB an j) )  ∎ where 
                 open EqR bSetoid
       ... | tri≈ ¬a b₁ ¬c = ⊥-elim ( nat-≡< b₁ (<-≤-trans (refl-≤≡ (cong suc m=j)) lt ) )
       ... | tri> ¬a ¬b c = ⊥-elim ( nat-≡< (trans (trans (sym b₁) k=sj ) (cong suc (sym m=j) )) (<-trans c a<sa) )
   ... | tri> ¬a ¬b c = ⊥-elim (nat-≤> (subst (λ k →  k n≤ suc i) (sym k=sj) lt ) c ) 
   mono : (j k : ℕ) → k ≡ suc i → j Data.Nat.≤ suc i 
          → b k ≤  b j
   mono j k k=sj lt with Data.Nat.<-cmp k (suc i)
   ... | tri< a ¬b ¬c = ⊥-elim ( ¬b k=sj ) 
   ... | tri≈ ¬a b₁ ¬c = lem00 j refl where 
       lem00 : (m : ℕ) → m ≡ j → (bi k ) ≤  (b m) 
       lem00 m m=j with Data.Nat.<-cmp m (suc i)
       ... | tri< a ¬b ¬c = lem03 where  
           lem04 : m n≤ i
           lem04 =  px≤py a
           lem03 : (bi k ) ≤  (Bni2.b obni m) 
           lem03 with  p∨¬p ( (  (Bni2.b (Bn1 L PB an i bn0) i) x (∧An L PB an i)) ≈ b0 )
           ... | case1 eq3 = begin
              ((Bni2.b obni i) x ( - (AAn.a (b-ai→a1 L PB an i (Bni2.b obni i ) (Bni2.bnz obni i) eq3 ) )))   
                  ≤⟨ Bni2.bin2-lem00 obni (Bni2.b obni i) ( - (AAn.a (b-ai→a1 L PB an i (Bni2.b obni i ) (Bni2.bnz obni i) eq3 ) ))  ⟩ 
              ( Bni2.b obni i)   ≤⟨  Bni2.bmono obni _ lem04 ⟩ 
              ( Bni2.b obni m)   ∎ where
                 open BA≤-Reasoning (ba PB)
           ... | case2 ne3 = begin
              ((Bni2.b obni i) x (∧An L PB an i)) ≤⟨ Bni2.bin2-lem00 obni (Bni2.b obni i)  (∧An L PB an i)  ⟩ 
              ( Bni2.b obni i)   ≤⟨  Bni2.bmono obni _ lem04 ⟩ 
              ( Bni2.b obni m) ∎ where
                 open BA≤-Reasoning (ba PB)
       ... | tri≈ ¬a b₂ ¬c = lem03 where 
           lem03 : (bi k ) ≤  (bi m)
           lem03 = ≈→≤ {bi k} {bi m} (bi-cong _ _ (trans b₁ (sym b₂)) )
       ... | tri> ¬a ¬b c = ⊥-elim ( nat-≤> (subst (λ k → k n≤ suc i) (sym m=j) lt)  c ) 
   ... | tri> ¬a ¬b c = ⊥-elim ( ¬b k=sj ) 


get-b : (L : HOD)  (PB : HODBooleanAlgebra L ) (an : AN L PB ) → (bn0 :  Bni L PB an ) → ( i : ℕ) → Bni2 L PB an bn0 i → Bni L PB an 
get-b L PB an bn0 i bni = record { b = Bni2.b bni i ; bnz = Bni2.bnz bni i } where
   open BooleanAlgebra (ba PB)
   open IsBooleanAlgebra (BooleanAlgebra.isBooleanAlgebra (ba PB))

bni2unique : (L : HOD) → (PB : HODBooleanAlgebra L ) → (an : AN L PB ) → (bn0 : Bni L PB an) 
  → (i j k : ℕ) → i Data.Nat.≤  j → (bi :  Bni2 L PB an bn0 i)→ (bj :  Bni2 L PB an bn0 j)
  → k Data.Nat.≤ i → BooleanAlgebra._≈_ (ba PB) (Bni2.b bi k) (Bni2.b bj k )
bni2unique L PB an bn0 i zero k i≤j bi bj k≤i = lem01 where 
   open BooleanAlgebra (ba PB)
   open IsBooleanAlgebra (BooleanAlgebra.isBooleanAlgebra (ba PB))
   lem00 : k ≡ zero
   lem00 with Data.Nat.<-cmp k zero
   ... | tri< a ¬b ¬c = ⊥-elim (nat-≤> z≤n a)
   ... | tri≈ ¬a b ¬c = b
   ... | tri> ¬a ¬b c = ⊥-elim (nat-≤> c (≤-<-trans k≤i (s≤s i≤j) ))
   lem01 : (Bni2.b bi k) ≈ (Bni2.b bj k )
   lem01 = o≡→== (cong elt (trans ( Bni2.bzero bi _ lem00 ) (sym ( Bni2.bzero bj _ lem00 )) )  )
bni2unique L PB an bn0 i (suc j) k i≤j bi bj k≤i = lem00 k k≤i where 
   open BooleanAlgebra (ba PB)
   open IsBooleanAlgebra (BooleanAlgebra.isBooleanAlgebra (ba PB))
   lem02 :  (k : ℕ) → k Data.Nat.≤ i → Bni2.b bi k ≈ Bni2.b bj k 
   lem02 k le = bni2unique L PB an bn0 i _ _ i≤j bi bj le
   lem00 : (m : ℕ) → m Data.Nat.≤ i → Bni2.b bi m ≈  Bni2.b bj m
   lem00 zero m≤i = o≡→== (cong elt (trans ( Bni2.bzero bi _ refl ) (sym ( Bni2.bzero bj _ refl ))  ))
   lem00 (suc m) m≤i = lem04 where
      lem03 : Bni2.b bi m ≈  Bni2.b bj m
      lem03 = lem00 m (Data.Nat.Properties.≤-trans a≤sa m≤i) 
      lem04 : Bni2.b bi (suc m) ≈ Bni2.b bj (suc m)
      lem04 with p∨¬p ( (  (Bni2.b bj m) x (∧An L PB an m)) ≈ b0 )
      ... | case1 eq = lem05 where 
            lem06 :  ((Bni2.b bi m) x (∧An L PB an m)) ≈ b0 
            lem06 = btrans {(Bni2.b bi m) x (∧An L PB an m)} {(Bni2.b bj m) x (∧An L PB an m)} {b0} 
                (x-resp  {∧An L PB an m} {∧An L PB an m} {Bni2.b bi m} {Bni2.b bj m} (brefl {∧An L PB an m} ) lem03 ) eq
            lem05 : Bni2.b bi (suc m) ≈ Bni2.b bj (suc m)
            lem05 = begin 
               Bni2.b bi (suc m)   ≈⟨ Bni2.eq1 bi  m m≤i lem06 ⟩ 
               (Bni2.b bi m) x ( - (AAn.a (b-ai→a1 L PB an m (Bni2.b bi m) (Bni2.bnz bi m ) lem06 ) ))   ≈⟨ x-resp 
                     { - (AAn.a (b-ai→a1 L PB an m (Bni2.b bi m) (Bni2.bnz bi m ) lem06 ) )} 
                     { - (AAn.a (b-ai→a1 L PB an m (Bni2.b bj m) (Bni2.bnz bj m ) eq ) )}  {Bni2.b bi m} {Bni2.b bj m}
                   (neg-resp {AAn.a (b-ai→a1 L PB an m (Bni2.b bi m) (Bni2.bnz bi m ) lem06)} {AAn.a (b-ai→a1 L PB an m (Bni2.b bj m) (Bni2.bnz bj m ) eq)} 
                       (ai→a1-cong L PB an _ _ (Bni2.b bi m) (Bni2.b bj m) (Bni2.bnz bi m ) (Bni2.bnz bj m ) lem06 eq refl )) lem03 ⟩
               (Bni2.b bj m) x ( - (AAn.a (b-ai→a1 L PB an m (Bni2.b bj m) (Bni2.bnz bj m ) eq ) ))   
                  ≈⟨ ==-sym ( Bni2.eq1 bj m (Data.Nat.Properties.≤-trans m≤i i≤j) eq ) ⟩ 
               Bni2.b bj (suc m)  ∎ where
                  open EqR bSetoid
      ... | case2 ne = lem05 where
            lem06 :  ¬ ( ((Bni2.b bi m) x (∧An L PB an m)) ≈ b0  )
            lem06 eq = ⊥-elim ( ne (btrans {(Bni2.b bj m) x (∧An L PB an m)} {(Bni2.b bi m) x (∧An L PB an m)} {b0} 
                (x-resp {∧An L PB an m} {∧An L PB an m} {Bni2.b bj m} {Bni2.b bi m}  (brefl {∧An L PB an m}) (bsym {Bni2.b bi m} {Bni2.b bj m} lem03) ) eq ))
            lem05 : Bni2.b bi (suc m) ≈ Bni2.b bj (suc m)
            lem05 = begin 
               Bni2.b bi (suc m)   ≈⟨ Bni2.eq2 bi  m m≤i lem06 ⟩ 
               (Bni2.b bi m) x (∧An L PB an m) ≈⟨ x-resp { ∧An L PB an m } { ∧An L PB an m } {Bni2.b bi m} {Bni2.b bj m} ==-refl  lem03 ⟩
               (Bni2.b bj m) x (∧An L PB an m) ≈⟨ ==-sym ( Bni2.eq2 bj m (Data.Nat.Properties.≤-trans m≤i i≤j) ne ) ⟩ 
               Bni2.b bj (suc m)  ∎ where
                  open EqR bSetoid

record BnR (L : HOD) (PB : HODBooleanAlgebra L ) (an : AN L PB ) (bni : Bni L PB an) (x : Ordinal) : Set n where
    field
       i : ℕ 
       bx :  odef (OS PB) x
       bn≤x :  (*  (elt (Bni.b (get-b L PB an bni i (Bn1 L PB an i bni ) )) ))  ⊆  (* x)

BnHOD : (L : HOD) → (PB : HODBooleanAlgebra L ) → (an : AN L PB ) (bni : Bni L PB an) → HOD
BnHOD L PB an bni = record { od = record { def = λ x → BnR L PB an bni x } ; odmax = & (OS PB) ; <odmax =  λ lt → odef< (BnR.bx lt)  } 

BnHOD⊆L : (L : HOD) → (PB : HODBooleanAlgebra L ) → (an : AN L PB ) (bni : Bni L PB an)  → BnHOD L PB an bni ⊆ Power L
BnHOD⊆L L PB an bni {x} lt z xz = OS⊆PL PB (BnR.bx lt)  _ xz 

bni-mono : (L : HOD) → (PB : HODBooleanAlgebra L ) → (an : AN L PB ) (bni : Bni L PB an) → (i j : ℕ) → i Data.Nat.≤ j
         → (* (elt (Bni2.b (Bn1 L PB an j  bni) j ))) ⊆  (* (elt (Bni2.b (Bn1 L PB an i bni) i  )))
bni-mono L PB an bni i j i≤j {x} ej = eq← lem01 ( lem00 ej ) where
    open BooleanAlgebra (ba PB)
    open IsBooleanAlgebra (BooleanAlgebra.isBooleanAlgebra (ba PB))
    lem01 : (Bni2.b (Bn1 L PB an i  bni) i) ≈ (Bni2.b (Bn1 L PB an j bni) i)  
    lem01 = bni2unique L PB an bni i j i i≤j (Bn1 L PB an i bni) (Bn1 L PB an j bni) refl-≤ 
    lem00 : (* (elt (Bni2.b (Bn1 L PB an j  bni) j ))) ⊆  (* (elt (Bni2.b (Bn1 L PB an j bni) i  )))
    lem00 = ≤→⊆ PB {(Bni2.b (Bn1 L PB an j  bni) j )} {Bni2.b (Bn1 L PB an j bni) i} ( Bni2.bmono (Bn1 L PB an j bni) _ i≤j  )

BnFilter : (L : HOD) → (PB : HODBooleanAlgebra L ) → (an : AN L PB ) (bni : Bni L PB an) → Filter  {OS PB} {L} (OS⊆PL PB) 
BnFilter L PB an bni = record { filter = BnHOD L PB an bni ; f⊆L =  BnR.bx  ; filter1 = f1 ; filter2 = f2 } where
   f1 :  {p q : HOD} → OS PB ∋ q → BnHOD L PB an bni ∋ p → p ⊆ q → BnHOD L PB an bni ∋ q 
   f1 {p} {q} oq bp p⊆q = record { i = BnR.i bp ; bx = oq ; bn≤x = lem00 } where
      lem01 : { x : Ordinal} → odef ( * ( elt (Bni.b (get-b L PB an bni (BnR.i bp) (Bn1 L PB an (BnR.i bp) bni ) ) ) ) ) x →  odef p x
      lem01 lt = eq→  *iso (BnR.bn≤x bp lt)
      lem00 : { x : Ordinal} → odef ( * ( elt (Bni.b (get-b L PB an bni (BnR.i bp) (Bn1 L PB an (BnR.i bp) bni ) ) ) ) ) x →  odef (* (& q)) x
      lem00 lt = eq← *iso ( p⊆q (lem01 lt ))
   f2 :  {p q : HOD} → BnHOD L PB an bni ∋ p → BnHOD L PB an bni ∋ q → OS PB ∋ (p ∩ q) → BnHOD L PB an bni ∋ (p ∩ q)
   f2 {p} {q} bp bq p∩q with Data.Nat.<-cmp (BnR.i bp) (BnR.i bq)
   ... | tri< a ¬b ¬c = record { i = BnR.i bq ; bx = p∩q ; bn≤x = lem01 } where
      lem01 : { x : Ordinal} → odef ( * ( elt (Bni.b (get-b L PB an bni (BnR.i bq) (Bn1 L PB an (BnR.i bq) bni ) ) ) ) ) x →  odef (* ( & (p ∩ q))) x
      lem01 {x} lt = eq← *iso ⟪ eq→  *iso (BnR.bn≤x bp lem02 ) , eq→  *iso (BnR.bn≤x bq lt )  ⟫  where
          lem02 : odef ( * ( elt (Bni.b (get-b L PB an bni (BnR.i bp) (Bn1 L PB an (BnR.i bp) bni ) ) ) ) ) x 
          lem02 = bni-mono L PB an bni (BnR.i bp) (BnR.i bq) (Data.Nat.Properties.≤-trans a≤sa a )  lt 
   ... | tri≈ ¬a b ¬c = record { i = BnR.i bp ; bx = p∩q ; bn≤x = λ lt → eq← *iso ⟪ eq→  *iso (BnR.bn≤x bp lt  ) 
           , eq→  *iso (BnR.bn≤x bq ( bni-mono L PB an bni (BnR.i bq) (BnR.i bp)  (refl-≤≡  (sym b))  lt  ))  ⟫ } 
   ... | tri> ¬a ¬b c = record { i = BnR.i bp ; bx = p∩q ; bn≤x = lem01 } where
      lem01 : { x : Ordinal} → odef ( * ( elt (Bni.b (get-b L PB an bni (BnR.i bp) (Bn1 L PB an (BnR.i bp) bni ) ) ) ) ) x →  odef (* ( & (p ∩ q))) x
      lem01 {x} lt = eq← *iso ⟪ eq→  *iso (BnR.bn≤x bp lt) , eq→  *iso (BnR.bn≤x bq lem02 )  ⟫  where
          lem02 : odef ( * ( elt (Bni.b (get-b L PB an bni (BnR.i bq) (Bn1 L PB an (BnR.i bq) bni ) ) ) ) ) x 
          lem02 = bni-mono L PB an bni (BnR.i bq) (BnR.i bp) (Data.Nat.Properties.≤-trans a≤sa c )  lt 

