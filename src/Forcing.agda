{-# OPTIONS --cubical-compatible --safe #-}
open import Level renaming ( suc to Suc ; zero to Zero ; _⊔_ to _n⊔_ )
open import Ordinals
open import logic
open import Relation.Nullary

--
-- 選択公理と数学　田中尚夫 190 page
--
--
--

import HODBase
import OD
open import Relation.Nullary
module Forcing where

open import  Relation.Binary.PropositionalEquality hiding ( [_] )
open import Relation.Binary.Definitions -- hiding ( _⇔_ )
open import Data.Empty
import OrdUtil
import ODUtil
open import logic
open import nat

open import Ordinals
import filter

open import Relation.Nullary
-- open import Relation.Binary hiding ( _⇔_ )
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Data.Nat renaming ( _<_  to _n<_  ; _+_ to _n+_ ; _≤_ to _n≤_ )
open import Data.Nat.Properties
open import BoolAlgebra

import Relation.Binary.Reasoning.Setoid as EqHOD

module MBA {n : Level } (O : Ordinals {n} ) (HODAxiom : HODBase.ODAxiom O)  (ho< : OD.ODAxiom-ho< O HODAxiom )
           (AC : OD.AxiomOfChoice O HODAxiom ) where

    open Ordinals.Ordinals  O
    open Ordinals.IsOrdinals isOrdinal
    open HODBase.ODAxiom HODAxiom
    open OD O HODAxiom
    open import ODC O HODAxiom AC as ODC

    open AxiomOfChoice AC
    open OrdUtil O
    open ODUtil O HODAxiom  ho<
    open HODBase.HOD
    open _∧_
    open _∨_
    open Bool
    open  HODBase._==_
    open import ZProduct O HODAxiom ho<
    open import filter O HODAxiom ho< AC

    open import bijection hiding ( b1 )

    -- LDec : (L : HOD) (P : HOD) → P ⊆ L → (x : HOD) → Dec0 (x ∈ P)
    -- LDec L P _ x = ∋-p P x

    -- open import Data.Nat
    open import ZEquiv O HODAxiom ho<

    open HODElement
    import BAlgebra

    open Bijection
    -- 補題 23.1 Bの任意の要素 b ≠ 0 に対して、bを含む M-生成超フィルターが存在する

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
       0<b→¬b≈od∅ : {a : HODElement (HBAR.OS H)} → b0 < a → ¬ ( (* (elt a))  =h= od∅ )
       0<b→¬b≈od∅ {a} 0<a eq = ⊥-elim (proj1 0<a (==-sym (==-trans eq (==-sym o∅==od∅ ) ) ) )


    record CM : Set (Suc (Suc n)) where
      field
          countable : Bijection ℕ (Ordinals.Ordinal O)

module MBB {n : Level } (O : Ordinals {n} ) (HODAxiom : HODBase.ODAxiom O)  (ho< : OD.ODAxiom-ho< O HODAxiom )
           (AC : OD.AxiomOfChoice O HODAxiom ) where

    open Ordinals.Ordinals  O
    open Ordinals.IsOrdinals isOrdinal
    open HODBase.ODAxiom HODAxiom
    open OD O HODAxiom
    open import ODC O HODAxiom AC as ODC

    open AxiomOfChoice AC
    open OrdUtil O
    open ODUtil O HODAxiom  ho<
    open HODBase.HOD
    open _∧_
    open _∨_
    open Bool
    open  HODBase._==_
    open import ZProduct O HODAxiom ho<
    open import filter O HODAxiom ho< AC

    open import bijection hiding ( b1 )

    -- LDec : (L : HOD) (P : HOD) → P ⊆ L → (x : HOD) → Dec0 (x ∈ P)
    -- LDec L P _ x = ∋-p P x

    -- open import Data.Nat
    open import ZEquiv O HODAxiom ho<

    open HODElement
    import BAlgebra

    open Bijection
    open MBA O HODAxiom ho< AC
    open HODBooleanAlgebra
    --
    -- a_n  = ∧ An (An ≠ ∅ )
    --
    --

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

    -- M は可算なので整列可能
    --
    -- { A ∈  M : ∅ ≠ A ⊆ B } = { A0 , A1, A2, ... An }
    --
    An : (L : HOD) → (PB : HODBooleanAlgebra L ) → AN L PB → HOD
    An L PB an = record { od = record { def = λ x → OAn L PB an x } ; odmax = & (Power (BAlgebra.HBAR.OS (H PB))) ; <odmax = λ lt → odef< (OAn.pa lt) }

    PAn : (L : HOD) → (PB : HODBooleanAlgebra L ) → AN L PB → ℕ → BPred (HODBooleanAlgebra.B PB) (ba PB)
    PAn L PB an i = record { pred = λ p → odef (* (elt (AN.imap an i))) (elt p)
       ; pcong = λ x y eq → ⟪ ( λ lt → subst (λ k → odef (* (elt (AN.imap an i))) k ) (*=h=*→≡ eq) lt )
          , ( λ lt → subst (λ k → odef (* (elt (AN.imap an i))) k ) (sym (*=h=*→≡ eq))  lt )  ⟫ }

    -- BはM完備なので最小上界が存在する
    --
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

    --
    --   b_0 = b
    --
    --   b_n+1 if ( bn ∙ an ≠ 0 ) then
    --     b_n+1 = bn ∙ an
    --   else
    --     bn - a ( An ∋ a such that a = bn- a > 0 )

    record Bni (L : HOD)  (PB : HODBooleanAlgebra L ) (an : AN L PB )  : Set n where
       open BooleanAlgebra (ba PB)
       open IsBooleanAlgebra (BooleanAlgebra.isBooleanAlgebra (ba PB))
       field
          b : HODBooleanAlgebra.B PB
          bnz : b0 < b

    --  if ( bn ∙ an = 0 ) then we have   An ∋ a such that a = bn- a > 0
    --
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

    --
    -- induction of b is not simple, we construct a record which represents the induction of b
    --   function Bni2.b is unique on the induciton Bn1 which is a property of Bni2
    --
    -- we can prove monotonity of b in Bni2

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
       bcong : (i j : ℕ) → i ≡ j →  b i ≈ b j   -- uniqueness of b on the induction Bn1
       bcong i j eq = subst ( λ k → b i ≈ b k ) eq ( brefl {b i} )
       bin2-lem00 : (a b : HODBooleanAlgebra.B PB) → (a x b) ≤ a
       bin2-lem00 a b = begin
          (a x b) x a ≈⟨ x-sym {a x b} {a} ⟩
          a x (a x b)  ≈⟨ x-assoc {a} {a} {b} ⟩
          (a x a) x b  ≈⟨ x-resp {b} {b} {a x a} {a} (brefl {b} ) (x-idem  {a}) ⟩
          a x b ∎ where open EqR bSetoid
       bzero≈  : ( j : ℕ) → j ≡ zero → b j ≈ Bni.b bn0
       bzero≈ j eq = o≡→== (cong elt (bzero j eq))

    --
    -- induction of b, such as Bni2
    --

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

    --
    -- uniqueness of b is proved without Bn1, it comes from Bni2
    --

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

    --
    -- 生成フィルターを集合として作る
    --

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

    BnFProper : (L : HOD) → (PB : HODBooleanAlgebra L ) → (an : AN L PB ) (bni : Bni L PB an) → ¬ (odef ( Filter.filter (BnFilter L PB an bni)) (& od∅ ))
    BnFProper L PB an bni record { i = i ; bx = bx ; bn≤x = bn≤x } = ⊥-elim (¬x<0 (eq→ *iso (bn≤x lem04 ))) where
      lem05 : HOD
      lem05 = * (elt (Bni.b (get-b L PB an bni i (Bn1 L PB an i bni ) ) ) )
      lem06 : ¬ (od lem05 == od od∅)
      lem06 = 0<b→¬b≈od∅ PB {(Bni.b (get-b L PB an bni i (Bn1 L PB an i bni ) ) )} (Bni2.bnz (Bn1 L PB an i bni ) i )
      lem04 : odef lem05 (& ( minimal lem05 lem06 ))
      lem04 = x∋minimal lem05 lem06

    --
    -- BnFilter を超フィルターに Zorn の補題で拡張する
    --

    open import maximum-filter O HODAxiom ho< AC

    maxf   : (L : HOD) → (PB : HODBooleanAlgebra L ) → (an : AN L PB ) (bni : Bni L PB an)
       → MaximumFilter (OS⊆PL PB) (BnFilter L PB an bni)
    maxf  L PB an bni  = F→Maximum {OS PB} {L} (OS⊆PL PB) (o∩ PB) (BnFilter L PB an bni ) lem00 lem01 (BnFProper L PB an bni) where
       lem03 : od∅ ⊆ OS PB
       lem03 lt = ⊥-elim (¬x<0 lt)
       lem00 : o∅ o< & (OS PB)   -- yes we have OS PB ∋ od∅
       lem00 = ∈∅< (o∪ PB {od∅} lem03 )
       lem01 : odef (Filter.filter (BnFilter L PB an bni)) (elt (Bni.b bni))
       lem01 = record { i = zero ; bx = A∋elt (Bni.b bni) ; bn≤x = λ lt → lt  }

    mf     : (L : HOD) → (PB : HODBooleanAlgebra L ) → (an : AN L PB ) (bni : Bni L PB an) → Filter  {OS PB} {L} (OS⊆PL PB)
    mf L PB an bni  =  MaximumFilter.mf (maxf L PB an bni)

    ultraf : (L : HOD) → (PB : HODBooleanAlgebra L ) → (an : AN L PB ) (bni : Bni L PB an) → ultra-filter ( mf L PB  an bni )
    ultraf L PB an bni  = F→ultra {OS PB} {L} (OS⊆PL PB) (o∩ PB) (BnFilter L PB an bni)  lem00 lem01 (BnFProper L PB an bni)  where
       lem03 : od∅ ⊆ OS PB
       lem03 lt = ⊥-elim (¬x<0 lt)
       lem00 : o∅ o< & (OS PB)   -- yes we have OS PB ∋ od∅
       lem00 = ∈∅< (o∪ PB {od∅} lem03 )
       lem01 : odef (Filter.filter (BnFilter L PB an bni)) (elt (Bni.b bni))
       lem01 = record { i = zero ; bx = A∋elt (Bni.b bni) ; bn≤x = λ lt → lt  }

module MBU {n : Level } (O : Ordinals {n} ) (HODAxiom : HODBase.ODAxiom O)  (ho< : OD.ODAxiom-ho< O HODAxiom )
           (AC : OD.AxiomOfChoice O HODAxiom ) where
    open Ordinals.Ordinals  O
    open Ordinals.IsOrdinals isOrdinal
    open HODBase.ODAxiom HODAxiom
    open OD O HODAxiom
    open import ODC O HODAxiom AC as ODC

    open AxiomOfChoice AC
    open OrdUtil O
    open ODUtil O HODAxiom  ho<
    open HODBase.HOD
    open _∧_
    open _∨_
    open Bool
    open  HODBase._==_
    open import ZProduct O HODAxiom ho<
    open import filter O HODAxiom ho< AC

    open import bijection hiding ( b1 )

    -- LDec : (L : HOD) (P : HOD) → P ⊆ L → (x : HOD) → Dec0 (x ∈ P)
    -- LDec L P _ x = ∋-p P x

    -- open import Data.Nat
    open import ZEquiv O HODAxiom ho<

    open HODElement
    import BAlgebra

    open Bijection

    open MBA O HODAxiom ho< AC
    open HODBooleanAlgebra

    --
    -- M_0^(B) = 0
    -- M_(α+1)^(B) = { x : Func x ∧ dom(x) ⊆ M_α^(B) ∧ ran(x) ⊆ B }
    -- M_(α)^(B) =  ∪ { M_β^(B) : β < α }  (α ∈  limit)
    --
    -- M^(B) =  ∪ { M_α^(B) : α ∈ (Ordinal ∩ M) }
    --
    -- v 0 = 0
    -- v x = { <  v y , 1 > : y ∈ x }   ¬ ( x =  0) }
    --
    -- i_G  : ? → ?
    -- i_G 0 = 0
    -- i_G x = { i_G y : y( x) ∈ G }
    --
    --

    --
    -- ブール値モデルの宇宙
    --
    --
    --   Somehthing lik (Ordinal → Bool Algebra ) * → Bool Algebra
    --

    record FuncsS  (A B : HOD) (x : Ordinal) : Set n where
       field
         dom cod : Ordinal
         dom⊆A : (* dom) ⊆ A
         cod⊆B : (* cod) ⊆ B
         is-func : odef (Funcs (* dom) (* cod)) x

    FuncsSHOD : (A B : HOD) → HOD
    FuncsSHOD A B = record { od = record { def = λ x → FuncsS A B x } ; odmax = osuc (& (ZFP A B)) ; <odmax
            = λ {y} px → lem02 px } where
       lem00 : (x y : Ordinal) → (lt : FuncsS A B x) → odef (* x) y → odef (ZFP (* (FuncsS.dom lt)) (* (FuncsS.cod lt) )) y
       lem00 x y lt xy = Func<ZFP (* (FuncsS.dom lt)) (* (FuncsS.cod lt) ) (FuncsS.is-func lt)  xy
       lem01 : (x : Ordinal) → (lt : FuncsS A B x) → ZFP(* (FuncsS.dom lt)) (* (FuncsS.cod lt) ) ⊆ ZFP A B
       lem01 x lt lt2 = proj1 (ZFP⊆  (FuncsS.dom⊆A lt) ) (proj2 (ZFP⊆  (FuncsS.cod⊆B lt) )  lt2 )
       lem02 : {y : Ordinal} → FuncsS A B y → y o< osuc (& (ZFP A B))
       lem02 {y} lt = begin
            y   ≤⟨ subst ( λ k → k o≤ (& (ZFP _ _)) ) &iso (⊆→o≤ (lem00 _ _ lt) )  ⟩
            & (ZFP (* (FuncsS.dom lt)) (* (FuncsS.cod lt)))  ≤⟨ ⊆→o≤ ( lem01 _ lt) ⟩
            & (ZFP A B)  ∎
              where open  o≤-Reasoning

    record BMOrd  (y : Ordinal) (M : (x : Ordinal) → x o< y → Ordinal ) (z : Ordinal)   : Set n where
        field
           value : Ordinal
           value<y : value o< y
           Mv=x : M value value<y ≡ z

    BUnion : (y : Ordinal) (M : (x : Ordinal ) → x o< y → Ordinal ) (max : Ordinal)
        (is-max : (x : Ordinal) → (x<y : x o< y ) → M x x<y o< max ) → HOD
    BUnion y M max is-max = record { od = record { def = λ z → BMOrd y M z } ; odmax = max ; <odmax = lem00 }  where
        lem00 : {z : Ordinal} → BMOrd y M z → z o< max
        lem00 {z} mo = subst (λ k → k o< _ ) (BMOrd.Mv=x mo) ( is-max _ (BMOrd.value<y mo))

    record BAU (L : HOD)  (PB : HODBooleanAlgebra L ) (x : Ordinal) : Set n where
      field
         f : (y : Ordinal) → y o≤ x →  Ordinal
         fcong : (a b : Ordinal) → (a≤x : a o≤ x) (b≤x : b o≤ x) → a ≡ b → f a a≤x ≡ f b b≤x
         fmax : Ordinal
         has-fmax : (y : Ordinal) → (y≤x : y o≤ x ) → f y y≤x o< fmax
         fp0 : (y : Ordinal) → y ≡ o∅  → (y≤x : y o≤ x) → f y y≤x ≡ o∅
         fp-prev : (y z : Ordinal) → (y=oz : y ≡ osuc z ) → (z≤x : z o≤ x)  → (y≤x : y o≤ x )
            → f y y≤x  ≡  & ( FuncsSHOD (* (f z z≤x )) (OS PB) )
         fp-lim : (y : Ordinal) → ((z : Ordinal) → ¬ ( y ≡ osuc z)) → o∅ o< y → (y≤x : y o≤ x)
            → f y y≤x ≡  & ( BUnion y (λ z z<y → f z (ordtrans z<y y≤x )) fmax (λ z z<y → has-fmax z (ordtrans z<y y≤x ) ) )
         -- we should have monotonicity
         -- fmono : (a b : Ordinal) → (a<x : a o< x) (b<x : b o< x) → a o< b → f a a<x o< f b b<x

    --
    -- Assumption : we have enough ordinal to have function hierarchy
    --
    record BFlim (L : HOD)  (PB : HODBooleanAlgebra L ) (y : Ordinal) : Set n where
      field
         bfmax : (bau : (x : Ordinal) → x o< y → BAU L PB x) → Ordinal
         is-bfmax : (x : Ordinal) → (x<y : x o< y )
            → (bau : (x : Ordinal) → x o< y → BAU L PB x)
            → (z : Ordinal) → (z≤x : z o≤ x) → BAU.f (bau x x<y ) z z≤x  o< bfmax bau

    BAU-unique : (L : HOD)  (PB : HODBooleanAlgebra L ) → {x y z : Ordinal} → (x<y : x o< y) → (bx : BAU L PB x) → (by : BAU L PB y )
       → (z≤x : z o≤ x) → BAU.f bx z z≤x ≡ BAU.f by z (ordtrans z≤x (osucc x<y))
    BAU-unique L PB {x} {y} {z} x<y bx by z≤x = Ordinals.inOrdinal.TransFinite0 O
             {λ z → (z≤x : z o≤ x) → BAU.f bx z z≤x ≡ BAU.f by z (ordtrans z≤x (osucc x<y)) } ind  z z≤x where
        ind : (z : Ordinal) → ((y₁ : Ordinal) → y₁ o< z → (z≤x₁ : y₁ o≤ x) → BAU.f bx y₁ z≤x₁ ≡ BAU.f by y₁ (ordtrans z≤x₁ (osucc x<y))) →
                (z≤x : z o≤ x) → BAU.f bx z z≤x ≡ BAU.f by z (ordtrans z≤x (osucc x<y))
        ind z prev z≤x with trio< z o∅
        ... | tri< a ¬b ¬c = ⊥-elim ( ¬x<0 a)
        ... | tri≈ ¬a b ¬c = trans ( BAU.fp0 bx _ b z≤x ) (sym ( BAU.fp0 by _ b (ordtrans z≤x (osucc x<y) ) ) )
        ... | tri> ¬a ¬b c with Oprev-p  z
        ... | yes0 p =  trans ( BAU.fp-prev bx z _ (sym ( Oprev.oprev=x p )) (ordtrans lem08 <-osuc)  z≤x )
                (trans (cong (&) lem01 )  (sym ( BAU.fp-prev by z _  (sym ( Oprev.oprev=x p )) lem09  (ordtrans z≤x (osucc x<y) )  ))) where
            lem08 : Oprev.oprev p o< x
            lem08 = osucprev ( begin
                osuc (Oprev.oprev p)  ≡⟨ Oprev.oprev=x p ⟩
                z ≤⟨ z≤x ⟩
                x ∎  )
                where open o≤-Reasoning
            lem07 : Oprev.oprev p o< z
            lem07 = osucprev ( begin
              osuc  (Oprev.oprev p)  ≡⟨ Oprev.oprev=x p ⟩
              z ∎  )
                where open o≤-Reasoning
            lem09 :  Oprev.oprev p o< osuc y
            lem09  = ordtrans (ordtrans lem08 <-osuc) (osucc x<y)
            lem00 : BAU.f bx (Oprev.oprev p) (ordtrans lem08 <-osuc) ≡ BAU.f by (Oprev.oprev p) (ordtrans (ordtrans lem08 <-osuc) (osucc x<y))
            lem00 = prev _ lem07 (ordtrans lem08 <-osuc)
            lem01 : FuncsSHOD (* (BAU.f bx (Oprev.oprev p) (ordtrans lem08 <-osuc) )) (OS PB) ≡ FuncsSHOD (* (BAU.f by (Oprev.oprev p) lem09 )) (OS PB)
            lem01 = cong ( λ k → FuncsSHOD (* k) (OS PB) ) lem00
        ... | no0 ¬p =  trans lem00 (trans lem03 (sym lem01)) where
            nbx : HOD
            nbx = BUnion z (λ x x<z → BAU.f bx x (ordtrans x<z z≤x)) (BAU.fmax bx) (λ x x<z → BAU.has-fmax bx x (ordtrans x<z z≤x) )
            nby : HOD
            nby = BUnion z (λ x x<z → BAU.f by x (ordtrans x<z (ordtrans z≤x (osucc x<y)) )) (BAU.fmax by) (λ x x<z → BAU.has-fmax by x (ordtrans x<z (ordtrans z≤x (osucc x<y)) ) )
            lem00 : BAU.f bx z z≤x ≡ & nbx
            lem00 = BAU.fp-lim  bx _  (λ w eq → ¬p (record { oprev = w ; oprev=x = sym eq } )) c z≤x
            lem01 : BAU.f by z (ordtrans z≤x (osucc x<y) ) ≡ & nby
            lem01 = BAU.fp-lim  by _  (λ w eq → ¬p (record { oprev = w ; oprev=x = sym eq } )) c (ordtrans z≤x (osucc x<y) )
            lem04 : (w  : Ordinal) → (w≤z : w o< z) → (w≤x : w o≤ x) → BAU.f bx w w≤x ≡ BAU.f by w (ordtrans w≤x (osucc x<y) )
            lem04 w lt le = prev _ lt le
            lem05 :  {w : Ordinal} → odef nbx w → odef nby w
            lem05 {w} bxw = record { value = BMOrd.value bxw ; value<y = lem07  ; Mv=x
                = trans (sym (trans (lem04 _ lem07 (ordtrans lem07 z≤x )) (BAU.fcong by _ _ _ _ refl ) ))  (BMOrd.Mv=x bxw)   } where
                  lem07 : BMOrd.value bxw  o< z
                  lem07 = BMOrd.value<y bxw
            lem06 :  {w : Ordinal} → odef nby w → odef nbx w
            lem06 {w} byw = record { value = BMOrd.value byw ; value<y = lem07 ; Mv=x
                = trans (trans (lem04 _ lem07 (ordtrans (BMOrd.value<y byw) z≤x )) (BAU.fcong by _ _ _ _ refl ) )  (BMOrd.Mv=x byw)   }  where
                  lem07 : BMOrd.value byw  o< z
                  lem07 = BMOrd.value<y byw
            lem03 : & nbx ≡ & nby
            lem03 = ==→o≡ record { eq→  = lem05 ; eq←  = lem06 }

    BAU-unique0 : (L : HOD)  (PB : HODBooleanAlgebra L ) → {x z : Ordinal} → (bx by : BAU L PB x)
       → (z≤x : z o≤ x) → BAU.f bx z z≤x ≡ BAU.f by z z≤x
    BAU-unique0 L PB {x} {z} bx by z≤x = Ordinals.inOrdinal.TransFinite0 O
             {λ z → (z≤x : z o≤ x) → BAU.f bx z z≤x ≡ BAU.f by z z≤x  } ind  z z≤x where
        ind : (z : Ordinal) → ((y₁ : Ordinal) → y₁ o< z → (z≤x₁ : y₁ o≤ x) → BAU.f bx y₁ z≤x₁ ≡ BAU.f by y₁ z≤x₁) →
                (z≤x : z o≤ x) → BAU.f bx z z≤x ≡ BAU.f by z z≤x
        ind z prev z≤x with trio< z o∅
        ... | tri< a ¬b ¬c = ⊥-elim ( ¬x<0 a)
        ... | tri≈ ¬a b ¬c = trans ( BAU.fp0 bx _ b z≤x ) (sym ( BAU.fp0 by _ b z≤x  ) )
        ... | tri> ¬a ¬b c with Oprev-p  z
        ... | yes0 p =  trans ( BAU.fp-prev bx z _ (sym ( Oprev.oprev=x p )) lem08  z≤x )
                (trans (cong (&) (cong ( λ k → FuncsSHOD (* k) (OS PB) ) lem00) )  (sym ( BAU.fp-prev by z _  (sym ( Oprev.oprev=x p )) lem08  z≤x  )))  where
            lem08 : Oprev.oprev p o< osuc x
            lem08 = begin
                Oprev.oprev p  <⟨ <-osuc ⟩
                osuc (Oprev.oprev p)  ≡⟨ Oprev.oprev=x p ⟩
                z ≤⟨ z≤x ⟩
                x ∎
                where open o≤-Reasoning
            lem07 : Oprev.oprev p o< z
            lem07 = osucprev ( (subst (λ k → k o< osuc z) (sym (Oprev.oprev=x p)) <-osuc  ) )
            lem00 : BAU.f bx (Oprev.oprev p) lem08  ≡ BAU.f by (Oprev.oprev p) lem08
            lem00 = prev _  lem07 lem08
        ... | no0 ¬p =  trans lem00 (trans lem03 (sym lem01)) where
            nbx : HOD
            nbx = BUnion z (λ x x<z → BAU.f bx x (ordtrans x<z z≤x)) (BAU.fmax bx) (λ x x<z → BAU.has-fmax bx x (ordtrans x<z z≤x) )
            nby : HOD
            nby = BUnion z (λ x x<z → BAU.f by x (ordtrans x<z z≤x)) (BAU.fmax by) (λ x x<z → BAU.has-fmax by x (ordtrans x<z z≤x ) )
            lem00 : BAU.f bx z z≤x ≡ & nbx
            lem00 = BAU.fp-lim  bx _  (λ w eq → ¬p (record { oprev = w ; oprev=x = sym eq } )) c z≤x
            lem01 : BAU.f by z z≤x  ≡ & nby
            lem01 = BAU.fp-lim  by _  (λ w eq → ¬p (record { oprev = w ; oprev=x = sym eq } )) c z≤x
            lem04 : (w  : Ordinal) → (w≤z : w o< z) → (w≤x : w o≤ x) → BAU.f bx w w≤x ≡ BAU.f by w w≤x
            lem04 w lt le = prev _ lt le
            lem05 :  {w : Ordinal} → odef nbx w → odef nby w
            lem05 {w} bxw = record { value = BMOrd.value bxw ; value<y = lem07  ; Mv=x
                = trans (sym (trans (lem04 _ lem07 (ordtrans lem07 z≤x )) (BAU.fcong by _ _ _ _ refl ) ))  (BMOrd.Mv=x bxw)   } where
                  lem07 : BMOrd.value bxw  o< z
                  lem07 = BMOrd.value<y bxw
            lem06 :  {w : Ordinal} → odef nby w → odef nbx w
            lem06 {w} byw = record { value = BMOrd.value byw ; value<y = lem07 ; Mv=x
                = trans (trans (lem04 _ lem07 (ordtrans (BMOrd.value<y byw) z≤x )) (BAU.fcong by _ _ _ _ refl ) )  (BMOrd.Mv=x byw)   }  where
                  lem07 : BMOrd.value byw  o< z
                  lem07 = BMOrd.value<y byw
            lem03 : & nbx ≡ & nby
            lem03 = ==→o≡ record { eq→  = lem05 ; eq←  = lem06 }

    BAU-unique1 : (L : HOD)  (PB : HODBooleanAlgebra L ) → {x y z : Ordinal} → (bx : BAU L PB x) (by : BAU L PB y)
       → x ≡ y → (z≤x : z o≤ x) (z≤y : z o≤ y) → BAU.f bx z z≤x ≡ BAU.f by z z≤y
    BAU-unique1 L PB {x} {_} {z} bx by refl z≤x z≤y with o<-irr {z} {osuc x} {z≤x} {z≤y}
    ... | refl = BAU-unique0 L PB bx by z≤x

    BAU-unique2 : (L : HOD)  (PB : HODBooleanAlgebra L ) → {x z1 z2 : Ordinal} → (bx by : BAU L PB x)
       → z1 ≡ z2 → (z1≤x : z1 o≤ x) (z2≤x : z2 o≤ x) → BAU.f bx z1 z1≤x ≡ BAU.f by z2 z2≤x
    BAU-unique2 L PB {x} {_} {z} bx by refl z1≤x z2≤x with o<-irr {z} {osuc x} {z1≤x} {z2≤x}
    ... | refl = BAU-unique0 L PB bx by z1≤x

    BAU-unique3 : (L : HOD)  (PB : HODBooleanAlgebra L ) → {x y z1 z2 : Ordinal} → (bx : BAU L PB x) (by : BAU L PB y)
       → x ≡ y → z1 ≡ z2 → (z1≤x : z1 o≤ x) (z2≤y : z2 o≤ y) → BAU.f bx z1 z1≤x ≡ BAU.f by z2 z2≤y
    BAU-unique3 L PB {x} {_} {z} bx by refl refl z1≤x z2≤y with o<-irr {z} {osuc x} {z1≤x} {z2≤y}
    ... | refl = BAU-unique0 L PB bx by z1≤x

    BUnion-unique : (L : HOD)  (PB : HODBooleanAlgebra L ) → {y max1 max2 b1 : Ordinal}
       → (bau1 : BAU L PB b1) → (bau2 : BAU L PB b1) → (y≤b1 : y o≤ b1)
       → (is-max1 : (x : Ordinal) → (x<y : x o< y) → BAU.f bau1 x (ordtrans x<y y≤b1 ) o< max1 )
       → (is-max2 : (x : Ordinal) → (x<y : x o< y) → BAU.f bau2 x (ordtrans x<y y≤b1 ) o< max2 )
       → BUnion y (λ z z<y →  BAU.f bau1 z (ordtrans z<y y≤b1 ) ) max1 is-max1 =h= BUnion y (λ z z<y →  BAU.f bau2 z (ordtrans z<y y≤b1 ) ) max2 is-max2
    BUnion-unique L PB {y} {_} bau1 bau2 y≤b1 is-max1 is-max2 = record {
         eq→ = λ {z} lt → record { value = BMOrd.value lt ; value<y = BMOrd.value<y lt
           ; Mv=x = trans (trans (BAU-unique0 L PB bau2 bau1 (ordtrans (BMOrd.value<y lt) y≤b1 ) ) (BAU.fcong bau1 _ _ _ _ refl ) ) ( BMOrd.Mv=x lt )  }
       ; eq← = λ {z} lt → record { value = BMOrd.value lt ; value<y = BMOrd.value<y lt
           ; Mv=x = trans (trans (BAU-unique0 L PB bau1 bau2 (ordtrans (BMOrd.value<y lt) y≤b1 ) ) (BAU.fcong bau2 _ _ _ _ refl ) ) ( BMOrd.Mv=x lt )  }
      }

    BUnion-unique1 : {y max1 max2 : Ordinal}
       → (M1 M2 : (x : Ordinal ) → x o< y → Ordinal )
       → (is-max1 : (x : Ordinal) → (x<y : x o< y) → M1 _ x<y o< max1 )
       → (is-max2 : (x : Ordinal) → (x<y : x o< y) → M2 _ x<y o< max2 )
       → ( (x : Ordinal ) → (x<y : x o< y) → M1 _ x<y ≡ M2 _ x<y )
       → BUnion y M1 max1 is-max1 =h= BUnion y M2 max2 is-max2
    BUnion-unique1 {y} {m1} {m2} M1 M2 im1 im2 eq = record {
              eq→ = λ {z} lt → record { value = BMOrd.value lt ; value<y = BMOrd.value<y lt ; Mv=x = lem00 z lt  }
            ; eq← = λ {z} lt → record { value = BMOrd.value lt ; value<y = BMOrd.value<y lt ; Mv=x = lem01 z lt  }
        } where
            lem00 : (z : Ordinal) → ( lt : BMOrd y M1 z ) → M2 (BMOrd.value lt) (BMOrd.value<y lt) ≡ z
            lem00 z lt = trans (sym (eq (BMOrd.value lt) (BMOrd.value<y lt) )) (BMOrd.Mv=x lt)
            lem01 : (z : Ordinal) → ( lt : BMOrd y M2 z ) → M1 (BMOrd.value lt) (BMOrd.value<y lt) ≡ z
            lem01 z lt = trans (eq (BMOrd.value lt) (BMOrd.value<y lt) ) (BMOrd.Mv=x lt)
    --
    -- Constructing the Boolean Algebra Universe
    --

    MBc : (L : HOD)  (PB : HODBooleanAlgebra L ) → (bflim : (y : Ordinal) →  BFlim L PB y) → (x : Ordinal) → BAU L PB x
    MBc L PB bflim x = Ordinals.inOrdinal.TransFinite0 O {λ x → BAU L PB x} lem01 x where
        lem01 : (x : Ordinal) → ((y : Ordinal) → y o< x → BAU L PB y) → BAU L PB x
        lem01 x prev = record { f = lem02
             ; fcong = lem04 ;  fmax = fmax ;  has-fmax = has-fmax ;  fp0 = lem50 ;  fp-prev = lem05 ;  fp-lim = lem60
          } where
            lem09 : (y : Ordinal) →  y ≡ x → ( z : Ordinal) → z o< y → BAU L PB z
            lem09 y b z z<y = prev z (subst (λ k → z o< k) b z<y )
            lem10 : (y : Ordinal)  → (b : y ≡ x) → (w : Ordinal) (w<y : w o< y) → BAU.f (lem09 y b w w<y) w <-osuc o< BFlim.bfmax (bflim y) (lem09 y b)
            lem10 y b w w<y =  BFlim.is-bfmax (bflim y) _ w<y (lem09 y b) _ <-osuc

            lem02 : (y : Ordinal) → y o≤ x →  Ordinal
            lem02 y y≤x with trio< y o∅
            ... | tri< a ¬b ¬c = ⊥-elim ( ¬x<0 a)
            ... | tri≈ ¬a b ¬c = o∅
            ... | tri> ¬a ¬b 0<y with trio< y x
            ... | tri< a ¬b ¬c = BAU.f (prev y a) y <-osuc
            ... | tri> ¬a ¬b c = ⊥-elim ( o≤> y≤x  c )
            ... | tri≈ ¬a b ¬c with Oprev-p  y
            ... | yes0 p = & ( FuncsSHOD (* (BAU.f (prev _ (ordtrans<-≤ lem03 y≤x ) ) (Oprev.oprev p) <-osuc )) (OS PB) ) where
                lem03 : Oprev.oprev p o< y
                lem03 = subst (λ k → Oprev.oprev p o< k) (Oprev.oprev=x p) <-osuc
            ... | no0 ¬p = & ( BUnion y (λ z z<y → BAU.f (lem09 y b z z<y) z <-osuc ) (BFlim.bfmax (bflim y) (lem09 y b)) (lem10 y b)  )

            lem50 :  (y : Ordinal) → y ≡ o∅ → (y≤x : y o≤ x) → lem02 y y≤x ≡ o∅
            lem50 y y=0 y≤x with trio< y o∅
            ... | tri< a ¬b ¬c = ⊥-elim ( ¬x<0 a)
            ... | tri≈ ¬a b ¬c = refl
            ... | tri> ¬a ¬b c = ⊥-elim ( ¬b y=0)

            fmax0 : HOD
            fmax0 = BUnion x (λ z z<y → BAU.f (lem09 x refl z z<y) z <-osuc ) (BFlim.bfmax (bflim x) (lem09 x refl )) (lem10 x refl )

            fmax : Ordinal
            fmax with Oprev-p  x
            ... | yes0 p = omax (osuc (& ( FuncsSHOD (* (BAU.f (prev _ lem03 ) (Oprev.oprev p) <-osuc )) (OS PB) ))) (osuc (& fmax0))  where
                lem03 : Oprev.oprev p o< x
                lem03 = subst (λ k → Oprev.oprev p o< k) (Oprev.oprev=x p) <-osuc
            ... | no0 ¬p =  osuc (& fmax0)

            lem04 :  (a b : Ordinal) (a≤x : a o≤ x) (b≤x : b o≤ x) → a ≡ b → lem02 a a≤x ≡ lem02 b b≤x
            lem04 a a a≤x b≤x refl = cong (λ k → lem02 a k) o<-irr  --  we cannot use cong₂ ( λ j k → lem02 j k )  a=b o<-irr

            lem05 : (y z : Ordinal) → y ≡ osuc z → (z≤x : z o≤ x) (y≤x : y o≤ x) → lem02 y y≤x ≡ & (FuncsSHOD (* (lem02 z z≤x)) (OS PB))
            lem05 y z eq z≤x y≤x with trio< y o∅
            ... | tri< a ¬b ¬c = ⊥-elim ( ¬x<0 a)
            ... | tri≈ ¬a b ¬c =  ⊥-elim ( o<¬≡ (sym b) (subst (λ k → o∅ o< k ) (sym eq) (b<x→0<x <-osuc ) ))
            ... | tri> ¬a ¬b c with trio< y x
            ... | tri< a ¬b₁ ¬c = trans ( BAU.fp-prev (prev y a) y z eq  (subst (λ k → z o< osuc k ) (sym eq) (ordtrans <-osuc <-osuc ))  <-osuc )
                  (cong (&) (cong ( λ k → FuncsSHOD (* k) (OS PB) ) lem06  ) ) where
               lem06 : BAU.f (prev y a ) z (subst (λ k → z o< osuc k) (sym eq) (ordtrans <-osuc <-osuc)) ≡ lem02 z z≤x
               lem06 with trio< z o∅
               ... | tri< a ¬b ¬c = ⊥-elim ( ¬x<0 a)
               ... | tri≈ ¬a b ¬c = BAU.fp0 (prev y a) _ b (subst (λ k → z o< osuc k) (sym eq) (ordtrans <-osuc <-osuc)) -- lem02 o∅ ≡ o∅
               ... | tri> ¬a ¬b c with trio< z x
               ... | tri< a₁ ¬b₁ ¬c = trans (BAU.fcong (prev y a) _ _ _ _ refl )
                    (sym (BAU-unique L PB (subst (λ k → z o< k) (sym eq) <-osuc ) (prev z a₁ ) (prev y a ) <-osuc ))
               ... | tri≈ ¬a₁ b ¬c = ⊥-elim ( o<> a (subst (λ k → x o< k) (trans (cong osuc (sym b)) (sym eq)) <-osuc  ))
               ... | tri> ¬a₁ ¬b₁ c₁ = ⊥-elim ( o≤> z≤x c₁ )
            ... | tri> ¬a₁ ¬b₁ c₁ = ⊥-elim ( o≤> y≤x  c₁ )
            ... | tri≈ ¬a₁ b ¬c with Oprev-p  y
            ... | yes0 p =  lem06 where
                lem03 : Oprev.oprev p o< y
                lem03 = subst (λ k → Oprev.oprev p o< k) (Oprev.oprev=x p) <-osuc
                lem08 : Oprev.oprev p ≡ z
                lem08 = osuc-inject (trans ( Oprev.oprev=x p ) eq )
                lem20 : Oprev.oprev p o< x
                lem20 = subst₂ ( λ j k → j o< k  ) (sym lem08) (trans (sym eq) b) <-osuc
                lem21 : BAU.f (prev (Oprev.oprev p) (ordtrans<-≤ lem03 y≤x)) (Oprev.oprev p) <-osuc ≡ lem02 z z≤x
                lem21 with trio< z o∅
                ... | tri< a ¬b ¬c = ⊥-elim ( ¬x<0 a)
                ... | tri≈ ¬a b ¬c = BAU.fp0 (prev _ (ordtrans<-≤ lem03 y≤x ) ) _ (trans lem08 b) <-osuc
                ... | tri> ¬a ¬b c with trio< z x
                ... | tri< a ¬b₁ ¬c = lem22  where
                    lem22 : BAU.f (prev (Oprev.oprev p) (ordtrans<-≤ lem03 y≤x)) (Oprev.oprev p) <-osuc ≡ BAU.f (prev _ a) z <-osuc
                    lem22 = begin
                        BAU.f (prev (Oprev.oprev p) (ordtrans<-≤ lem03 y≤x)) (Oprev.oprev p) <-osuc
                            ≡⟨ BAU.fcong (prev (Oprev.oprev p) (ordtrans<-≤ lem03 y≤x)) _ _ <-osuc _  lem08 ⟩
                        BAU.f (prev (Oprev.oprev p) (ordtrans<-≤ lem03 y≤x)) z (subst (λ k → z o< osuc k) (sym lem08) <-osuc )
                           ≡⟨ BAU-unique1 L PB (prev (Oprev.oprev p) (ordtrans<-≤ lem03 y≤x)) (prev _ a) lem08 _ _  ⟩
                        BAU.f (prev _ a) z <-osuc
                        ∎ where open ≡-Reasoning
                ... | tri≈ ¬a₁ b₁ ¬c = ⊥-elim ( o<¬≡  b₁ (subst (λ k → z o< k) (trans (sym eq) b ) <-osuc ))
                ... | tri> ¬a₁ ¬b₁ c₁ = ⊥-elim ( o<>  c₁ (subst (λ k → z o< k) (trans (sym eq) b ) <-osuc ))
                lem06 :  & ( FuncsSHOD (* (BAU.f (prev _ (ordtrans<-≤ lem03 y≤x ) ) (Oprev.oprev p) <-osuc )) (OS PB) ) ≡ & (FuncsSHOD (* (lem02 z z≤x)) (OS PB))
                lem06 = cong (λ k → & (FuncsSHOD (* k) (OS PB) ) ) lem21
            ... | no0 ¬p =  ⊥-elim ( ¬p record { oprev = z ; oprev=x = sym eq } )

            has-fmax : (y : Ordinal) (y≤x : y o≤ x) → lem02 y y≤x o< fmax
            has-fmax y y≤x with trio< y o∅
            ... | tri< a ¬b ¬c = ⊥-elim ( ¬x<0 a)
            ... | tri≈ ¬a b ¬c = subst (λ k → k o< fmax ) lem12 lem13 where
               lem11 : { x : Ordinal} → o∅ o< osuc x
               lem11 {x} with trio< x o∅
               ... | tri< a ¬b ¬c = ⊥-elim ( ¬x<0 a)
               ... | tri≈ ¬a b ¬c = subst (λ k → o∅ o< osuc k ) (sym b) <-osuc
               ... | tri> ¬a ¬b c = ordtrans <-osuc (osucc (b<x→0<x c))
               lem12 : lem02 y y≤x ≡ o∅
               lem12 with trio< y o∅
               ... | tri< a ¬b ¬c = ⊥-elim ( ¬x<0 a)
               ... | tri≈ ¬a b ¬c = refl
               ... | tri> ¬a ¬b 0<y = ⊥-elim ( ¬b b )
               lem13 : lem02 y  y≤x o< fmax
               lem13 with Oprev-p  x
               ... | yes0 p = ordtrans (subst (λ k → k o< osuc (& fmax0) ) (sym lem12) lem11 ) ( omax-y _ _  )
               ... | no0 ¬p = subst (λ k → k o< osuc (& fmax0) ) (sym lem12) lem11
            ... | tri> ¬a ¬b 0<y with trio< y x
            ... | tri< a ¬b ¬c = lem13 where
               lem11 : BAU.f (prev y a) y <-osuc o< osuc (& fmax0)
               lem11 = ordtrans ( odef< (record { value = _ ; value<y = a ; Mv=x = refl })  ) <-osuc
               lem13 : BAU.f (prev y a) y <-osuc o< fmax
               lem13 with Oprev-p  x
               ... | yes0 x = ordtrans lem11 ( omax-y _ _  )
               ... | no0 x = lem11
            ... | tri> ¬a ¬b c = ⊥-elim ( o≤> y≤x  c )
            ... | tri≈ ¬a b ¬c with Oprev-p  y
            ... | yes0 p = lem11 where
               lem03 : Oprev.oprev p o< y
               lem03 = subst (λ k → Oprev.oprev p o< k) (Oprev.oprev=x p) <-osuc
               lem14 : Oprev.oprev p o< x
               lem14 = subst (λ k → Oprev.oprev p o< k) b lem03
               lem11 : (& ( FuncsSHOD (* (BAU.f (prev _ (ordtrans<-≤ lem03 y≤x ) ) (Oprev.oprev p) <-osuc )) (OS PB) )) o< fmax
               lem11 with Oprev-p x
               ... | yes0 p1 = ordtrans (subst (λ k → & (FuncsSHOD (* k) _ ) o< osuc (& ( FuncsSHOD (* (BAU.f (prev _ lem15) (Oprev.oprev p1) <-osuc )) (OS PB) )) )
                     (sym lem12)  <-osuc) ( omax-x _ _   ) where
                  lem15 : Oprev.oprev p1 o< x
                  lem15 = subst (λ k → Oprev.oprev p1 o< k) (Oprev.oprev=x p1) <-osuc
                  lem16 : Oprev.oprev p1 ≡ Oprev.oprev p
                  lem16 = osuc-inject (trans (Oprev.oprev=x p1) (sym (trans (Oprev.oprev=x p) b ) ) )
                  lem12 : BAU.f (prev _ (ordtrans<-≤ lem03 y≤x ) ) (Oprev.oprev p) <-osuc ≡ BAU.f (prev _ lem15 ) (Oprev.oprev p1) <-osuc
                  lem12 = BAU-unique3 L PB (prev _ (ordtrans<-≤ lem03 y≤x ) ) (prev _ lem15 ) (sym lem16) (sym lem16) <-osuc <-osuc
               ... | no0 ¬p = ⊥-elim (¬p record { oprev = _ ; oprev=x = trans (Oprev.oprev=x p) b } )
            ... | no0 ¬p with Oprev-p  x
            ... | yes0 p1 = ⊥-elim ( ¬p record { oprev = Oprev.oprev p1 ; oprev=x = trans (Oprev.oprev=x p1) (sym b)  } )
            ... | no0 ¬p1 = subst (λ k → k o< osuc (& fmax0 )) (lem11 (sym b))  <-osuc  where
               lem11 : (x ≡ y ) → & fmax0 ≡ & ( BUnion y (λ z z<y → BAU.f (lem09 y b z z<y) z <-osuc ) (BFlim.bfmax (bflim y) (lem09 y b)) (lem10 y b)  )
               lem11 refl = ==→o≡ ( BUnion-unique1 (λ z z<y → BAU.f (lem09 x refl z z<y) z <-osuc ) (λ z z<y → BAU.f (lem09 y b z z<y) z <-osuc )
                  (lem10 x refl )  (lem10 y b) lem12  ) where
                   lem12 : (x₂ : Ordinal) (x<y : x₂ o< x) → BAU.f (lem09 x refl x₂ x<y) x₂ <-osuc ≡ BAU.f (lem09 x b x₂ x<y) x₂ <-osuc
                   lem12 x₂ x<y = BAU-unique1 L PB (lem09 x refl x₂ x<y) (lem09 y b x₂ x<y) refl <-osuc <-osuc

            lem60 : (y : Ordinal) → ((z : Ordinal) → ¬ y ≡ osuc z) → o∅ o< y → (y≤x : y o≤ x) →
                lem02 y y≤x ≡ & (BUnion y (λ z z<y → lem02 z (ordtrans z<y y≤x)) fmax (λ z z<y → has-fmax z (ordtrans z<y y≤x)))
            lem60 y ne 0<y y≤x with trio< y o∅
            ... | tri< a ¬b ¬c = ⊥-elim ( ¬x<0 a)
            ... | tri≈ ¬a b ¬c = ⊥-elim ( ¬c 0<y )
            ... | tri> ¬a ¬b c with trio< y x
            ... | tri< a ¬b₀ ¬c = lem20 where
                lem20 : BAU.f (prev _ a) y <-osuc ≡ & (BUnion y (λ z z<y → lem02 z (ordtrans z<y y≤x)) fmax (λ z z<y → has-fmax z (ordtrans z<y y≤x)))
                lem20 with Oprev-p  y
                ... | yes0 p =  ⊥-elim ( ne _ (sym (Oprev.oprev=x p) ))
                ... | no0 ¬p =  trans (BAU.fp-lim (prev y a) y lim 0<y <-osuc ) (==→o≡
                      record { eq→ = λ {z} lt → record { value = BMOrd.value lt ; value<y = BMOrd.value<y lt
                          ; Mv=x = trans (lem31 _ lt)  (BMOrd.Mv=x lt) }
                       ; eq← = λ {z} lt → record { value = BMOrd.value lt ; value<y = BMOrd.value<y lt
                          ; Mv=x = trans (lem40 _ lt) (BMOrd.Mv=x lt) }} ) where
                    lim :  (z : Ordinal) → ¬ y ≡ osuc z
                    lim z y=oz =  ⊥-elim ( ¬p record { oprev = z ; oprev=x = sym y=oz } )
                    lem31 :  (z : Ordinal) → (lt : BMOrd y (λ z₁ z<y → prev y a .BAU.f z₁ (ordtrans z<y <-osuc)) z )
                       → (lem02 (BMOrd.value lt) (ordtrans (BMOrd.value<y lt) y≤x))
                            ≡ BAU.f (prev y a)  (BMOrd.value lt) (ordtrans (BMOrd.value<y lt) <-osuc)
                    lem31 z lt with trio< (BMOrd.value lt) o∅
                    ... | tri< a ¬b ¬c =  ⊥-elim ( ¬x<0 a)
                    ... | tri≈ ¬a b ¬c = sym (BAU.fp0 (prev y a) _ b (ordtrans (BMOrd.value<y lt) <-osuc) )
                    ... | tri> ¬a ¬b c with trio< (BMOrd.value lt) x
                    ... | tri< a₁ ¬b ¬c = lem34 where
                        lem32 : (BMOrd.value lt) o< x
                        lem32 = a₁
                        lem34 : BAU.f (prev (BMOrd.value lt) a₁) (BMOrd.value lt) <-osuc
                            ≡ BAU.f (prev y a)  (BMOrd.value lt) (ordtrans (BMOrd.value<y lt) <-osuc)
                        lem34 = trans (BAU-unique L PB (BMOrd.value<y lt) (prev (BMOrd.value lt) a₁) (prev y a) <-osuc )
                           (BAU.fcong (prev y a) _ _ _ _ refl)
                    ... | tri≈ ¬a b ¬c = ⊥-elim ( o<¬≡ b (ordtrans (BMOrd.value<y lt ) a ) )
                    ... | tri> ¬a ¬b c = ⊥-elim ( o<> c (ordtrans (BMOrd.value<y lt ) a)  )
                    lem40 : (z : Ordinal) → (lt : BMOrd y (λ z z<y → lem02 z (ordtrans z<y y≤x) ) z)  → prev y a .BAU.f (BMOrd.value lt) (ordtrans (BMOrd.value<y lt) <-osuc)
                       ≡ lem02 (BMOrd.value lt) (ordtrans (lt .BMOrd.value<y) y≤x)
                    lem40 z lt with trio< (BMOrd.value lt) o∅
                    ... | tri< a ¬b ¬c =  ⊥-elim ( ¬x<0 a)
                    ... | tri≈ ¬a b ¬c = BAU.fp0 (prev y a) _ b (ordtrans (BMOrd.value<y lt) <-osuc)
                    ... | tri> ¬a ¬b c with trio< (BMOrd.value lt) x
                    ... | tri< a₁ ¬b ¬c = lem34 where
                        lem32 : (BMOrd.value lt) o< y
                        lem32 = BMOrd.value<y lt
                        lem34 :  BAU.f (prev y a ) (BMOrd.value lt) (ordtrans (BMOrd.value<y lt) <-osuc)
                            ≡ BAU.f (prev (BMOrd.value lt) a₁)  (BMOrd.value lt) <-osuc
                        lem34 = trans (BAU.fcong (prev y a) _ _ _ _ refl)  (sym (BAU-unique L PB lem32 (prev (BMOrd.value lt) a₁) (prev y a )  <-osuc ))
                    ... | tri≈ ¬a b ¬c = ⊥-elim ( o<¬≡ b (ordtrans (BMOrd.value<y lt ) a ) )
                    ... | tri> ¬a ¬b c = ⊥-elim ( o<> c (ordtrans (BMOrd.value<y lt ) a)  )
            ... | tri> ¬a₁ ¬b₁ c₁ = ⊥-elim ( o≤> y≤x c₁ )
            ... | tri≈ ¬a₁ b ¬c with Oprev-p  y
            ... | yes0 p =  ⊥-elim ( ne _ (sym (Oprev.oprev=x p) ))
            ... | no0 ¬p =  ==→o≡ lem24  where
                lem20 : (z : Ordinal) (z<y : z o< y) → BAU.f (lem09 y b z z<y) z <-osuc ≡ lem02 z (ordtrans z<y y≤x)
                lem20 z z<y with trio< z o∅
                ... | tri< a ¬b ¬c = ⊥-elim ( ¬x<0 a)
                ... | tri≈ ¬a b₂ ¬c = BAU.fp0 (lem09 y b z z<y) _ b₂ <-osuc
                ... | tri> ¬a ¬b c with trio< z x
                ... | tri< a ¬b₁ ¬c = lem23 where
                    lem23 : BAU.f (lem09 y b z z<y) z <-osuc ≡ BAU.f (prev z a ) z <-osuc
                    lem23 = BAU-unique1 L PB (lem09 y b z z<y) (prev z a ) refl <-osuc <-osuc
                ... | tri> ¬a₁ ¬b₁ c₁ = ⊥-elim ( o≤> (ordtrans z<y y≤x) c₁ )
                ... | tri≈ ¬a₁ b₂ ¬c with Oprev-p  z
                ... | yes0 p =  ⊥-elim ( ne _ (trans (sym (trans b₂ (sym b)) ) (sym (Oprev.oprev=x p) )  ))
                ... | no0 ¬p =  trans ( BAU.fp-lim (lem09 y b z z<y) z lim c <-osuc ) (==→o≡ lem25 ) where
                    lem25 :
                        BUnion z (λ z₁ z<y₁ → BAU.f (lem09 y b z z<y) z₁ (ordtrans z<y₁ <-osuc))
                            (lem09 y b z z<y .BAU.fmax) (λ z₁ z<y₁ → lem09 y b z z<y .BAU.has-fmax z₁ (ordtrans z<y₁ <-osuc))
                         =h= BUnion z (λ z₁ z<y₁ → BAU.f (lem09 z b₂ z₁ z<y₁) z₁ <-osuc) (BFlim.bfmax (bflim z) (lem09 z b₂)) (lem10 z b₂)
                    lem25 = BUnion-unique1 _ _ (λ z₁ z<y₁ → lem09 y b z z<y .BAU.has-fmax z₁ (ordtrans z<y₁ <-osuc)) (lem10 z b₂ )
                      (λ w w<z → trans (BAU.fcong (lem09 y b z z<y) _ _ ( ordtrans w<z <-osuc) (ordtrans <-osuc (osucc w<z))  refl )
                          (sym (BAU-unique L PB w<z  (lem09 z b₂ _ w<z ) (lem09 y b z z<y) <-osuc ))  )
                    lim : (w : Ordinal) → ¬ z ≡ osuc w
                    lim w z=oz =  ⊥-elim ( ¬p record { oprev = w ; oprev=x = sym z=oz } )
                lem24 : BUnion y (λ z z<y → BAU.f (lem09 y b z z<y) z <-osuc ) (BFlim.bfmax (bflim y) (lem09 y b)) (lem10 y b) =h=
                    BUnion y (λ z z<y → lem02 z (ordtrans z<y y≤x)) fmax (λ z z<y → has-fmax z (ordtrans z<y y≤x))
                lem24 = BUnion-unique1 _ _  (lem10 y b) (λ z z<y → has-fmax z (ordtrans z<y y≤x)) lem20

    record MBOrd (L : HOD)  (PB : HODBooleanAlgebra L ) (bflim : (y : Ordinal) →  BFlim L PB y) (x : Ordinal) : Set n where
      field
        b : Ordinal
        is-b : BAU.f (MBc L PB bflim b) _ <-osuc ≡ x

    B1 : (L : HOD)  (PB : HODBooleanAlgebra L ) (bflim : (y : Ordinal) →  BFlim L PB y) → OD
    B1 L PB bflim = record { def = λ x → MBOrd L PB bflim x }

module MBO {n : Level } (O : Ordinals {n} ) (HODAxiom : HODBase.ODAxiom O)  (ho< : OD.ODAxiom-ho< O HODAxiom )
           (AC : OD.AxiomOfChoice O HODAxiom ) where

    open Ordinals.Ordinals  O
    open Ordinals.IsOrdinals isOrdinal
    open HODBase.ODAxiom HODAxiom
    open OD O HODAxiom
    open import ODC O HODAxiom AC as ODC

    open AxiomOfChoice AC
    open OrdUtil O
    open ODUtil O HODAxiom  ho<
    open HODBase.HOD
    open _∧_
    open _∨_
    open Bool
    open  HODBase._==_
    open import ZProduct O HODAxiom ho<
    open import filter O HODAxiom ho< AC

    open import bijection hiding ( b1 )
    open MBA O HODAxiom ho< AC
    open MBU O HODAxiom ho< AC

    -- open HODBooleanAlgebra

    -- LDec : (L : HOD) (P : HOD) → P ⊆ L → (x : HOD) → Dec0 (x ∈ P)
    -- LDec L P _ x = ∋-p P x

    -- open import Data.Nat
    open import ZEquiv O HODAxiom ho<

    open HODElement
    import BAlgebra

    open Bijection
    -- B1 contains all Ordinals
    --
    --

    --
    -- v : M → B1, but we have to write everyhing in Ordinal
    --   this is because B1 is defined by Ordinal.
    --
    -- v ∅0 = o∅
    -- v x = { < v y , b1 > | y ∈ x } if x ≠ ∅0 ,  B1 ∋ { < v y , b0 > | y ∉ x }

    open _∧_

    --
    -- vO is a Function from single element Set to 1
    --
    record vO (L : HOD)  (PB : HODBooleanAlgebra L ) (Y : HOD) (x : Ordinal) : Set n where
      open BooleanAlgebra (HODBooleanAlgebra.ba PB)
      open IsBooleanAlgebra (BooleanAlgebra.isBooleanAlgebra (HODBooleanAlgebra.ba PB))
      field
         y : Ordinal
         vy : odef Y y
         f=p : & < * y , * (elt b1) >  ≡ x

--   vHOD : (L : HOD)  (PB : HODBooleanAlgebra L ) (Y : HOD)  → HOD
--   vHOD L PB Y = record { od = record { def = λ x → vO L PB Y x }  ; odmax = ? ; <odmax = λ {x} lt → ? }
--
--   record vR (L : HOD)  (PB : HODBooleanAlgebra L ) (x : Ordinal) : Set n where
--     field
--        f : (y : Ordinal) → y o≤ x →  Ordinal
--        fcong : (a b : Ordinal) → (a≤x : a o≤ x) (b≤x : b o≤ x) → a ≡ b → f a a≤x ≡ f b b≤x
--        fmax : Ordinal
--        has-fmax : (y : Ordinal) → (y≤x : y o≤ x ) → f y y≤x o< fmax
--        fp0 : (y : Ordinal) → y ≡ o∅  → (y≤x : y o≤ x) → f y y≤x ≡ o∅
--        fp-prev : (y z : Ordinal) → (y=oz : y ≡ osuc z ) → (z≤x : z o≤ x)  → (y≤x : y o≤ x )
--           → f y y≤x  ≡  & ( vHOD L PB ( * (f z z≤x ) ))  -- & ( FuncsSHOD (* (f z z≤x )) (OS PB) )
--        fp-lim : (y : Ordinal) → ((z : Ordinal) → ¬ ( y ≡ osuc z)) → o∅ o< y → (y≤x : y o≤ x)
--           → f y y≤x ≡  & ( BUnion y (λ z z<y → f z (ordtrans z<y y≤x )) fmax (λ z z<y → has-fmax z (ordtrans z<y y≤x ) ) )
--
--   vR-unique : (L : HOD)  (PB : HODBooleanAlgebra L ) → {x y z : Ordinal} → (x<y : x o< y) → (bx : vR L PB x) → (by : vR L PB y )
--      → (z≤x : z o≤ x) → vR.f bx z z≤x ≡ vR.f by z (ordtrans z≤x (osucc x<y))
--   vR-unique = ?
--
--   vMBc : (L : HOD)  (PB : HODBooleanAlgebra L ) (x : Ordinal) → vR L PB x
--   vMBc = ? -- L PB bflim x ox = ?
--
--   record vRB (L : HOD)  (PB : HODBooleanAlgebra L ) (bflim : (y : Ordinal) →  BFlim L PB y) (x : Ordinal) : Set n where
--     field
--        y : Ordinal
--        by : MBOrd L PB bflim y
--        y∋x : odef (* y) x
--
--   vMBc→B1  : (L : HOD)  (PB : HODBooleanAlgebra L ) (bflim : (y : Ordinal) →  BFlim L PB y) (x : Ordinal)
--       → (vm : vR L PB x ) → vRB L PB bflim x
--   vMBc→B1  = ?

    -- we can construct Set Theory Language L as a data type.
    -- we may define value of statement in L as Bool Value

    open import Relation.Binary hiding ( _⇔_ )
    open import Topology O HODAxiom ho< AC

    record OrderedHOD (P : HOD) : Set (Level.suc n) where
      field
         _p<_ : (x y : HODElement P) → Set n
         _=p=_ : (x y : HODElement P) → Set n
         PO : IsStrictPartialOrder {n} {n} _=p=_  _p<_
         p=resp : {x y w z : HODElement P } → elt x ≡ elt w → elt y ≡  elt z → x =p= y  → w =p= z
         p<-resp : {x y w z : HODElement P } → x =p= w → y =p= z → x p< y  → w p< z
      _p≤_ : (x y : HODElement P) → Set n
      x p≤ y = ( x =p= y ) ∨  ( x p< y )
      p-refl : {p : HODElement P} → p =p= p
      p-refl = IsEquivalence.refl (IsStrictPartialOrder.isEquivalence PO)
      p-refl1 : {p p' : HODElement P} → elt p ≡ elt p' → p =p= p'
      p-refl1 {p} refl = p=resp refl refl (p-refl {p})
      p-trans : {x y z : HODElement P} → x =p= y → y =p= z → x =p= z
      p-trans eq eq' = IsEquivalence.trans (IsStrictPartialOrder.isEquivalence PO) eq eq'
      p-sym : {x y : HODElement P} → x =p= y → y =p= x
      p-sym eq = IsEquivalence.sym (IsStrictPartialOrder.isEquivalence PO) eq
      p≤-resp : {x y w z : HODElement P } → x =p= w → y =p= z → x p≤ y  → w p≤ z
      p≤-resp {x} {y} {_} {_} x=w y=z (case1 eq) = case1 ( p=resp refl refl (p-trans (p-sym x=w) (p-trans eq y=z) ) )
      p≤-resp {x} {y} {_} {_} x=w y=z (case2 lt) = case2 ( p<-resp x=w y=z lt )
      p-sep : {x y : HODElement P} → (¬ (x p< y)) ∨ (¬ (y p< x) )
      p-sep {x} {y} with  p∨¬p (x p< y)
      ... | case2 lt = case1 lt
      ... | case1 x<y with  p∨¬p (y p< x)
      ... | case2 lt = case2 lt
      ... | case1 y<x = ⊥-elim ( IsStrictPartialOrder.asym PO x<y y<x )
      open IsStrictPartialOrder PO
      open import Data.Product
      p<-trans : {x y z : HODElement P} → x p< y → y p< z → x p< z
      p<-trans lt1 lt2 = IsStrictPartialOrder.trans PO lt1 lt2
      p≤-trans :  {x y z : HODElement P} → x p≤ y → y p≤ z → x p≤ z
      p≤-trans {x} {y} {z} (case1 eq) (case1 eq') = case1 (p-trans eq eq')
      p≤-trans {x} {y} {z} (case1 eq) (case2 lt) = case2 ( proj₂ <-resp-≈ (p-sym eq) lt )
      p≤-trans {x} {y} {z} (case2 lt) (case1 eq) = case2 ( proj₁ <-resp-≈ eq lt )
      p≤-trans {x} {y} {z} (case2 lt1) (case2 lt2) = case2 ( p<-trans lt1 lt2 )


    --  u ⊆ P , ∀ x ∈ u → y ∈ P → y ≤ x → y ∈ u
    record OpenP (P : HOD) (OP : OrderedHOD P) (u : Ordinal) : Set n where
      field
         u⊆P : (* u) ⊆ P
         is-open : (x y : Ordinal) → (ux : odef (* u) x) → (py : odef P y )
            →  OrderedHOD._p≤_ OP record { elt = y ; A∋elt  = py } record { elt = x ; A∋elt = u⊆P ux }  → odef (* u) y

    OpenPHOD :  (P : HOD) (OP : OrderedHOD P) → HOD
    OpenPHOD P OP = record { od = record { def = λ u → OpenP P OP u } ; odmax = osuc (& P)
       ; <odmax = λ {u} lt → subst (  λ k → k o< _ ) &iso  (⊆→o≤  (OpenP.u⊆P lt) )  }

    record DownP (P : HOD) (OP : OrderedHOD P) (u : HODElement P) (x : Ordinal) : Set n where
      field
         px  : odef P x
         is-below :  OrderedHOD._p≤_ OP record { elt = x ; A∋elt  = px } u

    -- set of all elements below u in P
    downHOD : (P : HOD) (OP : OrderedHOD P) (u : HODElement P) → HOD
    downHOD P OP u = record { od = record { def = λ x → DownP P OP u x } ; odmax = & P
       ; <odmax = λ {u} lt → odef< (DownP.px lt)  }

    -- is open
    downHOD∈OS : (P : HOD) (OP : OrderedHOD P) (u : HODElement P) → OpenP P OP (& (downHOD P OP u))
    downHOD∈OS  P OP u = record { u⊆P = λ {x} px → DownP.px (eq→ *iso px) ; is-open = λ x y px py le → eq← *iso
       (lem00 _ _ le (eq→ *iso px) ) } where
       open OrderedHOD OP
       open IsStrictPartialOrder PO
       lem00 : (ex ey : HODElement P) → ey p≤ ex → DownP P OP u (elt ex)  → DownP P OP u (elt ey)
       lem00 ex ey y≤x dux = record { px = A∋elt ey ; is-below =  p≤-trans  y≤x (p≤-resp (p-refl1 refl) p-refl (DownP.is-below dux)) }

    record ROH-lem00 (P : HOD) (OP : OrderedHOD P) (u : HODElement (Power P)) (ou : OpenP P OP (elt u))
         {x : Ordinal} (ux : odef (* (elt u)) x ) : Set n where
      field
         p : HODElement P
         dp⊆u : downHOD P OP p ⊆ (* (elt u))
         -- this means if u is open, it conains ∀ x p< ∃ p → x ∈ u
      open OrderedHOD OP
      open IsStrictPartialOrder PO
      p⊆u : {y : HODElement P } → y p≤ p → odef (* (elt p)) (elt y) → odef (* (elt u)) (elt y)
      p⊆u {y} y≤p py = dp⊆u (record { px = A∋elt y ; is-below = y≤p } )

    -- downHOD are open base
    --
    down-lem00 : (P : HOD) (OP : OrderedHOD P) (u : HODElement (Power P)) (ou : OpenP P OP (elt u))
        → {x : Ordinal} → (ux : odef (* (elt u)) x)
        → ROH-lem00 P OP u ou ux
    down-lem00 P OP u (ou @ record { u⊆P = u⊆P ; is-open = is-open }) {x} ux = lem00 where
       open OrderedHOD OP
       open IsStrictPartialOrder PO
       lem02 : HODElement P
       lem02 = record { elt = x ; A∋elt = A∋elt u _ ux }
       lem01 : {z : Ordinal} → odef (downHOD P OP lem02) z → odef (* (elt u)) z
       lem01 {z} d2 = OpenP.is-open ou _ _ ux (DownP.px d2) lem05  where
          lem05 : record { elt = z ; A∋elt = DownP.px d2 } p≤ record { elt = x ; A∋elt = u⊆P ux }
          lem05 = p≤-resp p-refl (p-refl1 refl) ( DownP.is-below d2 )
       lem00 : ROH-lem00 P OP u ou ux
       lem00 = record { p = lem02  ; dp⊆u = lem01 }

    down-lem02 : (P : HOD) (OP : OrderedHOD P) (u : HODElement (Power P)) (ou : OpenP P OP (elt u))
        → {x : Ordinal} → (ux : odef (* (elt u)) x)
        → odef ( downHOD P OP (ROH-lem00.p (down-lem00 P OP u ou ux  ) )  ) x
    down-lem02 P OP u ou {x} ux  = lem00 where
       open OrderedHOD OP
       open IsStrictPartialOrder PO
       lem01 :  odef P x
       lem01 = A∋elt u _ ux
       lem00 :  odef ( downHOD P OP (ROH-lem00.p (down-lem00 P OP u ou ux  ) )  ) x
       lem00 = record { px = lem01 ; is-below = case1 p-refl }

    record ROH-lem03 (P : HOD) (OP : OrderedHOD P) (u : HODElement (Power P)) (ou : OpenP P OP (elt u)) (y : Ordinal) : Set n where
      field
         x : Ordinal
         ux : odef (* (elt u)) x
         up : y ≡ (& ( downHOD P OP (ROH-lem00.p (down-lem00 P OP u ou {x} ux  ) ) ))
      y⊆P : (* y) ⊆  P
      y⊆P {z} lt = DownP.px ( eq→ (ord→== (trans &iso up) ) lt )
      y<P : y o< osuc (& P)
      y<P = subst (λ k → k o< _) &iso (⊆→o≤ y⊆P )

    ROH-lem05 : (P : HOD) (OP : OrderedHOD P) (u : HODElement (Power P)) (ou : OpenP P OP (elt u)) → HOD
    ROH-lem05 P OP u ou = record { od = record { def = λ x → ROH-lem03 P OP u ou x } ; odmax = osuc (& P) ; <odmax = λ {u} lt →  ROH-lem03.y<P lt }

    down-lem01 : (P : HOD) (OP : OrderedHOD P) (u : HODElement (Power P)) (ou : OpenP P OP (elt u))
        →  Union (ROH-lem05 P OP u ou)  =h= (* ( elt u)  )
    down-lem01 P OP u ou =  lem03  where
       open OrderedHOD OP
       lem05 : {y : Ordinal} → Own (ROH-lem05 P OP u ou ) y → odef (* (elt u)) y
       lem05 {y} record { owner = owner ; ao = ao ; ox = ox } = ROH-lem00.dp⊆u lem08 lem11  where
            lem09 : ROH-lem03 P OP u ou owner
            lem09 = ao
            lem07 : owner  ≡ & (downHOD P OP ( ROH-lem00.p (down-lem00 P OP u ou {ROH-lem03.x ao} (ROH-lem03.ux ao) ) ))
            lem07 = ROH-lem03.up ao
            lem08 : ROH-lem00 P OP u ou (ROH-lem03.ux ao)
            lem08 = down-lem00 P OP u ou {ROH-lem03.x ao} (ROH-lem03.ux ao)
            lem11 : odef (downHOD P OP (ROH-lem00.p (down-lem00 P OP u ou {ROH-lem03.x ao} (ROH-lem03.ux ao)  ) )) y
            lem11 = eq→ *iso ( eq→ (o≡→== (ROH-lem03.up ao) ) ox )
       lem06 : {y : Ordinal} → odef (* (elt u)) y → Own (ROH-lem05 P OP u ou) y
       lem06 {y} uy = record { owner = _ ; ao = record { x = _ ; ux = uy ; up = refl }  ; ox = eq← *iso record { px = A∋elt u _ uy ; is-below = case1 p-refl } }
       lem03 : Union (ROH-lem05 P OP u ou)  =h= (* ( elt u)  )
       lem03 = record { eq→ = λ {y} lt → lem05 lt ; eq← = λ {y} lt → lem06 lt }


    TOPP : (P : HOD) → OrderedHOD P → Topology P
    TOPP P OP = record { OS = OpenPHOD P OP  ;
         OS⊆PL = λ {y} op z px  → OpenP.u⊆P op px
       ; o∩ = λ {p} {q} op oq → record { u⊆P = λ {x} pqx → OpenP.u⊆P op (eq← *iso (proj1 (eq→ *iso pqx) ))
          ; is-open = λ x y ux py lt → eq←  *iso ⟪
               eq→ *iso (OpenP.is-open op _ _ (eq← *iso (proj1 (eq→  *iso ux))) py lt )
             , eq→ *iso (OpenP.is-open oq _ _ (eq← *iso (proj2 (eq→  *iso ux))) py 
                  (OrderedHOD.p≤-resp OP (OrderedHOD.p-refl OP) (OrderedHOD.p-refl1 OP refl ) lt ) ) ⟫  }
       ; o∪  = lem00
       ; OS∋od∅ = subst ( λ k → OpenP P OP k) (trans Union-0 (sym ord-od∅ ) ) (lem00 {od∅} (λ lt → ⊥-elim (¬x<0  lt) ) ) } where
          lem00 : {U : HOD} → U ⊆ OpenPHOD P OP → OpenPHOD P OP ∋ Union U
          lem00 {U} u⊆op = record { u⊆P = λ {x} ux → OpenP.u⊆P ( u⊆op (Own.ao (eq→ *iso ux))) (Own.ox (eq→ *iso ux))
            ; is-open = λ x y ux py lt → eq← *iso record { owner = Own.owner (eq→ *iso ux) ; ao = Own.ao  (eq→ *iso ux)
              ; ox = OpenP.is-open (u⊆op (Own.ao (eq→ *iso ux))) _ _ (Own.ox (eq→ *iso ux)) py lt }   }

    record UpP (P : HOD) (OP : OrderedHOD P) (u : HODElement P) (x : Ordinal) : Set n where
      field
         px  : odef P x
         is-above :  OrderedHOD._p<_ OP u record { elt = x ; A∋elt  = px } 

    -- set of an elements above u in P
    upHOD : (P : HOD) (OP : OrderedHOD P) (u : HODElement P) → HOD
    upHOD P OP u = record { od = record { def = λ x → UpP P OP u x } ; odmax = & P
       ; <odmax = λ {u} lt → odef< (UpP.px lt)  }
    -- is close
    upHOD∈OS : (P : HOD) (OP : OrderedHOD P) (u : HODElement P) → odef (Topology.CS (TOPP P OP)) (& (upHOD P OP u))
    upHOD∈OS P OP u = ⟪ (λ lt → UpP.px (eq→ *iso lt)) , record { u⊆P = λ lt → proj1 (eq→ *iso lt)  ; is-open = lem01 } ⟫ where
       open OrderedHOD OP
       open IsStrictPartialOrder PO
       lem01 : (x y : Ordinal) (ux : odef (* (& (P ＼ * (& (upHOD P OP u))))) x)
        (py : odef P y) → record { elt = y ; A∋elt = py } p≤ record { elt = x ; A∋elt = proj1 (eq→ *iso ux) } → odef (* (& (P ＼ * (& (upHOD P OP u))))) y
       lem01 x y ux py y≤x = eq← *iso ⟪ py , (λ lt → lem02 (eq→ *iso lt)) ⟫ where
          lem03 : odef (upHOD P OP u) x → ⊥
          lem03 record { px = px ; is-above = u<x } = proj2 (eq→ *iso ux) (eq← *iso record { px = px ; is-above = u<x } )
          lem04 : odef P x
          lem04 = proj1 (eq→ *iso ux)
          lem02 : odef (upHOD P OP u) y → ⊥
          lem02 record { px = py2 ; is-above = u<y } = proj2 (eq→ *iso ux) (eq← *iso record { px = lem04 ; is-above = lem05 y≤x } ) where
              lem05 : record { elt = y ; A∋elt = py } p≤ record { elt = x ; A∋elt = proj1 (eq→ *iso ux) } → u p< record { elt = x ; A∋elt = lem04 }  
              lem05 (case1 eq) = p<-resp p-refl (p=resp refl refl eq) u<y
              lem05 (case2 lt) = p<-trans u<y (p<-resp (p-refl1 refl) (p-refl1 refl) lt ) 

--    OP-transitive : (L : HOD) → (OL : OrderedHOD L) → {x y : Ordinal }  → odef (downHOD L OL) x → odef (* x) y → odef (downHOD L OL) y
--    OP-transitive L OL {x} {y} px xy = ?

    record Separate (P : HOD) (TP : Topology P) (p q : Ordinal ) : Set n where
      field
         sep : Ordinal
         os  : odef (Topology.OS TP) sep
         sp  : ( odef (* sep) p ∧ ( ¬ (odef (* sep) q)) )  ∨ ( odef (* sep) q ∧ ( ¬ (odef (* sep) p)) )

    T0-Separate : (P : HOD) → Topology P → {p q : HODElement P} → Set n
    T0-Separate P TP {p} {q}  = (p≠q : ¬ (elt p ≡ elt q)) → Separate P TP (elt p) (elt q)

    TOPP-Separate : (L : HOD) → (OL : OrderedHOD L) → {p q : HODElement L}
       → (p≠q : ¬ ( OrderedHOD._=p=_ OL p q)) → Separate L (TOPP L OL) (elt p) (elt q)
    TOPP-Separate L OL {p} {q} ne = lem30 p-sep  where
       open Topology
       open OrderedHOD OL
       lem26 : (¬ (p p< q)) ∨ (¬ (q p< p) )
       lem26 = p-sep
       lem30 : (¬ (p p< q)) ∨ (¬ (q p< p) ) → Separate L (TOPP L OL) (elt p) (elt q)
       lem30 (case1 np<q ) = record { sep =  & ( downHOD L OL q) ; os =  downHOD∈OS L OL q ; sp = case2 ( ⟪ eq← *iso lem31 , lem32 ⟫ )  } where
           lem31 : DownP L OL q (elt q)
           lem31 = record { px = A∋elt q ;  is-below = case1 p-refl  }
           lem32 : odef (* (& (downHOD L OL q))) (elt p) → ⊥
           lem32 lt = ⊥-elim ( np<q lem33 ) where
              lem33 : p p< q
              lem33 with DownP.is-below (eq→ *iso lt)
              ... | case1 eq = ⊥-elim ( ne (p=resp ? ? eq ))
              ... | case2 lt = p<-resp ? ? lt
       lem30 (case2 nq<p ) = record { sep =  & ( downHOD L OL p) ; os =  downHOD∈OS L OL p ; sp =  case1 ( ⟪ eq← *iso lem31 , lem32 ⟫ ) } where
           lem31 : DownP L OL p (elt p)
           lem31 = record { px = A∋elt p ;  is-below = case1 p-refl  }
           lem32 : odef (* (& (downHOD L OL p))) (elt q) → ⊥
           lem32 lt = ⊥-elim ( nq<p lem33 ) where
              lem33 : q p< p
              lem33 with DownP.is-below (eq→ *iso lt)
              ... | case1 eq = ⊥-elim ( ne (p=resp ? ? (p-sym eq) ))
              ... | case2 lt = p<-resp ? ? lt

    --
    -- Interior is a minimum open set containing x
    --
    ROH : (P : HOD) → (TP : Topology P) → HOD  -- regular open set of P
    ROH P TP = record { od = record { def = λ x → ((* x) ⊆ P )∧ (x ≡ & (Interior TP (Cl TP (* x)))) } ; odmax = osuc (& P )
       ; <odmax = λ {x} lt → subst (λ k → k o≤ & P) &iso ( ⊆→o≤ (λ {x} yx → proj1 lt yx )) }

    -- ROH-lem00 : (P : HOD) → (TP : Topology P) → {u : Ordinal} → odef (OS TP) u → (* u) ⊆ (Interior (TOPP L OL) (Cl (TOPP L OL) (* u)))

    -- ROH-lem00 : (P : HOD) → (TP : Topology P) → odef ROH u ⇔ (Interior (TOPP L OL) (Cl (TOPP L OL) (* u))) ⊆ (* u)
    -- ROH-lem00 =  ?

--   Cl-union : (L : HOD) ( OL : OrderedHOD L) {A : HOD} → Cl (TOPP L OL) (Union A) =h= Union (Cl (TOPP L OL) A)
--   Cl-union L OL {A} = record { eq→ = lem01 ; eq← = lem10 } where
--        open Topology
--        open OrderedHOD OL
--        top = TOPP L OL
--        lem01 : {x : Ordinal} → odef (Cl (TOPP L OL) (Union A)) x → odef (Union (Cl (TOPP L OL) A)) x
--        lem01 {x} ⟪ lx , csc ⟫ = record { owner = ? ; ao = ⟪ ? , ? ⟫ ; ox = ? }  where
--           lem02 : (c : Ordinal) → odef (CS (TOPP L OL)) c → Union A ⊆ * c → odef (* c) x    
--           lem02 = csc
--           lem03 : (c : Ordinal) → odef (CS (TOPP L OL)) c → A ⊆ * c → odef (* c) ?
--           lem03 = ?
--        lem10 : {x : Ordinal} → odef (Union (Cl (TOPP L OL) A)) x → odef (Cl (TOPP L OL) (Union A)) x
--        lem10 {x} record { owner = owner ; ao = ao ; ox = ox } = {! !}
--
--   inerior-int : (L : HOD) ( OL : OrderedHOD L) {x : HOD} →  Interior (TOPP L OL) (Intersection x) =h= Intersection (Interior (TOPP L OL) x)
--   inerior-int = ?

    -- ( ∀ L ∋ q, u → u is open →  ¬ ( u ∋ q) → ∃ r ≤ q → L ∋ s → (s ≤ r ) → ¬ ( u ∋ s ) ) == (  Interior (Cl top u) ⊆  u )
    --
    record  ROlem03 (L : HOD) (OL : OrderedHOD L) (u : HODElement (Power L) ) (ou : odef (Topology.OS (TOPP L OL)) (elt u) ) : Set n where
       open OrderedHOD OL
       field
          r : HODElement L →  HODElement L
          r-wld : (x y : HODElement L) → elt x ≡ elt y → elt (r x ) ≡ elt (r y  )
          prop : (q : HODElement L ) → ¬ ( odef (* (elt u)) (elt q) ) → ( r≤q : r q p≤ q ) → (s  : HODElement L ) → s p≤ r q
             → ¬ ( odef (* (elt u)) (elt s)  )

    ROH-lem06 : (L : HOD) (OL : OrderedHOD L)  → (p : HODElement L) → (u : HODElement (Power L)) → (d=u : downHOD L OL p =h= (* (elt u )))
        → ((  Interior (TOPP L OL) (Cl (TOPP L OL) (* (elt u)))) ⊆ (* (elt u))) 
          ⇔   ROlem03 L OL u (subst (λ k → OpenP L OL k) (trans (==→o≡ d=u) &iso ) (downHOD∈OS L OL p))
    ROH-lem06 L OL p u d=u = ⟪ ? , ? ⟫ where
       open Topology
       open OrderedHOD OL
       top = TOPP L OL
       lem00 : OpenP L OL (elt u)
       lem00 = subst (λ k → OpenP L OL k) (trans (==→o≡ d=u) &iso ) (downHOD∈OS L OL p)
       lem01 :  Interior top (Cl (TOPP L OL) (* (elt u))) ⊆ * (elt u) → ROlem03 L OL u lem00
       lem01 = ?
       lem02 :  Interior top (Cl (TOPP L OL) (downHOD L OL p)) ⊆ downHOD L OL p → ROlem03 L OL u lem00
       lem02 = ?
       lem03 : {x : Ordinal} → (dx : odef (downHOD L OL p) x ) → record { elt = x ; A∋elt = DownP.px dx }  p≤ p
       lem03 {x} dx = p≤-resp ? ? ( DownP.is-below dx )
       lem031 : {q : HODElement L }  → q p≤ p → odef (downHOD L OL p) (elt q) 
       lem031 {q} q≤p = record { px = A∋elt q ; is-below = q≤p }
       lem04 : {x : Ordinal} → (cx : odef (Cl top (downHOD L OL p)) x )  → record { elt = x ; A∋elt = proj1 cx } p≤ p
       lem04 {x} ⟪ lx , csl ⟫  with p∨¬p (odef (downHOD L OL p) x)
       ... | case1 dx = p≤-resp ? ? (lem03 dx)
       ... | case2 ndx = ⊥-elim (ndx ?) where -- (eq→ *iso (csl ? ? ? )  ))
           -- → odef (downHOD L OL p) x  ∨ ( (  ¬ (odef (downHOD L OL p) x )) ∧ ? ) -- (cs : some CS) ⊆ d → odef cs x
           lem06 : odef (CS top) (& ( L  ＼  downHOD L OL p))
           lem06 = ?
       lem05 : {x : Ordinal} → odef (Interior top (Cl top (downHOD L OL p))) x → ? 
       lem05 = ?

    ROH-lem04 : (L : HOD) (OL : OrderedHOD L)  → (u : HODElement (Power L)) → (ou : odef (Topology.OS (TOPP L OL)) (elt u))
        → ((  Interior (TOPP L OL) (Cl (TOPP L OL) (* (elt u)))) ⊆ (* (elt u))) ⇔   ROlem03 L OL u ou
    ROH-lem04 L OL u ou = ⟪ lem01 , ? ⟫ where
       open Topology
       open OrderedHOD OL
       top = TOPP L OL
       -- lem30 : (a x : Ordinal) → odef (OS top) a → odef (Cl top (* a))  x → ?
       -- lem30 a x oa ⟪ lx , csl ⟫ = {! !} where
       --      lem31 : ?
       --      lem31 = csl
       lem01 :  Interior top (Cl (TOPP L OL) (* (elt u))) ⊆ * (elt u) → ROlem03 L OL u ou
       lem01 iu = record { r = ? ; r-wld = ? ; prop = lem04 } where
          -- u contains
          lem02 :  Interior top (Cl top (* (elt u))) ⊆ * (elt u)
          lem02 {x}  ix = iu ix
          lem11 : Union (ROH-lem05 L OL u ou)  =h= (* ( elt u)  )   
          lem11 = down-lem01 L OL u ou
          lem13 : {x : Ordinal} → odef (Interior top (Cl (TOPP L OL) (Union (ROH-lem05 L OL u ou)))) x → odef (* (elt u)) x
          lem13 {x} ⟪ lx , record { v = v ; nv = record { u = w ; ou = ow ; ux = ux ; v⊆P = v⊆P ; u⊆v = u⊆v } ; v⊆A = v⊆A } ⟫ = {! !} where
              lem14 : {z : Ordinal} → odef (* v) z → odef (Cl (TOPP L OL) (Union (ROH-lem05 L OL u ou))) z
              lem14 = v⊆A 
              ew : HODElement (Power L)
              ew = record { elt = w ; A∋elt = ? }
              lem15 : Union (ROH-lem05 L OL ew ow)  =h= (* w  )   
              lem15 = down-lem01 L OL ew ow

          r : HODElement L →  HODElement L
          r = ?
          lem04 : (q : HODElement L ) → ¬ ( odef (* (elt u)) (elt q) ) → ( r≤q : r q p≤ q ) → (s  : HODElement L ) → s p≤ r q
             → ¬ ( odef (* (elt u)) (elt s)  )
          lem04 q nuq r≤q s s≤q = ? where
              lem03 : {x : Ordinal } → ¬ ( odef (* (elt u)) x ) → ¬ ( odef (Interior top (Cl top (* (elt u))) ) x )
              lem03 nix = contra-position iu nix
              lem05 : ¬ ( odef (Interior top (Cl top (* (elt u))) ) (elt q) )
              lem05 = lem03 nuq
              lem06 : ¬ ( odef (* (elt u)) (elt q) )
              lem06 = nuq
              lem07 : ( odef (* (elt u)) (elt s)  ) →
                  ( odef (Interior top (Cl top (* (elt u))) ) (elt q) )
              lem07 us = ⟪ ? , record { v = ? ; nv = record { u = & lem22 ; ou = ? ; ux = lem08 ; v⊆P = ?; u⊆v = ?} ; v⊆A = lem10 } ⟫  where
                 0<u : o∅ o< elt u
                 0<u = ? 
                 pu : HODElement (Power L)
                 pu = record { elt = elt u ; A∋elt = OS⊆PL top ou }
                 lem23 = downHOD∈OS L OL ?
                 lem20 : ? -- ROH-lem00 L OL ? ou 0<u
                 lem20 = down-lem00 L OL ? ou
                 lem22 : HOD
                 lem22 = ? -- downHOD L OL (lem20 .ROH-lem00.p)
                 lem21 : ? -- downHOD L OL (lem20 .ROH-lem00.p) ⊆ (* (elt u))
                 lem21 = ? -- ROH-lem00.dp⊆u lem20
                 lem08 : odef ? (elt q)
                 lem08 = ?
                 lem09 : OpenP L OL ?
                 lem09 = record { u⊆P = ? ; is-open = λ x y ux eq → ?  }
                 lem10 : {x : Ordinal} → odef (* ?) x → odef (Cl top (* (elt u))) x
                 lem10 {x} rx = ⟪ ?  , ? ⟫
       lem40 :  ROlem03 L OL u ou → Interior top (Cl (TOPP L OL) (* (elt u))) ⊆ * (elt u)
       lem40 record { r = r ; r-wld = r-wld ; prop = prop } {x} ⟪ lx , record { v = v
           ; nv = record { u = u1 ; ou = ou1 ; ux = ux ; v⊆P = v⊆P ; u⊆v = u⊆v } ; v⊆A = v⊆A } ⟫ = {! !}

    ROH-lem01 : (L : HOD) (OL : OrderedHOD L)  → (u : HODElement (Power L)) → (ou : odef (Topology.OS (TOPP L OL)) (elt u))
        → (odef (ROH L (TOPP L OL)) (elt u)) ⇔ ( ROlem03 L OL u ou  )
    ROH-lem01 L OL u ou =  ⟪ lem00 , ? ⟫ where
       open Topology
       open OrderedHOD OL
       lem01 : OpenP L OL (elt u)
       lem01 = ou
       lem00 : odef (ROH L (TOPP L OL)) (elt u) →  ROlem03 L OL u ou
       lem00 ⟪ u⊆L , u=int ⟫  = record { r = f ; r-wld = ? ; prop = lem03 } where
          lem02 : * (elt u) =h= Interior (TOPP L OL)  (Cl (TOPP L OL) (* (elt u)))
          lem02 = ord→== ( trans &iso u=int )
          lem001 : {z : Ordinal} → odef (Interior (TOPP L OL)  (Cl (TOPP L OL) (* (elt u)))) z → odef (* (elt u)) z
          lem001 = eq← lem02
          lem002 : {z : Ordinal} → ¬ (odef (Interior (TOPP L OL)  (Cl (TOPP L OL) (* (elt u)))) z )→ ¬ ( odef (* (elt u)) z )
          lem002 = contra-position ( eq→  lem02 )
          lem003 : {z : Ordinal} → ( odef (Interior (TOPP L OL)  (Cl (TOPP L OL) (* (elt u)))) z → ? )
          lem003 {z} ⟪ lz , record { v = v ; nv = record { u = u ; ou = ou ; ux = ux ; v⊆P = v⊆P ; u⊆v = u⊆v } ; v⊆A = v⊆A } ⟫ = {! !} where
             lem004 : {x : Ordinal} → odef (* v) x → ((c : Ordinal) → odef (CS (TOPP L OL)) c → * u ⊆ * c → odef (* c) x)  → odef (Cl (TOPP L OL) (* u)) x
             lem004 {x} vx csl = ⟪ ? , csl   ⟫
             lem005 : OpenP L OL u
             lem005 = ou
             lem006 : odef (* u) ?
             lem006 = OpenP.is-open ou ? ? ? ? ?
          f : (q : HODElement L) → HODElement L
          f q with p∨¬p ( elt q ≡ elt u)
          ... | case1 eq = ?
          ... | case2 ne = record { elt = Separate.sep (TOPP-Separate L OL {q} {?} ? )
             ; A∋elt = OS⊆PL (TOPP L OL) (Separate.os (TOPP-Separate L OL {q} {?} ?)) _ ? }
          lem04 : ( x y : Ordinal) → ( ux : odef ( * (elt u)) x) → (py : odef L y)
             → record { elt = y ; A∋elt  = py } p≤ record { elt = x ; A∋elt = OpenP.u⊆P ou ux }  →  odef (* (elt u)) y
          lem04 = OpenP.is-open ou
          lem03 : (q : HODElement L) → ¬ odef (* (elt u)) (elt q) → f q p≤ q → (s : HODElement L)
              → s p≤ (f q) → ¬ odef (* (elt u)) (elt s)
          lem03 q nuq fq≤q s s≤fq us with p∨¬p ( elt q ≡ elt u)
          ... | case1 eq = nuq ?
          ... | case2 ne with eq→ lem02 us
          ... | ⟪ ls , record { v = v ; nv = record { u = u1 ; ou = ou1 ; ux = ux ; v⊆P = v⊆P ; u⊆v = u⊆v } ; v⊆A = v⊆A } ⟫ = nuq lem07 where
             lem05 :  OpenP L OL u1
             lem05 = ou1
             lem06 : ( x y : Ordinal) → ( ux : odef ( * u1) x) → (py : odef L y)
                 → record { elt = y ; A∋elt  = py } p≤ record { elt = x ; A∋elt = OpenP.u⊆P ou1 ux }  →  odef (* u1) y
             lem06 = OpenP.is-open ou1
             lem07 : odef (* (elt u)) (elt q)
             lem07 = ? -- lem06 ? (elt q) ?  ? ?
             lem08 : odef (* u1) (elt q)
             lem08 = lem06 ? (elt q) ?  ? ?
       lem10 :  ROlem03 L OL u ou  → odef (ROH L (TOPP L OL)) (elt u)
       lem10 ro = ⟪ ? , (trans (sym &iso) ( ==→o≡ record { eq→ = ? ; eq← = ? } )) ⟫


    RO : (L : HOD)  (∋-p : (Q : HOD) → Q ⊆ L → ( x : HOD) → Dec0 ( x ∈ Q ))
         → (OL : OrderedHOD L )
         → BooleanAlgebra {n} {n} (HODElement (ROH L (TOPP L OL)))
    RO L ∋-p OL =  record { _≈_ = λ x y → (* (elt x)) =h= (* (elt y)) ; b1 = record { elt = & L ;  A∋elt =  ⟪ (λ lt → eq→ *iso lt ) , lem01 ⟫   }
          ; b0 = record { elt =  o∅  ;  A∋elt =  ⟪ (λ {x} lt → ⊥-elim (¬x<0 (eq→ o∅==od∅ lt) )) , lem00  ⟫ }
      ; -_ = λ x → record { elt = & ( L ＼ (Cl (TOPP L OL) (* (elt x)))) ; A∋elt = lem20 {x} }
      ; _+_ = λ x y → record { elt = & (Interior (TOPP L OL) (Cl (TOPP L OL) ((* (elt x)) ∪ (* (elt y)))))
          ; A∋elt = lem400 x y    }
      ; _x_ = λ x y → record { elt = & ((* (elt x)) ∩ (* (elt y))) ; A∋elt = ? }
       ; isBooleanAlgebra = record {
         isEquivalence = record { refl = ==-refl ; sym = ==-sym ; trans = ==-trans }
         ; x-resp = λ {f} {g} {h} {i} f=g h=i → ==-trans *iso ( ==-trans ?  (==-sym *iso))
         ; +-resp =  λ {f} {g} {h} {i} f=g h=i → ==-trans *iso (==-trans ?  (==-sym *iso)) ; neg-resp = λ {f} {g}  f=g → record { eq→ = λ lt → eq← *iso ⟪ proj1 ( eq→ *iso lt ) , (λ lt1 → proj2 (eq→ *iso lt) ?  ) ⟫
             ; eq← = λ lt → eq← *iso ⟪ proj1 ( eq→ *iso lt ) , (λ lt1 → proj2 (eq→ *iso lt) ?  ) ⟫ }
         ; +-assoc = λ {a} {b} {c} →  record { eq→ = λ lt → eq← *iso ?   ; eq← = λ lt → eq← *iso ?  }
         ; x-assoc = λ {a} {b} {c} →
            record { eq→ = λ lt → eq← *iso ?
                   ; eq← = λ lt → eq←  *iso ? }
         ; +-sym = λ {a} {b} →  record { eq→ = λ {x} lt → eq← *iso ?  ; eq← = λ  lt → eq← *iso ?   }
         ; x-sym = λ {a} {b} →  record { eq→ = λ lt → eq← *iso ? ; eq← = λ lt → eq← *iso ? }
         ; +-aab = λ {a} {b} →  record { eq→ = λ lt → ? ; eq← = λ lt → eq← *iso ?  }
         ; x-aab = λ {a} {b} →  record { eq→ = λ lt → ?  ; eq← = λ ax →  eq← *iso ?     }
         ; +-dist = λ {p} {q} {r} → ?
         ; x-dist = λ {p} {q} {r} → ?
         ; a+0 = λ {a} →  record { eq→ = λ lt →  ? ; eq← = λ lt → eq← *iso ?  }
         ; ax1 = λ {a} →  record { eq→ = λ lt → ? ; eq← = λ ax → ? } -- eq← *iso ⟪ ax , eq← *iso (OS⊆PL H (A∋elt a) _ ax)  ⟫  }
         ; a+-a1 = λ {a} →  record { eq→ = λ lt → eq← *iso ?
             ; eq← = λ lt → eq← *iso  ?   }
         ; ax-a0 =  λ {a} →  record { eq→ = λ lt → ⊥-elim ?
               ; eq← = λ lt → ⊥-elim ( ¬x<0 ( eq→ o∅==od∅ lt )) }
           } } where
       open Topology
       ROE = HODElement (ROH L (TOPP L OL))
       open OrderedHOD OL
       top = TOPP L OL
       lem100 : {u x y : HODElement L} {z : Ordinal } → odef (OS top ) (elt u) → odef (* (elt u)) (elt x) → y p≤ x → odef (* (elt u)) (elt y)
       lem100 {u} {x} {y} ou ux y≤x = OpenP.is-open ou _ _ ux (A∋elt y) (p≤-resp ? ? y≤x )
       lem09 : (x : Ordinal) → (* x) ⊆ od∅ → x ≡ o∅
       lem09 x lt with trio< x o∅
       ... | tri< a ¬b ¬c = ⊥-elim ( ¬x<0 a  )
       ... | tri≈ ¬a b ¬c = b
       ... | tri> ¬a ¬b c = ⊥-elim ( o≤> (subst₂ (λ j k → j o< k ) &iso (cong osuc ord-od∅) lem10  ) c) where
         lem10 : & (* x) o< osuc (& od∅ )
         lem10 = ⊆→o≤  lt
       lem08 : (x : Ordinal) → (nv : InteriorR top  od∅ x)  → InteriorR.v nv ≡ o∅
       lem08 x nv = lem09 _ (InteriorR.v⊆A nv)
       lem11 : OpenP L OL (& L )
       lem11 = record { u⊆P = λ lt → eq→ *iso lt  ; is-open = λ x y ux Ly lt → eq← *iso Ly  }
       lem14 : (x : Ordinal) → odef od∅  x → ⊥
       lem14 x lt = ⊥-elim ( ¬x<0 lt  )
       lem13 : (x : Ordinal) → odef (* o∅ ) x → ⊥
       lem13 x lt = lem14 _ (eq→  o∅==od∅ lt )
       lem12 : & L ≡ & (L ＼ * o∅)
       lem12 = ==→o≡ record { eq→ = λ lx → ⟪ lx , (λ lt → lem13 _ lt ) ⟫  ; eq← = λ lt → proj1 lt  }
          -- open BAlgebra O HODAxiom ho< L ∋-p
       lem06 : Cl top (* o∅) =h= * o∅
       lem06 = record { eq→ = λ {x} lt → proj2 lt o∅ ⟪ (λ lt1 →  ⊥-elim (lem13 _ lt1) )  , subst (λ k → OpenP L OL k ) lem12 lem11 ⟫  (λ lt → lt )
          ; eq← = λ lt → ⊥-elim ( ¬x<0 (eq→ o∅==od∅ lt)  ) }
       lem02 : (x : Ordinal) → ¬ ( InteriorR top (Cl top (* o∅)) x )
       lem02 x lt = ⊥-elim ( ¬x<0 (eq→ lem03 ( Neighbor.ux (InteriorR.nv lt ) ))) where
          lem04 : {x : Ordinal} → (* (InteriorR.v lt )) ⊆ (Cl top (* o∅))
          lem04 = InteriorR.v⊆A lt
          lem05 : {x : Ordinal } → (* (Neighbor.u (InteriorR.nv lt ))) ⊆ (* o∅)
          lem05 {y} lt1 = eq→ lem06 (lem04 {y} ( Neighbor.u⊆v (InteriorR.nv lt) lt1  ) )
          lem03 : (* (Neighbor.u (InteriorR.nv lt ))) =h= od∅
          lem03 = record { eq→ = λ {y} lt1 → eq→ o∅==od∅ (lem05 {y} lt1 ) ; eq← = λ lt → ⊥-elim ( ¬x<0 lt  ) }
       lem00 : o∅ ≡ & (Interior top (Cl top (* o∅)))
       lem00 = trans (sym ord-od∅) (==→o≡ record { eq→ = λ lt → ⊥-elim ( ¬x<0 lt ) ; eq← = λ lt → ⊥-elim ( lem02 _ (proj2 lt)) } )
       lem01 : & L ≡ & (Interior top (Cl top (* (& L))))
       lem01 = ==→o≡ record { eq→ = λ lt → ⟪ lt ,
             record { v = & L ; nv = record { u = & L ; ou = lem11 ; ux = eq← *iso lt ; v⊆P = λ lt → eq→ *iso lt ; u⊆v = λ lt → lt }
                ; v⊆A = λ lx → ⟪ eq→ *iso lx , (λ y lc L⊆c → L⊆c lx ) ⟫ } ⟫
           ; eq← = λ lt → proj1 lt }

       lem30 : HODElement (ROH L top) → HODElement (Power L)
       lem30 er = record { elt = elt er ; A∋elt = λ z lt → proj1 (A∋elt er) lt }
       negcl : (x : HODElement (ROH L top)) → HOD
       negcl x = Cl top  (* (& (L ＼ Cl top (* (elt x)))))
       lem40 :  {a b : HOD} → a =h= b →  (L ＼ a ) =h=  (L ＼ b)
       lem40 {a} {b} a=b = record { eq→ = λ lt → ⟪ proj1 lt , (λ lt1 → proj2 lt (eq← a=b lt1) ) ⟫
          ; eq← = λ lt → ⟪ proj1 lt ,  (λ lt1 → proj2 lt (eq→  a=b lt1) ) ⟫ }

       lem39 :  {A B C : HOD } → A ⊆ B → (L ＼ A ) ⊆ C  → (L ＼ B) ⊆ C
       lem39 {A} {B} {C} ab lac {x} lbc  = lac ⟪ proj1 lbc , (λ ax → proj2 lbc (ab ax)  ) ⟫

       lem300 : {x : ROE} → (* (elt x)) =h= Interior top  (Cl top  (* (elt x)))   -- from Regular open set definition
       lem300 {x} = ord→== ( trans &iso (proj2 ( A∋elt x )))

       lem20 : {x : ROE} →  * (& (L ＼ Cl top (* (elt x)))) ⊆ L ∧ (& (L ＼ Cl top (* (elt x))) ≡
             & (Interior top (Cl top (* (& (L ＼ Cl top (* (elt x))))))))
       lem20 {x} = ⟪ (λ lt → (proj1 (eq→ *iso lt))) , ==→o≡ record { eq→ = lem21 ; eq← = λ {z} lt → lem33 (eq→ (Interrior-cong top lem31 ) lt ) } ⟫ where
          lem21 : {z : Ordinal} → odef ((L ＼ Cl top (* (elt x)))) z
             → odef (Interior top (Cl top (* (& (L ＼ Cl top (* (elt x))))))) z
          lem21 {z} ⟪ lz , ne ⟫ = ⟪ lz ,  record { v = & lem200 ; nv = record { u = _ ; ou = lem202
                 ; ux = lem201 ; v⊆P = λ lt → proj1 (eq→ *iso lt) ; u⊆v = λ lt → lt  } ; v⊆A = lem203 } ⟫ where
             lem22 : odef (Cl top (* (elt x))) z → ⊥
             lem22 = ne
             lem200 : HOD
             lem200 = L ＼ Cl top (* (elt x))
             lem201 : odef (* (& lem200)) z
             lem201 = eq← *iso ⟪ lz , ne ⟫
             lem202 : OpenP L OL (& lem200)
             lem202 = P＼CS=OS top (CS∋Cl top (* (elt x)) )
             lem203 : {w : Ordinal} → odef (* (& lem200)) w → odef (Cl top (* (& (L ＼ Cl top (* (elt x)))))) w
             lem203 {w} clw = u⊆Clu top (* (& (L ＼ Cl top (* (elt x))))) (λ lc → proj1 (eq→ *iso lc) ) clw
          lem31 : (Cl top (* (& (L ＼ Cl top (* (elt x)))))) =h= (Cl top (L ＼ Cl top (* (elt x))))
          lem31 = Cl-cong {L} {(* (& (L ＼ Cl top (* (elt x)))))} {(L ＼ Cl top (* (elt x)))} top *iso
          lem33 : {z : Ordinal} → odef (Interior top (Cl top (L ＼ Cl top (* (elt x))))) z
              → odef ((L ＼ Cl top (* (elt x)))) z  -- extrnal without boundary
          lem33 {z} ⟪ lz , record { v = v ; nv = nv ; v⊆A = v⊆A } ⟫ = ⟪ lz , ( λ clz → lem26 (proj2 clz) )  ⟫ where
              open BAlgebra O HODAxiom ho< L ∋-p
              cclx = (Cl top (L ＼ Cl top (* (elt x)))) -- extrnal including boundary
              lem26  : (clz :  (c : Ordinal) →  odef (CS top) c →  * (elt x) ⊆ * c → odef (* c) z ) → ⊥
              lem26 clz  = proj2 lem03 (Neighbor.ux nv) where
                  -- z is not in * (elt x), and not on the boundary, because it is the interior
                  lem24 : {w : Ordinal} → odef (* v) w → odef (Cl top  (L ＼ Cl top (* (elt x)))) w
                  lem24 = v⊆A
                  lem28 : Neighbor top z v
                  lem28 = nv
                  --  odef (* (Neighbor.u nv)) z     z is in external without boundary
                  --  odef (Cl top (* (elt x))) z  z is in internal including boundary
                  lem07 : {w : Ordinal} → ¬ odef cclx w → ¬ odef (* (Neighbor.u nv)) w
                  lem07 = contra-position ( λ nuw → v⊆A (Neighbor.u⊆v nv nuw ))

                  lem16 : {w : Ordinal} → odef (* (elt x)) w → ¬ ( odef cclx w )
                  lem16 {w} xw cw = proj2 lem312 cw  where
                       lem311 : odef L w ∧ InteriorR top (Cl top  (* (elt x))) w   -- internal excluding boundary
                       lem311 = eq→ (lem300 {x}) xw
                       lem312 : odef (L ＼  Cl top (L ＼  (Cl top  (* (elt x))) )) w
                       lem312 = eq→ (Interior-Cl top (Cl top  (* (elt x)))) (eq→ (lem300 {x}) xw ) -- from regular open set
                  lem15 : {w : Ordinal} → odef (* (elt x)) w → odef (* (& (L ＼ * (Neighbor.u nv)))) w  -- external
                  lem15 {w} xw = eq← *iso ⟪ proj1 (A∋elt x) xw , lem07 (lem16 xw)  ⟫
                  lem10 : odef (CS top) ( &  (L ＼ (* (Neighbor.u nv))) )
                  lem10 = P＼OS=CS top (subst (λ k → odef (OS top) k) (sym &iso)  (Neighbor.ou nv) )
                  lem03 :  odef (L ＼ (* (Neighbor.u nv))) z
                  lem03 = eq→ *iso ( clz ( &  (L ＼ (* (Neighbor.u nv))) ) lem10 lem15 )
       lem400 : (x y : ROE ) → ( * (& (Interior top (Cl top (* (elt x) ∪ * (elt y))))) ⊆ L) ∧
        (& (Interior top (Cl top (* (elt x) ∪ * (elt y))))
         ≡ & (Interior top (Cl top (* (& (Interior top (Cl top (* (elt x) ∪ * (elt y)))))))))
       lem400 x y = ⟪ (λ lt → proj1 (eq→ *iso lt))  , ==→o≡ lem401 ⟫ where
           lem401 : (Interior top (Cl top (* (elt x) ∪ * (elt y)))) =h=
               (Interior top (Cl top (* (& (Interior top (Cl top (* (elt x) ∪ * (elt y))))))))
           lem401 = record { eq→ = ? ; eq← = ? }

