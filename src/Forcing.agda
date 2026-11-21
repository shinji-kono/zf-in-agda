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
open import Data.Nat.Properties using ( <-cmp ; ≤-<-trans ; <-trans ;  ≤-trans ; <-≤-trans )
open import BoolAlgebra

import Relation.Binary.Reasoning.Setoid as EqR

--
--   M is a coutable model of ZF
--   M ∋ B is complete M Boolean Algebra
--   G ⊆ B is a gerative filter including B ∋ b, b ≠ od∅
--
--   An = { M∋Ai : (Ai ⊆ B)  ∧ Ai ≠ od∅ }
--       M is a Union An

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
    open import ZEquiv O HODAxiom ho<

    open HODElement
    import BAlgebra

    open Bijection
    -- 補題 23.1 Bの任意の要素 b ≠ 0 に対して、bを含む M-生成超フィルターが存在する

    --
    -- Original Book uses Boolean Algebra on a HOD Set
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
       ⊆→≤  :　{ p q :  B } → * (elt p) ⊆ * (elt q) → p ≤ q
       ⊆→≤ {p} {q}  = proj1 ( HBA-⊆ L LDec H p q )
       ≤→⊆  :　{ p q : B }  → p ≤ q → * (elt p) ⊆ * (elt q)
       ≤→⊆  {p} {q}  = proj2 ( HBA-⊆ L LDec H p q )
       0<b→¬b≈od∅ : {a : B } → b0 < a → ¬ ( (* (elt a))  =h= od∅ )
       0<b→¬b≈od∅ {a} 0<a eq = ⊥-elim (proj1 0<a (==-sym (==-trans eq (==-sym o∅==od∅ ) ) ) )
       a=0∨0<a : {a : B } → (b0 ≈ a) ∨ (b0 < a)
       a=0∨0<a {a} with p∨¬p (b0 ≈ a)
       ... | case1 eq = case1 eq
       ... | case2 ne = case2 ⟪ ne , 0≤a a ⟫
       ≈→≡  : {a b : B } → a ≈ b → elt a ≡ elt b
       ≈→≡ {a} {b} a=b  = *=h=*→≡ a=b
       x=∩  : {a b : B } → * ( elt (a x b )) =h= ( (* ( elt a )) ∩ (* ( elt b ) ))
       x=∩  {a} {b} = record { eq→ = λ ab → eq→ *iso ab ; eq← = λ ab → eq← *iso ab } 
       +=∪  : {a b : B } → * ( elt (a + b )) =h= ( (* ( elt a )) ∪ (* ( elt b ) ))
       +=∪  {a} {b} = record { eq→ = λ ab → eq→ *iso ab ; eq← = λ ab → eq← *iso ab } 
       -- <-and  : {a b : B } → b0 < a → b0 < b → b0 < (a x b), we cannot say this

--    record CM : Set (Suc (Suc n)) where
--      field
--          countable : Bijection ℕ (Ordinals.Ordinal O)

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

    -- we cannot have a bijection here. Only a part of subset of Boolean Algebra is in our HOD Set.
    -- we are working on countable model, so only countable number of set of Power B is in M
    --
    -- M は可算なので整列可能
    --
    -- { A ∈  M : ∅ ≠ A ⊆ B } = { A0 , A1, A2, ... An }
    --
    record AN  (L : HOD) (PB : HODBooleanAlgebra L ) : Set (Level.suc n) where
       field
          ip : ℕ → HODElement (Power (BAlgebra.HBAR.OS (H PB) ))
          ip-inject : (i j : ℕ ) → elt (ip i) ≡ elt (ip j ) → i ≡ j
          ip=0 : elt (ip 0) ≡  o∅
          --  this is come from M is coutable, but it's Ok
          abi : (A : HOD) → (A ⊆ (BAlgebra.HBAR.OS (H PB) )) → ℕ
          is-abi : (A : HOD) → (ab : A ⊆ (BAlgebra.HBAR.OS (H PB) )) → elt (ip (abi A ab )) ≡ & A
       imap : ℕ → HODElement (Power (BAlgebra.HBAR.OS (H PB) ))
       imap i = ip (suc i)
       imap>0 : (i : ℕ) → ¬ ( elt (imap i) ≡ o∅ )
       imap>0 i eq = nat-<≡ (subst (λ k → k n≤ i) (ip-inject _ _ (trans ip=0 (sym eq)) ) z≤n )
       imap-ne : (i : ℕ) → od (* (elt (imap i))) == od od∅ → ⊥
       imap-ne i eq = imap>0 i (trans (sym &iso) (trans (==→o≡  eq) ord-od∅)  )
       abi>0 : (A : HOD) → (ab : A ⊆ (BAlgebra.HBAR.OS (H PB) )) → o∅ o< (& A) → 0 Data.Nat.< abi A ab
       abi>0 A ab 0<A with  <-cmp 0 (abi A ab)
       ... | tri< a ¬b ¬c = a
       ... | tri≈ ¬a b ¬c = ⊥-elim ( o<¬≡ (sym lem00) 0<A ) where
           lem00 : (& A) ≡ o∅ 
           lem00 = trans (sym (is-abi A ab)) (subst (λ k → elt (ip k) ≡ o∅ ) b ip=0 )

    PAn : (L : HOD) → (PB : HODBooleanAlgebra L ) → AN L PB → ℕ → BPred (HODBooleanAlgebra.B PB) (ba PB)
    PAn L PB an i = record { pred = λ p → odef (* (elt (AN.imap an i))) (elt p)
       ; pcong = λ x y eq → ⟪ ( λ lt → subst (λ k → odef (* (elt (AN.imap an i))) k ) (*=h=*→≡ eq) lt )
          , ( λ lt → subst (λ k → odef (* (elt (AN.imap an i))) k ) (sym (*=h=*→≡ eq))  lt )  ⟫ }

    -- BはM完備なので最小上界が存在する
    --
    -- ∧ an
    ∧an : (L : HOD) → (PB : HODBooleanAlgebra L ) → AN L PB → ℕ → B PB
    ∧an L PB an i = IsCompleteBooleanAlgebra.sup ( bc PB ) (PAn L PB an i)

    ∧an-cong : (L : HOD) → (PB : HODBooleanAlgebra L ) → (an : AN L PB) → (i j : ℕ) → i ≡ j → BooleanAlgebra._≈_ (ba PB) (∧an L PB an i) (∧an L PB an j)
    ∧an-cong L PB an i j eq = lem00 where
       open BooleanAlgebra (ba PB)
       open IsBooleanAlgebra (BooleanAlgebra.isBooleanAlgebra (ba PB))
       lem00 : (∧an L PB an i) ≈ (∧an L PB an j)
       lem00 = subst (λ k → (∧an L PB an i) ≈ (∧an L PB an k) ) eq (brefl {∧an L PB an i})

    record AAn (L : HOD) (PB : HODBooleanAlgebra L )  (bi : HODBooleanAlgebra.B PB) (an : AN L PB) : Set n where
       open BooleanAlgebra (ba PB)
       open IsBooleanAlgebra (BooleanAlgebra.isBooleanAlgebra (ba PB))
       field
         oa : Ordinal
         pan : odef (OS PB) oa
       a : B PB
       a = record { elt = oa ; A∋elt = pan  }
       field
         eq1 :  b0 < ( bi x ( - a ))


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
        (i : ℕ) (b : HODBooleanAlgebra.B PB) (bnz : BooleanAlgebra._<_ (ba PB) (BooleanAlgebra.b0 (ba PB)) b) (yy :  BooleanAlgebra._≈_ (ba PB) (( BooleanAlgebra._x_ (ba PB) b ( ∧an L PB an i ))) (BooleanAlgebra.b0 (ba PB)))
          → AAn L PB b an
    b-ai→a1 L PB an i b bnz yy = record { oa = _ ;  pan = pan ;  eq1 = lem10 } where
       open BooleanAlgebra (ba PB)
       open IsBooleanAlgebra (BooleanAlgebra.isBooleanAlgebra (ba PB))
       yy1 : (i : ℕ) → HOD
       yy1 i = minimal (* (elt (AN.imap an i))) (AN.imap-ne an i)
       ayy1 : (i : ℕ) → odef (* (elt (AN.imap an i))) (& (yy1 i))
       ayy1 i = x∋minimal (* (elt (AN.imap an i))) (AN.imap-ne an i)
       pbb : odef (OS PB) (elt b)
       pbb = A∋elt b
       ai-is-sup : (y : B PB) → (i : ℕ) → (ay : odef (* (elt (AN.imap an i))) (elt y)) → y ≤ ∧an L PB an i
       ai-is-sup y i ay = IsCompleteBooleanAlgebra.is-sup ( bc PB ) (PAn L PB an i) y  ay
       yy0 : (i : ℕ) → HODBooleanAlgebra.B PB
       yy0 i = record { elt = & (yy1 i) ; A∋elt = A∋elt (AN.imap an i) _ (ayy1 i) }
       pan : odef (OS PB) (elt (yy0 i))
       pan = A∋elt (yy0 i)
       bi = b
       ai = ∧an L PB an i
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
       lem12 : (b x (- ai )) ≤  (b x (- (yy0 i)))
       lem12 = x-monoˡ-< { - ai } { - (yy0 i)} {b} ( neg-mono-≤ { yy0 i }{ ai } (ai-is-sup (yy0 i ) i (ayy1 i) ) )
       lem11 :  b0 ≈ (b x (- (yy0 i))) → b0 ≈ (b x (- ai ))
       lem11 eq = begin
           b0 ≈⟨ bsym {b x ( - ai) } {b0} ( ≤0→≈ {b x (- ai )} ( resp-≤ {b x (- ai )} {b x (- (yy0 i))} {b x (- ai )} {b0} (brefl {b x (- ai )}) (bsym {b0} {b x (- (yy0 i))} eq) lem12  ) ) ⟩
           b x (- ai ) ∎ where open EqR bSetoid
       lem10 :  b0 < ( b x ( - (yy0 i) ))
       lem10  = ⟪ (λ eq → ⊥-elim (proj1 abn (lem11 eq)  ) ) , (
             begin b0 ≤⟨ proj2 abn ⟩
             b x  (- ai ) ≤⟨ x-monoˡ-< { - ai } { - (yy0 i)} {b} ( neg-mono-≤ { yy0 i }{ ai } (ai-is-sup (yy0 i) i (ayy1 i)) )  ⟩
             b x ( - (yy0 i) ) ∎
          ) ⟫ where
             open BA≤-Reasoning (ba PB)

    ai→a1-cong :  (L : HOD)  (PB : HODBooleanAlgebra L ) (an : AN L PB )
        (i j : ℕ) (bi bj : HODBooleanAlgebra.B PB) (bnzi : BooleanAlgebra._<_ (ba PB) (BooleanAlgebra.b0 (ba PB)) bi)
           (bnzj : BooleanAlgebra._<_ (ba PB) (BooleanAlgebra.b0 (ba PB)) bj)
        (yyi :  BooleanAlgebra._≈_ (ba PB) (( BooleanAlgebra._x_ (ba PB) bi ( ∧an L PB an i ))) (BooleanAlgebra.b0 (ba PB)))
        (yyj :  BooleanAlgebra._≈_ (ba PB) (( BooleanAlgebra._x_ (ba PB) bj ( ∧an L PB an j ))) (BooleanAlgebra.b0 (ba PB)))
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
          eq1 : (j : ℕ) → j Data.Nat.< i → (eq : ((b j) x (∧an L PB an j)) ≈ b0 )
              → (b (suc j)) ≈ ( (b j) x ( - (AAn.a (b-ai→a1 L PB an j (b j) (bnz j ) eq ) )))
          eq2 : (j : ℕ) → j Data.Nat.< i → (neq : ¬ (((b j) x (∧an L PB an j)) ≈ b0 ))
              → (b (suc j)) ≈  ( (b j) x (∧an L PB an j)  )
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
       bi j with  p∨¬p ( (  (Bni2.b (Bn1 L PB an i bn0) i) x (∧an L PB an i)) ≈ b0 )
       ... | case1 eq = ( Bni2.b obni i) x ( - (AAn.a (b-ai→a1 L PB an i (Bni2.b obni i) (Bni2.bnz obni i ) eq ) ))
       ... | case2 ne = ( Bni2.b obni i) x (∧an L PB an i)
       bnzi : (j : ℕ) → b0 < bi j
       bnzi j with  p∨¬p ( (  (Bni2.b (Bn1 L PB an i bn0) i) x (∧an L PB an i)) ≈ b0 )
       ... | case1 eq = AAn.eq1 (b-ai→a1 L PB an i (Bni2.b obni i) (Bni2.bnz obni i ) eq )
       ... | case2 ne = ⟪ (λ eq → ne (bsym {b0} {( Bni2.b obni i) x (∧an L PB an i) } eq) ) , 0≤a (( Bni2.b obni i) x (∧an L PB an i) )  ⟫
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
       eq1 : (j k : ℕ) → k ≡ suc j → j Data.Nat.< suc i → (eq : ((b j) x (∧an L PB an j)) ≈ b0 )
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
           lem00 : (m : ℕ) → m ≡ j → (eq2 : ((b m) x (∧an L PB an m)) ≈ b0 )→ (bi k ) ≈ ( (b m) x ( - (AAn.a (b-ai→a1 L PB an m (b m ) (bnz m) eq2 ) )))
           lem00 m m=j eq2 with Data.Nat.<-cmp m (suc i)
           ... | tri< a ¬b ¬c = lem03 where
               i=m : i ≡ m
               i=m = trans (cong pred (trans (sym b₁) k=sj ) ) (sym m=j )
               lem03 : (bi k ) ≈ ( (Bni2.b obni m) x ( - (AAn.a (b-ai→a1 L PB an m (Bni2.b obni m ) (Bni2.bnz obni m) eq2 ) )))
               lem03 with  p∨¬p ( (  (Bni2.b (Bn1 L PB an i bn0) i) x (∧an L PB an i)) ≈ b0 )
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
                  (  (Bni2.b (Bn1 L PB an i bn0) i) x (∧an L PB an i)) ≈⟨ x-resp
                      {∧an L PB an i} {∧an L PB an m} {Bni2.b (Bn1 L PB an i bn0) i} {Bni2.b (Bn1 L PB an i bn0) m}
                      (∧an-cong L PB an _ _ i=m ) (Bni2.bcong (Bn1 L PB an i bn0) _ _ i=m ) ⟩
                  (  (Bni2.b (Bn1 L PB an i bn0) m) x (∧an L PB an m)) ≈⟨ eq2 ⟩
                  b0 ∎ ) ) where
                      open EqR bSetoid
           ... | tri≈ ¬a b₁ ¬c = ⊥-elim ( nat-≡< b₁ (<-≤-trans (refl-≤≡ (cong suc m=j)) lt ) )
           ... | tri> ¬a ¬b c = ⊥-elim ( nat-≡< (trans (trans (sym b₁) k=sj ) (cong suc (sym m=j) )) (<-trans c a<sa) )
       ... | tri> ¬a ¬b c = ⊥-elim (nat-≤> (subst (λ k →  k n≤ suc i) (sym k=sj) lt ) c )
       eq2 : (j k : ℕ) → k ≡ suc j → j Data.Nat.< suc i → (ne : ¬ (((b j) x (∧an L PB an j)) ≈ b0 ))
              → (b k) ≈ ( (b j) x ( (∧an L PB an j)  ))
       eq2 j k k=sj lt ne with Data.Nat.<-cmp k (suc i)
       ... | tri< a ¬b ¬c = lem00  where
           lem00 : (Bni2.b obni k) ≈ ( (b j) x ( (∧an L PB an j)  ))
           lem00 with Data.Nat.<-cmp j (suc i)
           ... | tri< a₁ ¬b ¬c = subst (λ w → (Bni2.b obni w)
                ≈ ( (Bni2.b obni j) x (∧an L PB an j)) ) (sym k=sj) ( Bni2.eq2 obni j (sx≤py→x≤y (subst (λ w → w Data.Nat.< (suc i)) k=sj a)) ne )
           ... | tri≈ ¬a b ¬c = ⊥-elim ( nat-≤> (refl-≤≡ (sym b)) lt )
           ... | tri> ¬a ¬b c = ⊥-elim ( nat-≤> (<-trans (s≤s refl-≤) c) lt )
       ... | tri≈ ¬a b₁ ¬c = lem00 j refl ne where -- k ≡ suc i, k ≡ suc j
           lem00 : (m : ℕ) → m ≡ j → (eq2 : ¬ (((b m) x (∧an L PB an m)) ≈ b0 ))→ (bi k ) ≈ ( (b m) x  (∧an L PB an j) )
           lem00 m m=j neq2 with Data.Nat.<-cmp m (suc i)
           ... | tri< a ¬b ¬c = lem03 where
               i=m : i ≡ m
               i=m = trans (cong pred (trans (sym b₁) k=sj ) ) (sym m=j )
               i=j : i ≡ j
               i=j = cong pred (trans (sym b₁) k=sj ) 
               lem03 : (bi k ) ≈ ( (Bni2.b obni m) x (∧an L PB an j) )
               lem03 with  p∨¬p ( (  (Bni2.b (Bn1 L PB an i bn0) i) x (∧an L PB an i)) ≈ b0 )
               ... | case1 eq3 = ⊥-elim (neq2 (begin
                  ((Bni2.b (Bn1 L PB an i bn0) m) x (∧an L PB an m)) ≈⟨ x-resp {∧an L PB an m} {∧an L PB an i}
                         {Bni2.b (Bn1 L PB an i bn0) m} {Bni2.b (Bn1 L PB an i bn0) i}
                     (∧an-cong L PB an _ _ (sym i=m) )  (Bni2.bcong (Bn1 L PB an i bn0) _ _ (sym i=m) ) ⟩
                  ((Bni2.b (Bn1 L PB an i bn0) i) x (∧an L PB an i)) ≈⟨ eq3 ⟩
                  b0 ∎ )) where
                     open EqR bSetoid
               ... | case2 ne3 = begin
                   ((Bni2.b (Bn1 L PB an i bn0) i) x  (∧an L PB an i))
                     ≈⟨  x-resp {∧an L PB an i} {∧an L PB an j} {Bni2.b (Bn1 L PB an i bn0) i} {Bni2.b (Bn1 L PB an i bn0) m}
                         (∧an-cong L PB an _ _ i=j ) (Bni2.bcong (Bn1 L PB an i bn0) _ _ i=m ) ⟩
                  ( (Bni2.b (Bn1 L PB an i bn0) m) x  (∧an L PB an j) )  ∎ where
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
               lem03 with  p∨¬p ( (  (Bni2.b (Bn1 L PB an i bn0) i) x (∧an L PB an i)) ≈ b0 )
               ... | case1 eq3 = begin
                  ((Bni2.b obni i) x ( - (AAn.a (b-ai→a1 L PB an i (Bni2.b obni i ) (Bni2.bnz obni i) eq3 ) )))
                      ≤⟨ Bni2.bin2-lem00 obni (Bni2.b obni i) ( - (AAn.a (b-ai→a1 L PB an i (Bni2.b obni i ) (Bni2.bnz obni i) eq3 ) ))  ⟩
                  ( Bni2.b obni i)   ≤⟨  Bni2.bmono obni _ lem04 ⟩
                  ( Bni2.b obni m)   ∎ where
                     open BA≤-Reasoning (ba PB)
               ... | case2 ne3 = begin
                  ((Bni2.b obni i) x (∧an L PB an i)) ≤⟨ Bni2.bin2-lem00 obni (Bni2.b obni i)  (∧an L PB an i)  ⟩
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
          lem04 with p∨¬p ( (  (Bni2.b bj m) x (∧an L PB an m)) ≈ b0 )
          ... | case1 eq = lem05 where
                lem06 :  ((Bni2.b bi m) x (∧an L PB an m)) ≈ b0
                lem06 = btrans {(Bni2.b bi m) x (∧an L PB an m)} {(Bni2.b bj m) x (∧an L PB an m)} {b0}
                    (x-resp  {∧an L PB an m} {∧an L PB an m} {Bni2.b bi m} {Bni2.b bj m} (brefl {∧an L PB an m} ) lem03 ) eq
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
                lem06 :  ¬ ( ((Bni2.b bi m) x (∧an L PB an m)) ≈ b0  )
                lem06 eq = ⊥-elim ( ne (btrans {(Bni2.b bj m) x (∧an L PB an m)} {(Bni2.b bi m) x (∧an L PB an m)} {b0}
                    (x-resp {∧an L PB an m} {∧an L PB an m} {Bni2.b bj m} {Bni2.b bi m}  (brefl {∧an L PB an m}) (bsym {Bni2.b bi m} {Bni2.b bj m} lem03) ) eq ))
                lem05 : Bni2.b bi (suc m) ≈ Bni2.b bj (suc m)
                lem05 = begin
                   Bni2.b bi (suc m)   ≈⟨ Bni2.eq2 bi  m m≤i lem06 ⟩
                   (Bni2.b bi m) x (∧an L PB an m) ≈⟨ x-resp { ∧an L PB an m } { ∧an L PB an m } {Bni2.b bi m} {Bni2.b bj m} ==-refl  lem03 ⟩
                   (Bni2.b bj m) x (∧an L PB an m) ≈⟨ ==-sym ( Bni2.eq2 bj m (Data.Nat.Properties.≤-trans m≤i i≤j) ne ) ⟩
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

    open Filter

    A∧P : (L : HOD) → (PB : HODBooleanAlgebra L ) → (an : AN L PB ) (bni : Bni L PB an) → (A : HOD)
       → BPred (HODBooleanAlgebra.B PB) (ba PB)
    A∧P L PB an bni A = record { pred = λ bp → odef A (elt bp)  ; pcong = λ a b eq → ⟪ (λ aa → lem00 {a} {b} eq aa )  , (λ bb → lem00 {b} {a} (==-sym eq) bb)  ⟫  } where
       lem00 : {a b : HODElement (OS PB)} → (* (elt a)) =h= (* (elt b)) → odef A (elt a) → odef A (elt b)
       lem00 {a} {b} eq aa = subst (λ k → odef A k ) ( subst₂ (λ j k → j ≡ k  ) &iso &iso (==→o≡ eq)  ) aa

    A∧ : (L : HOD) → (PB : HODBooleanAlgebra L ) → (an : AN L PB ) (bni : Bni L PB an) → (A : HOD) → HODElement (OS PB)
    A∧ L PB an bni A = IsCompleteBooleanAlgebra.sup ( bc PB ) (A∧P L PB an bni A )

    A∧-cong : (L : HOD) → (PB : HODBooleanAlgebra L ) → (an : AN L PB ) (bni : Bni L PB an) → (A B : HOD) → A =h= B
        → elt (A∧ L PB an bni A ) ≡ elt (A∧ L PB an bni B )
    A∧-cong L PB an bni A B A=B = subst₂ (λ j k → j ≡ k ) &iso &iso ( ==→o≡ lem00) where
       open BooleanAlgebra (ba PB)
       open IsBooleanAlgebra (BooleanAlgebra.isBooleanAlgebra (ba PB))
       a : HODElement (OS PB)
       a = A∧ L PB an bni A
       b : HODElement (OS PB)
       b = A∧ L PB an bni B
       lem01 : (y : HODElement (OS PB)) → BPred.pred (A∧P L PB an bni A) y → y ≤ (A∧ L PB an bni B )
       lem01 y pax = IsCompleteBooleanAlgebra.is-sup (bc PB) (A∧P L PB an bni B) y (eq→ A=B pax)
       lem02 : (y : HODElement (OS PB)) → BPred.pred (A∧P L PB an bni B) y → y ≤ (A∧ L PB an bni A )
       lem02 y pax = IsCompleteBooleanAlgebra.is-sup (bc PB) (A∧P L PB an bni A) y (eq→ (==-sym A=B) pax)
       lem00 : a ≈ b
       lem00 =  bool-≤≥→≈ {a} {b}
          (IsCompleteBooleanAlgebra.is-minsup (bc PB) (A∧P L PB an bni A ) {b} lem01 )
          (IsCompleteBooleanAlgebra.is-minsup (bc PB) (A∧P L PB an bni B ) {a} lem02 )

    A∧-∧an-cong : (L : HOD) → (PB : HODBooleanAlgebra L ) → (an : AN L PB ) (bni : Bni L PB an) 
           → (i : ℕ) → 0 Data.Nat.< i → (* (elt (A∧ L PB an bni (* (elt (AN.ip an i) ))))) =h= (* (elt ( ∧an L PB an (Data.Nat.pred i ))))
    A∧-∧an-cong L PB an bni zero () 
    A∧-∧an-cong L PB an bni (suc i) 0<i = IsCompleteBooleanAlgebra.sup-cong (bc PB) (A∧P L PB an bni (* (elt (AN.ip an (suc i))))) (PAn L PB an (Data.Nat.pred (suc i))) 
      ⟪ (λ {x} lt → lem00 {x} lt ) , (λ {x} lt → lem01 {x} lt ) ⟫ where
           lem00 :  {x : HODElement (OS PB)} → BPred.pred (A∧P L PB an bni (* (elt (AN.ip an (suc i))))) x → BPred.pred (PAn L PB an (Data.Nat.pred (suc i))) x
           lem00 {x} lt =  lt
           lem01 :  {x : HODElement (OS PB)} → BPred.pred (PAn L PB an (Data.Nat.pred (suc i))) x → BPred.pred (A∧P L PB an bni (* (elt (AN.ip an (suc i))))) x
           lem01 {x} lt = lt 

    genericf : (L : HOD) → (PB : HODBooleanAlgebra L ) → (an : AN L PB ) (bni : Bni L PB an)
        → {A : HOD} → (A⊆F : A ⊆ filter (mf L PB an bni)) → odef (OS PB) (& A) → o∅ o< (& A) → odef (filter (mf L PB an bni)) (elt (A∧ L PB an bni A ))
    genericf L PB an bni {A} A⊆mf oa 0<A = lem01 where
       open BooleanAlgebra (ba PB)
       open IsBooleanAlgebra (BooleanAlgebra.isBooleanAlgebra (ba PB))

       lem05 : ¬ ( odef A (& od∅ ))
       lem05 a0 = MaximumFilter.proper (maxf L PB an bni) (A⊆mf a0)
       lem00 : {a : Ordinal } → odef A a → odef (filter (mf L PB an bni)) a
       lem00 aa = A⊆mf aa
       lem03 : {a : Ordinal} → odef A a → odef (OS PB) a
       lem03 aa = f⊆L (mf L PB an bni) (A⊆mf aa )
       i : ℕ
       i = AN.abi an A lem03
       ab : A ⊆ OS PB
       ab lt =  f⊆L (mf L PB an bni) ( A⊆mf  lt )
       0<i : 0 Data.Nat.< i
       0<i = AN.abi>0 an A ab 0<A  
       lem50 : A =h= od∅ → ⊥ 
       lem50 = 0<P→ne 0<A
       lem04 : elt (AN.ip an i ) ≡ & A
       lem04 = AN.is-abi an A lem03
       lem13 : (* (elt (AN.ip an i ))) =h= A
       lem13 = ord→== (trans &iso lem04 )
       lem17 : (* (elt (AN.imap an (pred i) ))) =h= A
       lem17 = ==-trans (lem18 i 0<i ) lem13   where    -- imap = suc ip 
           lem18 : (i : ℕ) → 0 Data.Nat.< i → (* (elt (AN.imap an (pred i) ))) =h= (* (elt (AN.ip an i )))
           lem18 zero ()
           lem18 (suc i) 0<i = ==-refl
       bn : Bni2 L PB an bni (suc i)
       bn = Bn1 L PB an (suc i) bni 
       bi' : B PB
       bi'  = Bni2.b bn (suc (Data.Nat.pred i))
       bi3 : B PB
       bi3  = Bni2.b bn (Data.Nat.pred i)
       ai : B PB
       ai = A∧ L PB an bni (* (elt (AN.ip an i) ))
       ai3 : B PB
       ai3 = ∧an L PB an (Data.Nat.pred i) 
       ai=ai3 : ai ≈ ai3
       ai=ai3 = A∧-∧an-cong  L PB an bni i 0<i 
       lem37 : (i : ℕ) → 0 Data.Nat.< i → suc (pred i) n≤ suc i
       lem37 zero ()
       lem37 (suc i) 0<i = a≤sa 
       lem14 : (bi3 x ai) ≤ ai
       lem14 = ⊆→≤ PB {bi3 x ai} {ai} (λ lt → proj2 (eq→ *iso lt) )
       lem38 : odef (filter (mf L PB an bni)) (elt bi3)
       lem38 = MaximumFilter.F⊆mf (maxf L PB an bni) ( record { i = pred i ; bx = A∋elt bi3 ; bn≤x = lem39  } ) where
           lem40 : (Bni2.b (Bn1 L PB an (pred i) bni) (pred i)) ≈ (Bni2.b (Bn1 L PB an (suc i) bni) (pred i))
           lem40 = bni2unique L PB an bni _ _ (pred i) (Data.Nat.Properties.≤-trans a≤sa (lem37 i 0<i )) 
               (Bn1 L PB an (pred i) bni) (Bn1 L PB an (suc i) bni) refl-≤  
           lem39 : {x : Ordinal } 
              → odef ( * (elt (Bni2.b (Bn1 L PB an (pred i) bni) (pred i)))) x 
              → odef ( * (elt (Bni2.b (Bn1 L PB an (suc  i) bni) (pred i)))) x
           lem39 {x} lt = eq→ lem40 lt

       lem34 : ¬ ( ( bi3 x ai3 ) ≈ b0 )
       lem34 bxa=0 = MaximumFilter.proper (maxf L PB an bni) lem42 where
           lem44 : (a : B PB) → odef A (elt a) → odef (* (elt (AN.imap an (pred i)))) (elt a)
           lem44 a aa = eq← lem17 aa
           lem43 : (a : B PB) → odef A (elt a) → a ≤ ai3    -- come from the completness
           lem43 a aa = IsCompleteBooleanAlgebra.is-sup (bc PB) (PAn L PB an (Data.Nat.pred i)) a (lem44 a aa)
           lem40 : (a : B PB) → odef A (elt a) → (bi3 x a)  ≈ b0 
           lem40 a aa = begin    -- a ≤ ai3 means   ( a x ai3 ) ≈ a
              bi3 x a ≈⟨ x-resp {a} {a x ai3} {bi3} {bi3} (bsym {a x ai3} {a} (lem43 a aa)) (brefl {bi3}) ⟩ 
              bi3 x (a x ai3 ) ≈⟨ x-assoc {bi3} {a} {ai3} ⟩ 
              (bi3 x a) x ai3  ≈⟨ x-resp {ai3} {ai3} {bi3 x a} {a x bi3} (brefl {ai3}) (x-sym {bi3} {a} ) ⟩ 
              (a x bi3 ) x ai3  ≈⟨ bsym {a x (bi3 x ai3) } {(a x bi3) x ai3} ( x-assoc {a} {bi3} {ai3} )  ⟩ 
              a x ( bi3  x ai3 )  ≈⟨ x-resp {bi3 x ai3} {b0} {a} {a} bxa=0 (brefl {a}) ⟩ 
              a x b0  ≈⟨ x-sym {a} {b0} ⟩ 
              b0 x a  ≈⟨ 0≤a a ⟩ 
              b0 ∎ where open EqR bSetoid 
           lem46 : (a : B PB) → odef (OS PB) (& (* (elt bi3) ∩ * (elt a)))
           lem46 a = o∩ PB (subst (λ k → odef (OS PB) k ) (sym &iso) (A∋elt bi3)) (subst (λ k → odef (OS PB) k ) (sym &iso) (A∋elt a))
           lem45 : (a : B PB ) →  & (* (elt bi3) ∩ * (elt a)) ≡ elt (bi3 x a)
           lem45 a = trans (==→o≡ record { eq→ = λ ab → eq← *iso ab  ; eq← = λ ab → eq→ *iso ab  }  )  &iso
           -- bi3 x a is in the filter, because of ∩ 
           lem41 : (a : B PB) → odef A (elt a) → odef (filter (mf L PB an bni)) (elt (bi3 x a) )
           lem41 a aa = subst (λ k → odef (filter (mf L PB an bni)) k ) (lem45 a) ( filter2 (mf L PB an bni) 
               (subst (λ k → odef (filter (mf L PB an bni)) k ) (sym &iso) lem38)  
               (subst (λ k → odef (filter (mf L PB an bni)) k ) (sym &iso) (lem00 aa)) (lem46 a) )
           am : B PB
           am = record { elt = & (minimal A lem50 ) ; A∋elt = ab (x∋minimal A lem50) }
           is-am : odef A (elt am)
           is-am = x∋minimal A lem50 
           lem42 : odef (filter (mf L PB an bni)) (& od∅ )
           lem42 = subst ( λ k → odef (filter (mf L PB an bni)) k ) (trans (≈→≡ PB {bi3 x am} {b0} (lem40 am is-am )) (sym ord-od∅)  ) ( lem41 am is-am  )
       lem33 : bi' ≈ ( bi3 x ai3 )    -- difinition of the filter
       lem33 = Bni2.eq2 bn (Data.Nat.pred i) (lem37 i 0<i) lem34  

       lem12 : odef (filter (BnFilter L PB an bni)) (elt bi')
       lem12 = record { i = suc (Data.Nat.pred i) ; bx = A∋elt bi' ; bn≤x = lem35   } where
           lem36 : (Bni2.b (Bn1 L PB an (suc (pred i)) bni) (suc (pred i))) ≈ (Bni2.b (Bn1 L PB an (suc i) bni) (suc (pred i)))
           lem36 = bni2unique L PB an bni _ _ (suc (pred i)) (lem37 i 0<i ) (Bn1 L PB an (suc (pred i)) bni) (Bn1 L PB an (suc i) bni) refl-≤ 
           lem35 : {x : Ordinal } 
               → odef ( * (elt (Bni2.b (Bn1 L PB an (suc (pred i)) bni) (suc (pred i))))) x 
               → odef ( * (elt (Bni2.b (Bn1 L PB an (suc i)        bni) (suc (pred i))))) x
           lem35 {x} lt = eq→ lem36 lt
       lem16 : odef (filter (BnFilter L PB an bni)) (elt (bi3 x ai))
       lem16 = subst ( λ k → odef (filter (BnFilter L PB an bni)) k) (≈→≡ PB {bi'} {bi3 x ai} 
             (btrans {bi'} {bi3 x ai3} {bi3 x ai} lem33 (x-resp {ai3} {ai} {bi3} {bi3} (bsym {ai} {ai3} ai=ai3) (brefl {bi3} ) ) ) ) lem12
       --  (bi3 x ai) is in the filter, then (bi3 x ai) ≤ ai makes ai is in the filter
       lem15 : odef (filter (BnFilter L PB an bni)) (elt ai)
       lem15 = filter1 (BnFilter L PB an bni) (A∋elt ai) (subst (λ k → odef (filter (BnFilter L PB an bni)) k ) (sym &iso) lem16 )
          ( λ bix → eq→ *iso (≤→⊆ PB {bi3 x ai} {ai} lem14 bix ) )
       lem021 : odef (filter (mf L PB an bni)) (elt ai)
       lem021 = MaximumFilter.F⊆mf (maxf L PB an bni) lem15
       lem01 : odef (filter (mf L PB an bni))  (elt (A∧ L PB an bni A ))
       lem01 = subst (λ k → odef (filter (mf L PB an bni)) k) (A∧-cong L PB an bni (* (elt (AN.ip an i))) A lem13 ) lem021

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

