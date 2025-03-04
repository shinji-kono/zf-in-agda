{-# OPTIONS --cubical-compatible --safe #-}
-- {-# OPTIONS --cubical-compatible --allow-unsolved-metas #-}
open import Level renaming (zero to Zero ; suc to Suc)
open import Ordinals
open import logic
open import Relation.Nullary

import HODBase
import OD
open import Relation.Binary
open import  Relation.Binary.PropositionalEquality hiding ( [_] )

module zorn {n : Level } (O : Ordinals {n} ) (HODAxiom : HODBase.ODAxiom O)  (ho< : OD.ODAxiom-ho< O HODAxiom )
       (AC : OD.AxiomOfChoice O HODAxiom ) 
        (_<_ : (x y : OD.HOD O HODAxiom) → Set n ) 
        (<-cong : {x y w z : OD.HOD O HODAxiom} 
            → HODBase._==_ O (HODBase.HOD.od x) (HODBase.HOD.od w) → HODBase._==_ O (HODBase.HOD.od  y) (HODBase.HOD.od z) → x < y  → w < z )
        (PO : IsStrictPartialOrder _≡_ _<_ ) where


-- open import  Relation.Binary.Structures
open import Data.Empty
open import Data.Nat hiding ( _≤_  ; _<_ )

import OrdUtil
open inOrdinal O

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

open import filter O HODAxiom ho< AC
open import ZProduct O HODAxiom ho<

open Filter


--
-- Zorn-lemma : { A : HOD }
--     → o∅ o< & A
--     → ( ( B : HOD) → (B⊆A : B ⊆ A) → IsTotalOrderSet B → SUP A B   ) -- SUP condition
--     → Maximal A
--


--
-- Partial Order on HOD ( possibly limited in A )
--

_<<_ : (x y : Ordinal ) → Set n
x << y = * x < * y

_≤_ : (x y : Ordinal ) → Set n    -- we can't use * x ≡ * y, it is Set (Level.suc n). Level (suc n) troubles Chain
x ≤ y = (x ≡ y ) ∨ ( * x < * y )

POO : IsStrictPartialOrder _≡_ _<<_
POO = record { isEquivalence = record { refl = refl ; sym = sym ; trans = trans }
   ; trans = IsStrictPartialOrder.trans PO
   ; irrefl = λ x=y x<y → IsStrictPartialOrder.irrefl PO (cong (*) x=y) x<y
   ; <-resp-≈ =  record { fst = λ {x} {y} {y1} y=y1 xy1 → subst (λ k → x << k ) y=y1 xy1 ; snd = λ {x} {x1} {y} x=x1 x1y → subst (λ k → k << x ) x=x1 x1y } }

≤-ftrans : {x y z : Ordinal } →  x ≤  y →  y ≤  z →  x ≤  z
≤-ftrans {x} {y} {z} (case1 refl ) (case1 refl ) = case1 refl
≤-ftrans {x} {y} {z} (case1 refl ) (case2 y<z) = case2 y<z
≤-ftrans {x} {_} {z} (case2 x<y ) (case1 refl ) = case2 x<y
≤-ftrans {x} {y} {z} (case2 x<y) (case2 y<z) = case2 ( IsStrictPartialOrder.trans PO x<y y<z )

ftrans≤-< : {x y z : Ordinal } →  x ≤  y →  y << z →  x <<  z
ftrans≤-< {x} {y} {z} (case1 eq) y<z = subst (λ k → k < * z) (sym (cong (*) eq))  y<z
ftrans≤-< {x} {y} {z} (case2 lt) y<z = IsStrictPartialOrder.trans PO lt y<z

ftrans<-≤ : {x y z : Ordinal } →  x <<  y →  y ≤ z →  x <<  z
ftrans<-≤ {x} {y} {z} x<y (case1 eq) = subst (λ k → * x < k ) ((cong (*) eq)) x<y
ftrans<-≤ {x} {y} {z} x<y (case2 lt) = IsStrictPartialOrder.trans PO x<y lt

<-irr : {a b : Ordinal} → (a ≡ b ) ∨ (* a < * b ) → * b < * a → ⊥
<-irr {a} {b} (case1 a=b) b<a = IsStrictPartialOrder.irrefl PO   (sym (cong (*) a=b) ) b<a
<-irr {a} {b} (case2 a<b) b<a = IsStrictPartialOrder.irrefl PO   refl
          (IsStrictPartialOrder.trans PO     b<a a<b)

<<-irr : {a b : Ordinal } → a ≤ b  → b << a → ⊥
<<-irr {a} {b} (case1 a=b) b<a = IsStrictPartialOrder.irrefl PO (cong (*) (sym a=b)) b<a
<<-irr {a} {b} (case2 a<b) b<a = IsStrictPartialOrder.irrefl PO refl (IsStrictPartialOrder.trans PO b<a a<b)

ptrans =  IsStrictPartialOrder.trans PO

-- open _==_
-- open _⊆_ -- we use different definition

-- We cannot prove this without Well foundedness of A
--
-- <-TransFinite : {A x : HOD} → {P : HOD → Set n} → x ∈ A
--     → ({y : HOD} → A ∋  y → y < x → P y ) → P x
-- <-TransFinite = ?

--
-- Closure of ≤-monotonic function f has total order
--

≤-monotonic-f : (A : HOD) → ( Ordinal → Ordinal ) → Set n
≤-monotonic-f A f = (x : Ordinal ) → odef A x → (  x ≤  (f x) ) ∧  odef A (f x )

<-monotonic-f : (A : HOD) → ( Ordinal → Ordinal ) → Set n
<-monotonic-f A f = (x : Ordinal ) → odef A x → ( * x < * (f x) ) ∧  odef A (f x )

data FClosure (A : HOD) (f : Ordinal → Ordinal ) (s : Ordinal) : Ordinal → Set n where
   init : {s1 : Ordinal } → odef A s → s ≡ s1  → FClosure A f s s1
   fsuc : (x : Ordinal) ( p :  FClosure A f s x ) → FClosure A f s (f x)

A∋fc : {A : HOD} (s : Ordinal) {y : Ordinal } (f : Ordinal → Ordinal) (mf : ≤-monotonic-f A f) → (fcy : FClosure A f s y ) → odef A y
A∋fc {A} s f mf (init as refl ) = as
A∋fc {A} s f mf (fsuc y fcy) = proj2 (mf y ( A∋fc {A} s  f mf fcy ) )

A∋fcs : {A : HOD} (s : Ordinal) {y : Ordinal } (f : Ordinal → Ordinal) (mf : ≤-monotonic-f A f) → (fcy : FClosure A f s y ) → odef A s
A∋fcs {A} s f mf (init as refl) = as
A∋fcs {A} s f mf (fsuc y fcy) = A∋fcs {A} s f mf fcy

s≤fc : {A : HOD} (s : Ordinal ) {y : Ordinal } (f : Ordinal → Ordinal) (mf : ≤-monotonic-f A f) → (fcy : FClosure A f s y ) →  s ≤  y
s≤fc {A} s {.s} f mf (init x refl ) = case1 refl
s≤fc {A} s {.(f x)} f mf (fsuc x fcy) with proj1 (mf x (A∋fc s f mf fcy ) )
... | case1 x=fx =  subst₂ (λ j k → j ≤ k ) refl x=fx (s≤fc s f mf fcy)
... | case2 x<fx with s≤fc {A} s f mf fcy
... | case1 s≡x = case2 ( subst₂ (λ j k → j < k ) (sym (cong (*) s≡x )) refl x<fx  )
... | case2 s<x = case2 ( IsStrictPartialOrder.trans PO s<x x<fx )

fcn : {A : HOD} (s : Ordinal) { x : Ordinal} {f : Ordinal → Ordinal} → (mf : ≤-monotonic-f A f) → FClosure A f s x → ℕ
fcn s mf (init as _) = zero
fcn {A} s {x} {f} mf (fsuc y p) with proj1 (mf y (A∋fc s f mf p))
... | case1 eq = fcn s mf p
... | case2 y<fy = suc (fcn s mf p )

¬z=sx : (z : ℕ ) →  ¬ ( zero ≡ suc z )
¬z=sx z ()

fcn-0 : {A : HOD} (s : Ordinal) { y : Ordinal} {f : Ordinal → Ordinal} → (mf : ≤-monotonic-f A f)
    →  (cy : FClosure A f s y ) → 0 ≡ fcn s mf cy → s ≡ y
fcn-0 {A} s {y} {f} mf (init x x₁) eq = x₁
fcn-0 {A} s {.(f x)} {f} mf (fsuc x cy) eq with proj1 (mf x (A∋fc s f mf cy))
... | case1 eq1 = trans (fcn-0 s mf cy eq) eq1
... | case2 y<fy = ⊥-elim (¬z=sx _ eq)

fcn-inject : {A : HOD} (s : Ordinal) { x y : Ordinal} {f : Ordinal → Ordinal} → (mf : ≤-monotonic-f A f)
     → (cx : FClosure A f s x ) (cy : FClosure A f s y ) → fcn s mf cx  ≡ fcn s mf cy → x ≡ y
fcn-inject {A} s {x} {y} {f} mf (init x₁ x₂) (init x₃ x₄) eq = trans (sym x₂) x₄
fcn-inject {A} s {x} {.(f x₃)} {f} mf (init x₁ x₂) (fsuc x₃ cy) eq with proj1 (mf x₃ (A∋fc s f mf cy ) )
... | case1 eqy = trans (sym x₂) (trans (fcn-0 s mf cy eq) eqy)  
... | case2 lty = ⊥-elim ( ¬z=sx _ eq )  
fcn-inject {A} s {.(f x)} {y} {f} mf (fsuc x cx) (init x₁ x₂) eq with proj1 (mf x (A∋fc s f mf cx ) )
... | case1 eqx = sym (trans (sym x₂) (trans (fcn-0 s mf cx (sym eq)) eqx)  )
... | case2 ltx = ⊥-elim ( ¬z=sx _ (sym eq) )  
fcn-inject {A} s {.(f x)} {.(f x₁)} {f} mf (fsuc x cx) (fsuc x₁ cy) eq with proj1 (mf x (A∋fc s f mf cx ) ) | proj1 (mf x₁ (A∋fc s f mf cy ) )
... | case1 eqx | case1 eqy = cong f lemma01 where
     lemma01 :  x ≡ x₁
     lemma01 = fcn-inject {A} s  mf cx cy eq
... | case1 eqx | case2 lty = trans (sym eqx) (sym (fc03 _ cx (sym eq)))  where
         fc03 : (y1 : Ordinal) → (cy1 : FClosure A f s y1 ) →  suc (fcn s mf cy) ≡ fcn s mf cy1 → f x₁  ≡ y1
         fc03 y1 (init x₁ x₂) x = ⊥-elim (¬z=sx _ (sym x)) 
         fc03 .(f y1) (fsuc y1 cy1) j=y1 with proj1 (mf y1 (A∋fc s f mf cy1 ) )
         ... | case1 eq = trans ( fc03  y1 cy1 j=y1 ) eq
         ... | case2 lt = cong f fc05 where 
              fc05 : x₁ ≡ y1
              fc05 = fcn-inject {A} s mf cy cy1 (cong pred j=y1)
... | case2 ltx | case1 eqy = trans (fc03 _ cy eq) eqy  where
         fc03 : (y1 : Ordinal) → (cy1 : FClosure A f s y1 ) →  suc (fcn s mf cx) ≡ fcn s mf cy1 → f x  ≡ y1
         fc03 y1 (init x₁ x₂) x = ⊥-elim (¬z=sx _ (sym x)) 
         fc03 .(f y1) (fsuc y1 cy1) j=y1 with proj1 (mf y1 (A∋fc s f mf cy1 ) )
         ... | case1 eq = trans ( fc03  y1 cy1 j=y1 ) eq
         ... | case2 lt = cong f fc05 where 
              fc05 : x ≡ y1
              fc05 = fcn-inject {A} s mf cx cy1 (cong pred j=y1)
... | case2 ltx | case2 lty = cong f lemma01 where
     lemma01 :  x ≡ x₁
     lemma01 = fcn-inject {A} s  mf cx cy (cong pred eq)

open import Data.Nat.Properties
fcn-< : {A : HOD} (s : Ordinal ) { x y : Ordinal} {f : Ordinal → Ordinal} → (mf : ≤-monotonic-f A f)
    → (cx : FClosure A f s x ) (cy : FClosure A f s y ) → fcn s mf cx Data.Nat.< fcn s mf cy  → * x < * y
fcn-< {A} s {x} {_} {f} mf cx cy x<y = fc01 (fcn s mf cy) cx cy refl x<y where
     fc06 : {y : Ordinal } { as : odef A s } (eq : s ≡ y  ) { j : ℕ } →  ¬ suc j ≡ fcn {A} s {y} {f} mf (init as eq )
     fc06 {x} {y} eq {j} not = fc08 not where
        fc08 :  {j : ℕ} → ¬ suc j ≡ 0
        fc08 ()
     fc01 : (i : ℕ ) → {y : Ordinal } → (cx : FClosure A f s x ) (cy : FClosure A f s y ) → (i ≡ fcn s mf cy ) → fcn s mf cx Data.Nat.< i → * x < * y
     fc01 zero cx cy eq ()
     fc01 (suc i) cx (init x₁ x₂) x lt = ⊥-elim (fc06 {_} {x₁} x₂ x)
     fc01 (suc i) {y} cx (fsuc y1 cy) i=y lt with proj1 (mf y1 (A∋fc s f mf cy ) )
     ... | case1 y=fy = subst (λ k → * x < k ) (cong (*) y=fy) ( fc01 (suc i) {y1} cx cy i=y (s≤s (sx≤py→x≤y lt))  )
     ... | case2 y<fy with <-cmp (fcn s mf cx ) i
     ... | tri> ¬a ¬b c = ⊥-elim ( nat-≤> (sx≤py→x≤y lt) c )
     ... | tri≈ ¬a b ¬c = subst (λ k → * k < * (f y1) ) (fcn-inject s mf cy cx (sym (trans b (cong pred i=y) ))) y<fy
     ... | tri< a ¬b ¬c = IsStrictPartialOrder.trans PO fc02 y<fy where
          fc03 :  suc i ≡ suc (fcn s mf cy) → i ≡ fcn s mf cy
          fc03 eq = cong pred eq
          fc02 :  * x < * y1
          fc02 =  fc01 i cx cy (fc03 i=y ) a
 

fcn-cmp : {A : HOD} (s : Ordinal) { x y : Ordinal } (f : Ordinal → Ordinal) (mf : ≤-monotonic-f A f)
    → (cx : FClosure A f s x) → (cy : FClosure A f s y ) → Tri (* x < * y) (x ≡ y) (* y < * x )
fcn-cmp {A} s {x} {y} f mf cx cy with <-cmp ( fcn s mf cx ) (fcn s mf cy )
... | tri< a ¬b ¬c = tri< fc11 (λ eq → <-irr (case1 (sym eq)) fc11) (λ lt → <-irr (case2 fc11) lt) where
      fc11 : * x < * y
      fc11 = fcn-< {A} s {x} {y} {f} mf cx cy a
... | tri≈ ¬a b ¬c = tri≈ (λ lt → <-irr (case1 (sym fc10)) lt) fc10 (λ lt → <-irr (case1 fc10) lt) where
      fc10 : x ≡ y
      fc10 = fcn-inject {A} s {x} {y} {f} mf cx cy b
... | tri> ¬a ¬b c = tri> (λ lt → <-irr (case2 fc12) lt) (λ eq → <-irr (case1 eq) fc12) fc12  where
      fc12 : * y < * x
      fc12 = fcn-< {A} s {y} {x} {f} mf cy cx c


-- open import Relation.Binary.Properties.Poset as Poset

IsTotalOrderSet : ( A : HOD ) → Set n
IsTotalOrderSet A = {a b : Ordinal } → odef A a → odef A b  → Tri (* a < * b) (a ≡ b) (* b < * a )

⊆-IsTotalOrderSet : { A B : HOD } →  B ⊆ A  → IsTotalOrderSet A → IsTotalOrderSet B
⊆-IsTotalOrderSet {A} {B} B⊆A T  ax ay = T (B⊆A ax) (B⊆A ay)

record HasPrev (A B : HOD) ( f : Ordinal → Ordinal ) (x : Ordinal )   : Set n where
   field
      ax : odef A x
      y : Ordinal
      ay : odef B y
      x=fy :  x ≡ f y

record IsSUP (A B : HOD) (x : Ordinal ) : Set n where
   field
      ax : odef A x
      x≤sup   : {y : Ordinal} → odef B y → (y ≡ x ) ∨ (y << x ) -- B is Total, use positive

record SUP ( A B : HOD )  : Set (Level.suc n) where
   field
      sup : HOD
      isSUP : IsSUP A B (& sup)
   ax = IsSUP.ax isSUP
   x≤sup = IsSUP.x≤sup isSUP

--
--   Our Proof strategy of the Zorn Lemma  
--
--    As ZChain.cfcs closure of supf z is smaller than next supf z1, and supf z o< supfz1, because of mf<
--    if have to be stopped since we have upper bound & A, so there is a Maximul element.
--
--         f (f ( ... (supf y))) f (f ( ... (supf z1)))
--        /          |         /             |
--       /           |        /              |
--    supf y   <       supf z1          <    supf z2
--           o<                      o<
--
--    if sup z1 ≡ sup z2, the chain is stopped at sup z1, then f (sup z1) ≡ sup z1
--

fc-stop : ( A : HOD )    ( f : Ordinal → Ordinal ) (mf : ≤-monotonic-f A f) { a b : Ordinal }
    → (aa : odef A a ) →(  {y : Ordinal} → FClosure A f a y → (y ≡ b ) ∨ (y << b )) → a ≡ b → f a ≡ a
fc-stop A f mf {a} {b} aa x≤sup a=b with x≤sup (fsuc a (init aa refl ))
... | case1 eq = trans eq (sym a=b)
... | case2 lt = ⊥-elim (<-irr (case1 (cong f (sym a=b))) (ftrans<-≤ lt fc00 ) ) where
     fc00 :   b ≤  (f b)
     fc00 = proj1 (mf _ (subst (λ k → odef A k) a=b aa ))

∈∧P→o< :  {A : HOD } {y : Ordinal} → {P : Set n} → odef A y ∧ P → y o< & A
∈∧P→o< {A } {y} p = subst (λ k → k o< & A) &iso ( c<→o< (subst (λ k → odef A k ) (sym &iso ) (proj1 p )))

-- Union of supf z and FClosure A f y

data UChain  { A : HOD } { f : Ordinal → Ordinal }  {supf : Ordinal → Ordinal} {y : Ordinal } (ay : odef A y )
       (x : Ordinal) : (z : Ordinal) → Set n where
    ch-init : {z : Ordinal } (fc : FClosure A f y z) → UChain ay x z
    ch-is-sup  : (u : Ordinal) {z : Ordinal }  (u<x : u o< x) (supu=u : supf u ≡ u) ( fc : FClosure A f (supf u) z ) → UChain ay x z

UnionCF : ( A : HOD ) ( f : Ordinal → Ordinal ) {y : Ordinal } (ay : odef A y ) ( supf : Ordinal → Ordinal ) ( x : Ordinal ) → HOD
UnionCF A f ay supf x
   = record { od = record { def = λ z → odef A z ∧ UChain {A} {f} {supf} ay x z } ;
       odmax = & A ; <odmax = λ {y} sy → ∈∧P→o< sy }

-- Union of chain lower than x

data IChain  {A : HOD}  { f : Ordinal → Ordinal } {y : Ordinal } (ay : odef A y )
               {x : Ordinal } (supfz : {z : Ordinal } → z o< x → Ordinal) : (z : Ordinal ) → Set n where
    ic-init : {z : Ordinal } (fc : FClosure A f y z) → IChain ay supfz z
    ic-isup : {z : Ordinal} (i : Ordinal) (i<x : i o< x) (s<x : supfz i<x o≤ i ) (fc : FClosure A f (supfz i<x) z) → IChain ay supfz z

UnionIC : ( A : HOD ) ( f : Ordinal → Ordinal ) { x : Ordinal } {y : Ordinal } (ay : odef A y ) (supfz : {z : Ordinal } → z o< x → Ordinal)  → HOD
UnionIC A f ay supfz
   = record { od = record { def = λ z → odef A z ∧ IChain {A} {f} ay supfz z } ;
       odmax = & A ; <odmax = λ {y} sy → ∈∧P→o< sy }

supf-inject0 : {x y : Ordinal } {supf : Ordinal → Ordinal } → (supf-mono : {x y : Ordinal } →  x o≤  y  → supf x o≤ supf y )
   → supf x o< supf y → x o<  y
supf-inject0 {x} {y} {supf} supf-mono sx<sy with trio< x y
... | tri< a ¬b ¬c = a
... | tri≈ ¬a eq ¬c = ⊥-elim ( o<¬≡ (cong supf eq) sx<sy )
... | tri> ¬a ¬b y<x with osuc-≡< (supf-mono (o<→≤ y<x) )
... | case1 eq = ⊥-elim ( o<¬≡ (sym eq) sx<sy )
... | case2 lt = ⊥-elim ( o<> sx<sy lt )

record IsMinSUP ( A B : HOD ) (sup : Ordinal) : Set n where
   field
      as : odef A sup
      x≤sup : {x : Ordinal } → odef B x → (x ≡ sup ) ∨ (x << sup )
      minsup : { sup1 : Ordinal } → odef A sup1
         →  ( {x : Ordinal  } → odef B x → (x ≡ sup1 ) ∨ (x << sup1 ))  → sup o≤ sup1

record MinSUP ( A B : HOD )  : Set n where
   field
      sup : Ordinal
      isMinSUP : IsMinSUP A B sup
   as = IsMinSUP.as isMinSUP
   x≤sup = IsMinSUP.x≤sup isMinSUP
   minsup = IsMinSUP.minsup isMinSUP

chain-mono : {A : HOD}  ( f : Ordinal → Ordinal ) → (mf : ≤-monotonic-f A f )  {y : Ordinal} (ay : odef A y) (supf : Ordinal → Ordinal )
   (supf-mono : {x y : Ordinal } →  x o≤  y  → supf x o≤ supf y ) {a b c : Ordinal} → a o≤ b
        → odef (UnionCF A f ay supf a) c → odef (UnionCF A f ay supf b) c
chain-mono f mf ay supf supf-mono {a} {b} {c} a≤b ⟪ ua , ch-init fc ⟫ = ⟪ ua , ch-init fc ⟫
chain-mono f mf ay supf supf-mono {a} {b} {c} a≤b ⟪ ua , ch-is-sup u u<x supu=u fc ⟫ = ⟪ ua , ch-is-sup u (ordtrans<-≤ u<x a≤b) supu=u fc ⟫

record ZChain ( A : HOD )    ( f : Ordinal → Ordinal )  (mf< : <-monotonic-f A f)
        {y : Ordinal} (ay : odef A y)  ( z : Ordinal ) : Set (Level.suc n) where
   field
      supf :  Ordinal → Ordinal

      asupf :  {x : Ordinal } → odef A (supf x)
      is-minsup : {x : Ordinal } → (x≤z : x o≤ z) → IsMinSUP A (UnionCF A f ay supf x) (supf x)
      supf-mono : {a b : Ordinal } → a o≤ b → supf a o≤ supf b
      cfcs  : {a b w : Ordinal } → a o< b → b o≤ z → supf a o< b → FClosure A f (supf a) w → odef (UnionCF A f ay supf b) w
      zo≤sz : {x : Ordinal } → x o≤ z → x o≤ supf x   -- because of mf<

   chain : HOD
   chain = UnionCF A f ay supf z
   chain⊆A : chain ⊆ A
   chain⊆A = λ lt → proj1 lt

   chain∋init : {x : Ordinal } → odef (UnionCF A f ay supf x) y
   chain∋init {x} = ⟪ ay , ch-init (init ay refl)  ⟫

   mf : ≤-monotonic-f A f
   mf x ax = ⟪ case2 mf00 , proj2 (mf< x ax ) ⟫ where
      mf00 : * x < * (f x)
      mf00 = proj1 ( mf< x ax )

   f-next : {a z : Ordinal} → odef (UnionCF A f ay supf z) a → odef (UnionCF A f ay supf z) (f a)
   f-next {a} ⟪ ua , ch-init fc ⟫ = ⟪ proj2 ( mf _ ua)  , ch-init (fsuc _ fc) ⟫
   f-next {a} ⟪ ua , ch-is-sup u su<x su=u fc ⟫ = ⟪ proj2 ( mf _ ua)  , ch-is-sup u su<x su=u (fsuc _ fc) ⟫

   supf-inject : {x y : Ordinal } → supf x o< supf y → x o<  y
   supf-inject {x} {y} sx<sy with trio< x y
   ... | tri< a ¬b ¬c = a
   ... | tri≈ ¬a eq ¬c = ⊥-elim ( o<¬≡ (cong supf eq) sx<sy )
   ... | tri> ¬a ¬b y<x with osuc-≡< (supf-mono (o<→≤ y<x) )
   ... | case1 eq = ⊥-elim ( o<¬≡ (sym eq) sx<sy )
   ... | case2 lt = ⊥-elim ( o<> sx<sy lt )

   -- another kind of maximality of the chain
   --    note that supf z is not an element of this chain
   --
   csupf : {b : Ordinal } → supf b o< supf z → supf b o< z → odef (UnionCF A f ay supf z) (supf b) 
   csupf {b} sb<sz sb<z = cfcs (supf-inject sb<sz) o≤-refl sb<z (init asupf refl)

   minsup : {x : Ordinal } → x o≤ z  → MinSUP A (UnionCF A f ay supf x)
   minsup {x} x≤z = record { sup = supf x ; isMinSUP = is-minsup x≤z }

   supf-is-minsup : {x : Ordinal } → (x≤z : x o≤ z) → supf x ≡ MinSUP.sup (minsup x≤z)
   supf-is-minsup _ = refl

   -- different from order because y o< supf
   fcy<sup  : {u w : Ordinal } → u o≤ z  → FClosure A f y w → (w ≡ supf u ) ∨ ( w << supf u )
   fcy<sup  {u} {w} u≤z fc with MinSUP.x≤sup (minsup u≤z) ⟪ subst (λ k → odef A k ) (sym &iso) (A∋fc {A} y f mf fc)
       , ch-init (subst (λ k → FClosure A f y k) (sym &iso) fc ) ⟫
   ... | case1 eq = case1 (subst (λ k → k ≡ supf u ) &iso  (trans eq (sym (supf-is-minsup u≤z ) ) ))
   ... | case2 lt = case2 (subst₂ (λ j k → j << k ) &iso (sym (supf-is-minsup u≤z )) lt )

   initial : {x : Ordinal } → x o≤ z → odef (UnionCF A f ay supf x) x →  y ≤ x
   initial {x} x≤z ⟪ aa , ch-init fc ⟫ = s≤fc y f mf fc
   initial {x} x≤z ⟪ aa , ch-is-sup u u<x is-sup fc ⟫ = ≤-ftrans (fcy<sup (ordtrans u<x x≤z) (init ay refl)) (s≤fc _ f mf fc)

   sup=u : {b : Ordinal} → (ab : odef A b) → b o≤ z
       → IsSUP A (UnionCF A f ay supf b) b  → supf b ≡ b
   sup=u {b} ab b≤z is-sup = z50 where
           z48 : supf b o≤ b
           z48 = IsMinSUP.minsup (is-minsup b≤z) ab (λ ux → IsSUP.x≤sup is-sup ux )
           z50 : supf b ≡ b
           z50 with trio< (supf b) b
           ... | tri< sb<b ¬b ¬c = ⊥-elim ( o≤> z47 sb<b ) where
                 z47 : b o≤ supf b
                 z47 = zo≤sz b≤z
           ... | tri≈ ¬a b ¬c = b
           ... | tri> ¬a ¬b b<sb = ⊥-elim ( o≤> z48 b<sb )

   --
   -- supf is minsup, so its UniofCF are equal, these are equal
   -- 
   supfeq : {a b : Ordinal } → a o≤ z →  b o≤ z → UnionCF A f ay supf a =h= UnionCF A f ay supf b → supf a ≡ supf b
   supfeq {a} {b} a≤z b≤z ua=ub with trio< (supf a) (supf b)
   ... | tri< sa<sb ¬b ¬c = ⊥-elim ( o≤> (
             IsMinSUP.minsup (is-minsup b≤z) asupf (λ {z} uzb → IsMinSUP.x≤sup (is-minsup a≤z) (eq←  ua=ub uzb) )) sa<sb )
   ... | tri≈ ¬a b ¬c = b
   ... | tri> ¬a ¬b sb<sa = ⊥-elim ( o≤> (
             IsMinSUP.minsup (is-minsup a≤z) asupf (λ {z} uza → IsMinSUP.x≤sup (is-minsup b≤z) (eq→ ua=ub uza) )) sb<sa )

   --
   -- supf a over b and supf a is not included in UnionCF a nor UnionCF b, so UnionCF b is equal to the UnionCF a
   --
   union-max : {a b : Ordinal } → b o≤ supf a → b o≤ z → supf a o< supf b → UnionCF A f ay supf a =h= UnionCF A f ay supf b
   union-max {a} {b} b≤sa b≤z sa<sb = record { eq→ = z47 ; eq← = z48 } where
          z47 : {w : Ordinal } → odef (UnionCF A f ay supf a ) w → odef ( UnionCF A f ay supf b ) w
          z47 {w} ⟪ aw , ch-init fc ⟫ = ⟪ aw , ch-init fc ⟫
          z47 {w} ⟪ aw , ch-is-sup u u<a su=u fc ⟫ = ⟪ aw , ch-is-sup u u<b su=u fc ⟫ where
              u<b : u o< b
              u<b = ordtrans u<a (supf-inject sa<sb )
          z48 : {w : Ordinal } → odef (UnionCF A f ay supf b ) w → odef ( UnionCF A f ay supf a ) w
          z48 {w} ⟪ aw , ch-init fc ⟫ = ⟪ aw , ch-init fc ⟫
          z48 {w} ⟪ aw , ch-is-sup u u<b su=u fc ⟫ = ⟪ aw , ch-is-sup u u<a su=u fc ⟫ where
              u<a : u o< a
              u<a = supf-inject ( osucprev (begin
                 osuc (supf u)  ≡⟨ cong osuc su=u ⟩
                 osuc u  ≤⟨ osucc u<b ⟩
                 b  ≤⟨ b≤sa ⟩
                 supf a ∎ )) where open o≤-Reasoning 

   x≤supfx→¬sa<sa : {a b : Ordinal } → b o≤ z → b o≤ supf a → ¬ (supf a o< supf b )
   x≤supfx→¬sa<sa {a} {b} b≤z b≤sa sa<sb = ⊥-elim ( o<¬≡ z27 sa<sb ) where -- x o≤ supf a ∧ supf a o< supf b → ⊥, because it defines the same UnionCF
         z27 : supf a ≡ supf b
         z27 = supfeq (ordtrans (supf-inject sa<sb) b≤z) b≤z ( union-max  b≤sa b≤z sa<sb)

   order : {a b w : Ordinal } → b o≤ z → supf a o< supf b → FClosure A f (supf a) w → w ≤ supf b
   order {a} {b} {w} b≤z sa<sb fc = IsMinSUP.x≤sup (is-minsup b≤z) (cfcs (supf-inject sa<sb) b≤z sa<b fc) where
         sa<b : supf a o< b
         sa<b with x<y∨y≤x (supf a) b
         ... | case1 lt = lt
         ... | case2 b≤sa = ⊥-elim (x≤supfx→¬sa<sa b≤z b≤sa sa<sb)

   supf-idem : {b : Ordinal } → b o≤ z → supf b o≤ z  → supf (supf b) ≡ supf b
   supf-idem {b} b≤z sfb≤x = z52 where
       z54 :  {w : Ordinal} → odef (UnionCF A f ay supf (supf b)) w → (w ≡ supf b) ∨ (w << supf b)
       z54 {w} ⟪ aw , ch-init fc ⟫ = fcy<sup b≤z fc
       z54 {w} ⟪ aw , ch-is-sup u u<x su=u fc ⟫ = order b≤z (subst (λ k → k o< supf b) (sym su=u) u<x)  fc where
               u<b : u o< b
               u<b = supf-inject (subst (λ k → k o< supf b ) (sym (su=u)) u<x )
       z52 : supf (supf b) ≡ supf b
       z52 = sup=u asupf sfb≤x  record { ax = asupf  ; x≤sup = z54  }

   supf-mono< : {a b : Ordinal } → b o≤ z → supf a o< supf b → supf a << supf b
   supf-mono< {a} {b} b≤z sa<sb  with order {a} {b} b≤z sa<sb (init asupf refl)
   ... | case2 lt = lt
   ... | case1 eq = ⊥-elim ( o<¬≡ eq sa<sb )

   f-total : IsTotalOrderSet chain
   f-total {a} {b} ⟪ uaa , ch-is-sup ua sua<x sua=ua fca ⟫ ⟪ uab , ch-is-sup ub sub<x sub=ub fcb ⟫ = fc-total where
         fc-total : Tri (* a < * b) (a ≡ b) (* b < * a )
         fc-total with trio< ua ub
         fc-total | tri< a₁ ¬b ¬c with ≤-ftrans  (order (o<→≤ sub<x) (subst₂ (λ j k → j o< k) (sym sua=ua) (sym sub=ub) a₁) fca ) (s≤fc (supf ub) f mf fcb )
         ... | case1 eq1 = tri≈ (λ lt → ⊥-elim (<-irr (case1 (sym eq1)) lt)) eq1  (λ lt → ⊥-elim (<-irr (case1 eq1) lt)) 
         ... | case2 a<b =  tri< a<b (λ eq → <-irr (case1 (sym eq)) a<b ) (λ lt → <-irr (case2 a<b ) lt)
         fc-total | tri≈ _ eq _ = fcn-cmp _ f mf fca (subst (λ k → FClosure A f (supf k) b) (sym eq) fcb)
         fc-total | tri> ¬a ¬b c with ≤-ftrans  (order (o<→≤ sua<x) (subst₂ (λ j k → j o< k) (sym sub=ub) (sym sua=ua) c) fcb ) (s≤fc (supf ua) f mf fca )
         ... | case1 eq1 = tri≈ (λ lt → ⊥-elim (<-irr (case1 eq1) lt)) (sym eq1)  (λ lt → ⊥-elim (<-irr (case1 (sym eq1)) lt)) 
         ... | case2 b<a =  tri> (λ lt → <-irr (case2 b<a ) lt)  (λ eq → <-irr (case1 eq) b<a )  b<a
   f-total {a} {b} ⟪ uaa , ch-init fca ⟫ ⟪ uab , ch-is-sup ub sub<x sub=ub fcb ⟫ = ft00 where
      ft01 : a ≤ b → Tri ( * a <  * b) ( a ≡  b) ( * b <  * a )
      ft01 (case1 eq) = tri≈ (λ lt → ⊥-elim (<-irr (case1 (sym eq)) lt)) eq  (λ lt → ⊥-elim (<-irr (case1 eq) lt))  
      ft01 (case2 a<b) = tri< a<b (λ eq → <-irr (case1 (sym eq)) a<b ) (λ lt → <-irr (case2 a<b ) lt)  
      ft00 :   Tri ( * a <  * b) ( a ≡  b) ( * b <  * a )
      ft00 = ft01 (≤-ftrans (fcy<sup (o<→≤ sub<x) fca) (s≤fc {A} _ f mf fcb))
   f-total {a} {b} ⟪ uaa , ch-is-sup ua sua<x sua=ua fca ⟫ ⟪ uab , ch-init fcb ⟫ = ft00 where
      ft01 : b ≤ a → Tri ( * a <  * b) ( a ≡  b) ( * b <  * a )
      ft01 (case1 eq) = tri≈ (λ lt → ⊥-elim (<-irr (case1 eq) lt)) (sym eq) (λ lt → ⊥-elim (<-irr (case1 (sym eq)) lt))  
      ft01 (case2 b<a) = tri> (λ lt → <-irr (case2 b<a ) lt) (λ eq → <-irr (case1 eq) b<a ) b<a 
      ft00 :   Tri ( * a <  * b) ( a ≡  b) ( * b <  * a )
      ft00 = ft01 (≤-ftrans (fcy<sup (o<→≤ sua<x) fcb) (s≤fc {A} _ f mf fca))
   f-total {a} {b} ⟪ uaa , ch-init fca ⟫ ⟪ uab , ch-init fcb ⟫ = fcn-cmp y f mf fca fcb 

record ZChain1 ( A : HOD )    ( f : Ordinal → Ordinal )  (mf< : <-monotonic-f A f)
        {y : Ordinal} (ay : odef A y)  (zc : ZChain A f mf< ay (& A)) ( z : Ordinal ) : Set (Level.suc n) where
   supf = ZChain.supf zc
   field
      is-max :  {a b : Ordinal } → (ca : odef (UnionCF A f ay supf z) a ) → b o< z  → (ab : odef A b)
          → HasPrev A (UnionCF A f ay supf z) f b ∨  IsSUP A (UnionCF A f ay supf b) b
          → * a < * b  → odef ((UnionCF A f ay supf z)) b

record Maximal ( A : HOD )  : Set (Level.suc n) where
   field
      maximal : HOD
      as : A ∋ maximal
      ¬maximal<x : {x : HOD} → A ∋ x  → ¬ maximal < x       -- A is Partial, use negative

--
-- supf in TransFinite indution may differ each other, but it is the same because of the minimul sup
--
supf-unique :  ( A : HOD )    ( f : Ordinal → Ordinal )  (mf< : <-monotonic-f A f)
        {y xa xb : Ordinal} → (ay : odef A y) →  (xa o≤ xb ) → (za : ZChain A f mf< ay xa ) (zb : ZChain A f mf< ay xb )
      → {z : Ordinal } → z o≤ xa → ZChain.supf za z ≡ ZChain.supf zb z
supf-unique A f mf< {y} {xa} {xb} ay xa≤xb za zb {z} z≤xa = 
  TransFinite0 {λ z → z o≤ xa → ZChain.supf za z ≡ ZChain.supf zb z } ind z z≤xa  where
       supfa = ZChain.supf za
       supfb = ZChain.supf zb
       ind : (x : Ordinal) → ((w : Ordinal) → w o< x → w o≤ xa → supfa w ≡ supfb w) → x o≤ xa → supfa x ≡ supfb x
       ind x prev x≤xa = sxa=sxb where
           ma = ZChain.minsup za x≤xa
           mb = ZChain.minsup zb (OrdTrans x≤xa xa≤xb )
           spa = MinSUP.sup ma
           spb = MinSUP.sup mb
           sax=spa : supfa x ≡ spa
           sax=spa = ZChain.supf-is-minsup za x≤xa
           sbx=spb : supfb x ≡ spb
           sbx=spb = ZChain.supf-is-minsup zb (OrdTrans x≤xa xa≤xb )
           sxa=sxb : supfa x ≡ supfb x
           sxa=sxb with trio< (supfa x) (supfb x)
           ... | tri≈ ¬a b ¬c = b
           ... | tri< a ¬b ¬c = ⊥-elim ( o≤> (
               begin
                 supfb x  ≡⟨ sbx=spb ⟩
                 spb  ≤⟨ MinSUP.minsup mb (MinSUP.as ma) (λ {z} uzb → MinSUP.x≤sup ma (z53 uzb)) ⟩
                 spa ≡⟨ sym sax=spa ⟩
                 supfa x ∎ ) a ) where
                    open o≤-Reasoning 
                    z53 : {z : Ordinal } →  odef (UnionCF A f ay (ZChain.supf zb) x) z →  odef (UnionCF A f ay (ZChain.supf za) x) z
                    z53 ⟪ as , ch-init fc ⟫ = ⟪ as , ch-init fc ⟫
                    z53 {z} ⟪ as , ch-is-sup u u<x su=u fc ⟫ = ⟪ as , ch-is-sup u u<x (trans ua=ub su=u) z55 ⟫ where
                        ua=ub : supfa u ≡ supfb u
                        ua=ub = prev u u<x (ordtrans u<x x≤xa )
                        z55 : FClosure A f (ZChain.supf za u) z
                        z55 = subst (λ k → FClosure A f k z ) (sym ua=ub) fc
           ... | tri> ¬a ¬b c = ⊥-elim ( o≤> (
               begin
                 supfa x  ≡⟨ sax=spa ⟩
                 spa  ≤⟨ MinSUP.minsup ma (MinSUP.as mb) (λ uza → MinSUP.x≤sup mb (z53 uza)) ⟩
                 spb  ≡⟨ sym sbx=spb ⟩
                 supfb x ∎ ) c ) where
                    open o≤-Reasoning 
                    z53 : {z : Ordinal } →  odef (UnionCF A f ay (ZChain.supf za) x) z →  odef (UnionCF A f ay (ZChain.supf zb) x) z
                    z53 ⟪ as , ch-init fc ⟫ = ⟪ as , ch-init fc ⟫
                    z53 {z} ⟪ as , ch-is-sup u u<x su=u fc ⟫ =  ⟪ as , ch-is-sup u u<x (trans ub=ua su=u) z55  ⟫ where
                        ub=ua : supfb u ≡ supfa u
                        ub=ua = sym ( prev u u<x (ordtrans u<x x≤xa ))
                        z55 : FClosure A f (ZChain.supf zb u) z
                        z55 = subst (λ k → FClosure A f k z ) (sym ub=ua) fc


Zorn-lemma : { A : HOD }
    → o∅ o< & A
    → ( ( B : HOD) → (B⊆A : B ⊆ A) → IsTotalOrderSet B → SUP A B   ) -- SUP condition
    → Maximal A
Zorn-lemma {A}  0<A supP = zorn00 where
     z07 :   {y : Ordinal} {A : HOD } → {P : Set n} → odef A y ∧ P → y o< & A
     z07 {y} {A} p = subst (λ k → k o< & A) &iso ( c<→o< (subst (λ k → odef A k ) (sym &iso ) (proj1 p )))
     s : HOD
     s = minimal A (λ eq → ¬x<0 ( subst (λ k → o∅ o< k ) (=od∅→≡o∅ eq) 0<A ))
     as : A ∋ s
     as =  x∋minimal A (λ eq → ¬x<0 ( subst (λ k → o∅ o< k ) (=od∅→≡o∅ eq) 0<A ))  
     s<A : & s o< & A
     s<A = c<→o< as
     HasMaximal : HOD
     HasMaximal = record { od = record { def = λ x → odef A x ∧ ( (m : Ordinal) →  odef A m → ¬ (* x < * m)) }  ; odmax = & A ; <odmax = z07 }
     no-maximum : HasMaximal =h= od∅ → (x : Ordinal) → odef A x ∧ ((m : Ordinal) →  odef A m →  odef A x ∧ (¬ (* x < * m) )) →  ⊥
     no-maximum nomx x P = ¬x<0 (eq→ nomx {x} ⟪ proj1 P , (λ m ma p → proj2 ( proj2 P m ma ) p ) ⟫ )
     Gtx : { x : HOD} → A ∋ x → HOD
     Gtx {x} ax = record { od = record { def = λ y → odef A y ∧ (x < (* y)) } ; odmax = & A ; <odmax = z07 }
     z08  : ¬ Maximal A →  HasMaximal =h= od∅
     z08 nmx  = record { eq→  = λ {x} lt → ⊥-elim ( nmx record {maximal = * x ; as = subst (λ k → odef A k) (sym &iso) (proj1 lt)
         ; ¬maximal<x = λ {y} ay x<y → proj2 lt (& y) ay (<-cong ==-refl (==-sym *iso) x<y) } ) ; eq← =  λ {y} lt → ⊥-elim ( ¬x<0 lt )}
     x-is-maximal : ¬ Maximal A → {x : Ordinal} → (ax : odef A x) → & (Gtx (subst (λ k → odef A k ) (sym &iso) ax)) ≡ o∅ → (m : Ordinal) → odef A m → odef A x ∧ (¬ (* x < * m))
     x-is-maximal nmx {x} ax nogt m am  = ⟪ subst (λ k → odef A k) &iso (subst (λ k → odef A k ) (sym &iso) ax) ,  ¬x<m  ⟫ where
        ¬x<m :  ¬ (* x < * m)
        ¬x<m x<m = ∅< {Gtx (subst (λ k → odef A k ) (sym &iso) ax)} {* m} ⟪ subst (λ k → odef A k) (sym &iso) am , subst (λ k → * x < k ) (cong (*) (sym &iso)) x<m ⟫  (≡o∅→=od∅ nogt)

     --
     -- we have minsup using LEM, this is similar to the proof of the axiom of choice
     --
     minsupP :  ( B : HOD) → (B⊆A : B ⊆ A) → IsTotalOrderSet B → MinSUP A B
     minsupP B B⊆A total = m02 where
         xsup : (sup : Ordinal ) → Set n
         xsup sup = {w : Ordinal } → odef B w → (w ≡ sup ) ∨ (w << sup )
         ∀-imply-or :  {A : Ordinal  → Set n } {B : Set n }
                        → ((x : Ordinal ) → A x ∨ B) →  ((x : Ordinal ) → A x) ∨ B
         ∀-imply-or  {A} {B} ∀AB with p∨¬p ((x : Ordinal ) → A x) -- LEM
         ∀-imply-or  {A} {B} ∀AB | case1 t = case1 t
         ∀-imply-or  {A} {B} ∀AB | case2 x  = case2 (lemma (λ not → x not )) where
               lemma : ¬ ((x : Ordinal ) → A x) →  B
               lemma not with p∨¬p B
               lemma not | case1 b = b
               lemma not | case2 ¬b = ⊥-elim  (not (λ x → dont-orb (∀AB x) ¬b ))
         m00 : (x : Ordinal ) → ( ( z : Ordinal) → z o< x →  ¬ (odef A z ∧ xsup z) ) ∨ MinSUP A B
         m00 x = TransFinite0 ind x where
            ind : (x : Ordinal) → ((z : Ordinal) → z o< x → ( ( w : Ordinal) → w o< z →  ¬ (odef A w ∧ xsup w ))  ∨ MinSUP A B)
                  → ( ( w : Ordinal) → w o< x →  ¬ (odef A w ∧ xsup w) )  ∨ MinSUP A B
            ind x prev  =  ∀-imply-or m01 where
                m01 : (z : Ordinal) → (z o< x → ¬ (odef A z ∧ xsup z)) ∨ MinSUP A B
                m01 z with trio< z x
                ... | tri≈ ¬a b ¬c = case1 ( λ lt →  ⊥-elim ( ¬a lt )  )
                ... | tri> ¬a ¬b c = case1 ( λ lt →  ⊥-elim ( ¬a lt )  )
                ... | tri< a ¬b ¬c with prev z a
                ... | case2 mins = case2 mins
                ... | case1 not with p∨¬p (odef A z ∧ xsup z)
                ... | case1 mins = case2 record { sup = z ; isMinSUP = record { as = proj1 mins ; x≤sup = proj2 mins ; minsup = m04 } } where
                  m04 : {sup1 : Ordinal} → odef A sup1 → ({w : Ordinal} → odef B w → (w ≡ sup1) ∨ (w << sup1)) → z o≤ sup1
                  m04 {s} as lt with trio< z s
                  ... | tri< a ¬b ¬c = o<→≤ a
                  ... | tri≈ ¬a b ¬c = o≤-refl0 b
                  ... | tri> ¬a ¬b s<z = ⊥-elim ( not s s<z ⟪ as , lt ⟫  )
                ... | case2 notz = case1 (λ _ → notz )
         m03 : ¬ ((z : Ordinal) → z o< & A → ¬ odef A z ∧ xsup z)
         m03 not = ⊥-elim ( not s1 (odef< (SUP.ax S)) ⟪ SUP.ax S , m05 ⟫ ) where
             S : SUP A B
             S = supP B  B⊆A total
             s1 = & (SUP.sup S)
             m05 : {w : Ordinal } → odef B w → (w ≡ s1 ) ∨ (w << s1 )
             m05 {w} bw with SUP.x≤sup S bw
             ... | case1 eq = case1 ( subst₂ (λ j k → j ≡ k ) &iso refl (trans &iso eq))
             ... | case2 lt = case2 lt
         m02 : MinSUP A B
         m02 = dont-or (m00 (& A)) m03

     -- Uncountable ascending chain by axiom of choice
     cf : ¬ Maximal A → Ordinal → Ordinal
     cf  nmx x with ∋-p A (* x)
     ... | no0 _ = o∅
     ... | yes0 ax with is-o∅ (& ( Gtx ax ))
     ... | yes0 nogt = -- no0 larger element, so it is maximal
         ⊥-elim (no-maximum (z08 nmx) x ⟪ subst (λ k → odef A k) &iso ax , x-is-maximal nmx (subst (λ k → odef A k ) &iso ax) nogt ⟫ )
     ... | no0 not =  & (minimal (Gtx ax) (λ eq → not (=od∅→≡o∅ eq)))
     is-cf : (nmx : ¬ Maximal A ) → {x : Ordinal} → odef A x → odef A (cf nmx x) ∧ ( * x < * (cf nmx x) )
     is-cf nmx {x} ax with ∋-p A (* x)
     ... | no0 not = ⊥-elim ( not (subst (λ k → odef A k ) (sym &iso) ax ))
     ... | yes0 ax with is-o∅ (& ( Gtx ax ))
     ... | yes0 nogt = ⊥-elim (no-maximum (z08 nmx) x ⟪ subst (λ k → odef A k) &iso ax , x-is-maximal nmx (subst (λ k → odef A k ) &iso ax) nogt ⟫ )
     ... | no0 not = x∋minimal (Gtx ax) (λ eq → not (=od∅→≡o∅ eq))

     ---
     --- infintie ascention sequence of f
     ---
     cf-is-<-monotonic : (nmx : ¬ Maximal A ) → (x : Ordinal) →  odef A x → ( * x < * (cf nmx x) ) ∧  odef A (cf nmx x )
     cf-is-<-monotonic nmx x ax = ⟪ proj2 (is-cf nmx ax ) , proj1 (is-cf nmx ax ) ⟫
     cf-is-≤-monotonic : (nmx : ¬ Maximal A ) →  ≤-monotonic-f A ( cf nmx )
     cf-is-≤-monotonic nmx x ax = ⟪ case2 (proj1 ( cf-is-<-monotonic nmx x ax  ))  , proj2 ( cf-is-<-monotonic nmx x ax  ) ⟫

     --
     -- maximality of chain
     --
     --     supf is fixed for z ≡ & A , we can prove order and is-max
     --     we have supf-unique now, it is provable in the first Tranfinte induction

     SZ1 : ( f : Ordinal → Ordinal )  (mf : ≤-monotonic-f A f) (mf< : <-monotonic-f A f)
        {init : Ordinal} (ay : odef A init) (zc : ZChain A f mf< ay (& A)) (x : Ordinal) → x o≤ & A → ZChain1 A f mf< ay zc x
     SZ1 f mf mf< {y} ay zc x x≤A = zc1 x x≤A  where
        chain-mono1 :  {a b c : Ordinal} → a o≤ b
            → odef (UnionCF A f ay (ZChain.supf zc) a) c → odef (UnionCF A f ay (ZChain.supf zc) b) c
        chain-mono1  {a} {b} {c} a≤b = chain-mono f mf ay (ZChain.supf zc) (ZChain.supf-mono zc) a≤b
        is-max-hp : (x : Ordinal) {a : Ordinal} {b : Ordinal} → odef (UnionCF A f ay (ZChain.supf zc) x) a → (ab : odef A b)
            → HasPrev A (UnionCF A f ay (ZChain.supf zc) x) f b
            → * a < * b → odef (UnionCF A f ay (ZChain.supf zc) x) b
        is-max-hp x {a} {b} ua ab has-prev a<b with HasPrev.ay has-prev
        ... | ⟪ ab0 , ch-init fc ⟫ = ⟪ ab , ch-init ( subst (λ k → FClosure A f y k) (sym (HasPrev.x=fy has-prev)) (fsuc _ fc )) ⟫
        ... | ⟪ ab0 , ch-is-sup u u<x su=u fc ⟫ = ⟪ ab , subst (λ k → UChain ay x k )
                      (sym (HasPrev.x=fy has-prev)) ( ch-is-sup u u<x su=u (fsuc _ fc))  ⟫

        supf = ZChain.supf zc

        zc1 :  (x : Ordinal ) → x o≤ & A →   ZChain1 A f mf< ay zc x
        zc1 x x≤A with Oprev-p x
        ... | yes0 op = record { is-max = is-max } where
               px = Oprev.oprev op
               is-max :  {a : Ordinal} {b : Ordinal} → odef (UnionCF A f ay supf x) a →
                  b o< x → (ab : odef A b) →
                  HasPrev A (UnionCF A f ay supf x) f b  ∨ IsSUP A (UnionCF A f ay supf b) b →
                  * a < * b → odef (UnionCF A f ay supf x) b
               is-max {a} {b} ua b<x ab P a<b with or-exclude P
               is-max {a} {b} ua b<x ab P a<b | case1 has-prev = is-max-hp x {a} {b} ua ab has-prev a<b
               is-max {a} {b} ua b<x ab P a<b | case2 is-sup with osuc-≡< (ZChain.supf-mono zc (o<→≤ b<x))
               ... | case2 sb<sx = m10 where
                  b<A : b o< & A
                  b<A = odef< ab
                  m05 : ZChain.supf zc b ≡ b
                  m05 =  ZChain.sup=u zc ab (o<→≤ (odef< ab) )  record { ax = ab ; x≤sup = λ {z} uz → IsSUP.x≤sup (proj2 is-sup) uz  }
                  m10 : odef (UnionCF A f ay supf x) b
                  m10 = ZChain.cfcs zc b<x x≤A (subst (λ k → k o< x) (sym m05) b<x) (init (ZChain.asupf zc) m05)
               ... | case1 sb=sx = ⊥-elim (<-irr (case1 m10) (proj1 (mf< (supf b) (ZChain.asupf zc)))) where
                  m17 : MinSUP A (UnionCF A f ay supf x) -- supf z o< supf ( supf x )
                  m17 = ZChain.minsup zc x≤A
                  m18 : supf x ≡ MinSUP.sup m17
                  m18 = ZChain.supf-is-minsup zc x≤A
                  m10 : f (supf b) ≡ supf b
                  m10 = fc-stop A f mf (ZChain.asupf zc) m11 sb=sx where
                      m11 : {z : Ordinal} → FClosure A f (supf b) z → (z ≡ ZChain.supf zc x) ∨ (z << ZChain.supf zc x)
                      m11 {z} fc = subst (λ k → (z ≡ k) ∨ (z << k)) (sym m18) ( MinSUP.x≤sup m17 m13 ) where
                          m04 : ¬ HasPrev A (UnionCF A f ay supf b) f b
                          m04 nhp = proj1 is-sup ( record { ax = HasPrev.ax nhp ; y = HasPrev.y nhp ; ay =
                                chain-mono1 (o<→≤ b<x) (HasPrev.ay  nhp) ; x=fy = HasPrev.x=fy nhp } )
                          m05 : ZChain.supf zc b ≡ b
                          m05 =  ZChain.sup=u zc ab (o<→≤ (odef< ab) )  record { ax = ab ; x≤sup = λ {z} uz → IsSUP.x≤sup (proj2 is-sup) uz  }
                          m14 : ZChain.supf zc b o< x
                          m14 = subst (λ k → k o< x ) (sym m05)  b<x
                          m13 :  odef (UnionCF A f ay supf x) z
                          m13 = ZChain.cfcs zc b<x x≤A m14 fc

        ... | no0 lim = record { is-max = is-max }  where
               is-max :  {a : Ordinal} {b : Ordinal} → odef (UnionCF A f ay supf x) a →
                  b o< x → (ab : odef A b) →
                  HasPrev A (UnionCF A f ay supf x) f b  ∨ IsSUP A (UnionCF A f ay supf b) b →
                  * a < * b → odef (UnionCF A f ay supf x) b
               is-max {a} {b} ua b<x ab P a<b with or-exclude P
               is-max {a} {b} ua b<x ab P a<b | case1 has-prev = is-max-hp x {a} {b} ua ab has-prev a<b
               is-max {a} {b} ua b<x ab P a<b | case2 is-sup with IsSUP.x≤sup (proj2 is-sup) (ZChain.chain∋init zc  )
               ... | case1 b=y = ⟪ subst (λ k → odef A k ) b=y ay ,  ch-init (subst (λ k → FClosure A f y k ) b=y (init ay refl ))  ⟫
               ... | case2 y<b with osuc-≡< (ZChain.supf-mono zc (o<→≤ b<x))
               ... | case2 sb<sx = m10 where
                  m09 : b o< & A
                  m09 = subst (λ k → k o< & A) &iso ( c<→o< (subst (λ k → odef A k ) (sym &iso ) ab))
                  m05 : ZChain.supf zc b ≡ b
                  m05 = ZChain.sup=u zc ab (o<→≤  m09) record { ax = ab ; x≤sup = λ lt → IsSUP.x≤sup (proj2 is-sup) lt }
                  m10 : odef (UnionCF A f ay supf x) b
                  m10 = ZChain.cfcs zc b<x x≤A (subst (λ k → k o< x) (sym m05) b<x) (init (ZChain.asupf zc) m05)
               ... | case1 sb=sx = ⊥-elim (<-irr (case1 m10) (proj1 (mf< (supf b) (ZChain.asupf zc)))) where
                  m17 : MinSUP A (UnionCF A f ay supf x) -- supf z o< supf ( supf x )
                  m17 = ZChain.minsup zc x≤A
                  m18 : supf x ≡ MinSUP.sup m17
                  m18 = ZChain.supf-is-minsup zc x≤A
                  m10 : f (supf b) ≡ supf b
                  m10 = fc-stop A f mf (ZChain.asupf zc) m11 sb=sx where
                      m11 : {z : Ordinal} → FClosure A f (supf b) z → (z ≡ ZChain.supf zc x) ∨ (z << ZChain.supf zc x)
                      m11 {z} fc = subst (λ k → (z ≡ k) ∨ (z << k)) (sym m18) ( MinSUP.x≤sup m17 m13 ) where
                          m05 =  ZChain.sup=u zc ab (o<→≤ (odef< ab) ) record { ax = ab ; x≤sup = λ {z} uz → IsSUP.x≤sup (proj2 is-sup) uz }
                          m14 : ZChain.supf zc b o< x
                          m14 = subst (λ k → k o< x ) (sym m05)  b<x
                          m13 :  odef (UnionCF A f ay supf x) z
                          m13 = ZChain.cfcs zc b<x x≤A m14 fc

     uchain : ( f : Ordinal → Ordinal ) → (mf : ≤-monotonic-f A f ) {y : Ordinal} (ay : odef A y) → HOD
     uchain f mf {y} ay = record { od = record { def = λ x → FClosure A f y x } ; odmax = & A ; <odmax =
             λ {z} cz → subst (λ k → k o< & A) &iso ( c<→o< (subst (λ k → odef A k ) (sym &iso ) (A∋fc y f mf cz ))) }

     utotal : ( f : Ordinal → Ordinal ) → (mf : ≤-monotonic-f A f ) {y : Ordinal} (ay : odef A y)
        → IsTotalOrderSet (uchain f mf ay)
     utotal f mf {y} ay {a} {b} ca cb = fcn-cmp y f mf ca cb

     ysup : ( f : Ordinal → Ordinal ) → (mf : ≤-monotonic-f A f ) {y : Ordinal} (ay : odef A y)
       →  MinSUP A (uchain f mf ay)
     ysup f mf {y} ay = minsupP (uchain f mf ay) (λ lt → A∋fc y f mf lt)  (utotal f mf ay)

     --
     -- create all ZChains under o< x
     --

     ind : ( f : Ordinal → Ordinal ) → (mf< : <-monotonic-f A f ) {y : Ordinal} (ay : odef A y) → (x : Ordinal)
         → ((z : Ordinal) → z o< x → ZChain A f mf< ay z) → ZChain A f mf< ay x
     ind f mf< {y} ay x prev with Oprev-p x
     ... | yes0 op = zc41 sup1 where
          --
          -- we have previous ordinal to use induction
          --
          px = Oprev.oprev op
          zc : ZChain A f mf< ay (Oprev.oprev op)
          zc = prev px (subst (λ k → px o< k) (Oprev.oprev=x op) <-osuc )
          px<x : px o< x
          px<x = subst (λ k → px o< k) (Oprev.oprev=x op) <-osuc
          opx=x : osuc px ≡ x
          opx=x = Oprev.oprev=x op

          zc-b<x : (b : Ordinal ) → b o< x → b o< osuc px
          zc-b<x b lt = subst (λ k → b o< k ) (sym (Oprev.oprev=x op)) lt

          supf0 = ZChain.supf zc
          pchain  : HOD
          pchain   = UnionCF A f ay supf0 px

          supf-mono = ZChain.supf-mono zc

          zc04 : {b : Ordinal} → b o≤ x → (b o≤ px ) ∨ (b ≡ x )
          zc04 {b} b≤x with trio< b px
          ... | tri< a ¬b ¬c = case1 (o<→≤ a)
          ... | tri≈ ¬a b ¬c = case1 (o≤-refl0 b)
          ... | tri> ¬a ¬b px<b with osuc-≡< b≤x
          ... | case1 eq = case2 eq
          ... | case2 b<x = ⊥-elim ( ¬p<x<op ⟪ px<b , subst (λ k → b o< k ) (sym (Oprev.oprev=x op)) b<x  ⟫ )

          mf : ≤-monotonic-f A f
          mf x ax = ⟪ case2 mf00 , proj2 (mf< x ax ) ⟫ where
             mf00 : * x < * (f x)
             mf00 = proj1 ( mf< x ax )

          --
          -- find the next value of supf
          --

          pchainpx : HOD
          pchainpx = record { od = record { def = λ z →  (odef A z  ∧ UChain  ay px z )
                ∨ (FClosure A f (supf0 px) z ∧ (supf0 px o< x)) } ; odmax = & A ; <odmax = zc00 } where
               zc00 : {z : Ordinal } → (odef A z ∧ UChain ay px z ) ∨ (FClosure A f (supf0 px) z ∧ (supf0 px o< x) )→ z o< & A
               zc00 {z} (case1 lt) = z07 lt
               zc00 {z} (case2 fc) = odef< ( A∋fc (supf0 px) f mf (proj1 fc) )

          zc02 : { a b : Ordinal } → odef A a ∧ UChain ay px a → FClosure A f (supf0 px) b ∧ ( supf0 px o< x) → a ≤ b
          zc02 {a} {b} ca fb = zc05 (proj1 fb) where
             zc05 : {b : Ordinal } → FClosure A f (supf0 px) b → a ≤ b
             zc05 (fsuc b1 fb ) with proj1 ( mf b1 (A∋fc (supf0 px) f mf fb ))
             ... | case1 eq = subst (λ k → a ≤ k ) eq (zc05 fb)
             ... | case2 lt = ≤-ftrans (zc05 fb) (case2 lt)
             zc05 (init b1 refl) = MinSUP.x≤sup (ZChain.minsup zc o≤-refl) ca

          ptotal : IsTotalOrderSet pchainpx
          ptotal (case1 a) (case1 b) =  ZChain.f-total zc a b
          ptotal {a0} {b0} (case1 a) (case2 b) with zc02 a b
          ... | case1 eq = tri≈ (<-irr (case1 (sym eq))) eq (<-irr (case1 eq)) 
          ... | case2 lt = tri< lt (λ eq → <-irr (case1 (sym eq)) lt) (<-irr (case2 lt)) 
          ptotal {b0} {a0} (case2 b) (case1 a) with zc02 a b
          ... | case1 eq = tri≈ (<-irr (case1 eq)) (sym eq) (<-irr (case1 (sym eq))) 
          ... | case2 lt = tri> (<-irr (case2 lt)) (λ eq → <-irr (case1 eq) lt) lt  
          ptotal (case2 a) (case2 b) = fcn-cmp (supf0 px) f mf (proj1 a) (proj1 b)

          pcha : pchainpx ⊆ A
          pcha (case1 lt) = proj1 lt
          pcha (case2 fc) = A∋fc _ f mf (proj1 fc)

          sup1 : MinSUP A pchainpx
          sup1 = minsupP pchainpx pcha ptotal

          --
          --     supf0 px o≤ sp1
          --

          zc41 : MinSUP A pchainpx → ZChain A f mf< ay x
          zc41 sup1 =  record { supf = supf1 ; asupf = asupf1 ; zo≤sz =  zo≤sz ;  is-minsup =  is-minsup ;  cfcs = cfcs ; supf-mono = supf1-mono }  where

                 sp1 = MinSUP.sup sup1

                 supf1 : Ordinal → Ordinal
                 supf1 z with trio< z px
                 ... | tri< a ¬b ¬c = supf0 z
                 ... | tri≈ ¬a b ¬c = supf0 z
                 ... | tri> ¬a ¬b c = sp1

                 sf1=sf0 : {z : Ordinal } → z o≤ px → supf1 z ≡ supf0 z
                 sf1=sf0 {z} z≤px with trio< z px
                 ... | tri< a ¬b ¬c = refl
                 ... | tri≈ ¬a b ¬c = refl
                 ... | tri> ¬a ¬b c = ⊥-elim ( o≤> z≤px c )

                 sf1=sp1 : {z : Ordinal } → px o< z → supf1 z ≡ sp1
                 sf1=sp1 {z} px<z with trio< z px
                 ... | tri< a ¬b ¬c = ⊥-elim ( o<> px<z a )
                 ... | tri≈ ¬a b ¬c = ⊥-elim ( o<¬≡ (sym b) px<z )
                 ... | tri> ¬a ¬b c = refl

                 sf=eq :  { z : Ordinal } → z o< x → supf0 z ≡ supf1 z
                 sf=eq {z} z<x = sym (sf1=sf0 (subst (λ k → z o< k ) (sym (Oprev.oprev=x op)) z<x ))

                 asupf1 : {z : Ordinal } → odef A (supf1 z)
                 asupf1 {z} with trio< z px
                 ... | tri< a ¬b ¬c = ZChain.asupf zc
                 ... | tri≈ ¬a b ¬c = ZChain.asupf zc
                 ... | tri> ¬a ¬b c = MinSUP.as sup1

                 supf1-mono : {a b : Ordinal } → a o≤ b → supf1 a o≤ supf1 b
                 supf1-mono {a} {b} a≤b with trio< b px
                 ... | tri< a ¬b ¬c =  subst₂ (λ j k → j o≤ k ) (sym (sf1=sf0 (o<→≤ (ordtrans≤-< a≤b a)))) refl ( supf-mono a≤b )
                 ... | tri≈ ¬a b ¬c =  subst₂ (λ j k → j o≤ k ) (sym (sf1=sf0 (subst (λ k → a o≤ k) b a≤b))) refl ( supf-mono a≤b )
                 supf1-mono {a} {b} a≤b | tri> ¬a ¬b c with trio< a px
                 ... | tri< a<px ¬b ¬c = zc19 where
                       zc21 : MinSUP A (UnionCF A f ay supf0 a)
                       zc21 = ZChain.minsup zc (o<→≤ a<px)
                       zc24 : {x₁ : Ordinal} → odef (UnionCF A f ay supf0 a) x₁ → (x₁ ≡ sp1) ∨ (x₁ << sp1)
                       zc24 {x₁} ux = MinSUP.x≤sup sup1 (case1 (chain-mono f mf ay supf0 (ZChain.supf-mono zc) (o<→≤ a<px) ux ) )
                       zc19 : supf0 a o≤ sp1
                       zc19 = subst (λ k → k o≤ sp1) (sym (ZChain.supf-is-minsup zc  (o<→≤ a<px))) ( MinSUP.minsup zc21 (MinSUP.as sup1) zc24 )
                 ... | tri≈ ¬a b ¬c = zc18 where
                       zc21 : MinSUP A (UnionCF A f ay supf0 a)
                       zc21 = ZChain.minsup zc (o≤-refl0 b)
                       zc20 : MinSUP.sup zc21 ≡ supf0 a
                       zc20 = sym (ZChain.supf-is-minsup zc (o≤-refl0 b))
                       zc24 : {x₁ : Ordinal} → odef (UnionCF A f ay supf0 a) x₁ → (x₁ ≡ sp1) ∨ (x₁ << sp1)
                       zc24 {x₁} ux = MinSUP.x≤sup sup1 (case1 (chain-mono f mf ay supf0 (ZChain.supf-mono zc) (o≤-refl0 b) ux ) )
                       zc18 : supf0 a o≤ sp1
                       zc18 = subst (λ k → k o≤ sp1) zc20( MinSUP.minsup zc21 (MinSUP.as sup1) zc24 )
                 ... | tri> ¬a ¬b c = o≤-refl

                 fcup : {u z : Ordinal } → FClosure A f (supf1 u) z → u o≤ px → FClosure A f (supf0 u) z
                 fcup {u} {z} fc u≤px = subst (λ k → FClosure A f k z ) (sf1=sf0 u≤px) fc
                 fcpu : {u z : Ordinal } → FClosure A f (supf0 u) z → u o≤ px →  FClosure A f (supf1 u) z
                 fcpu {u} {z} fc u≤px = subst (λ k → FClosure A f k z ) (sym (sf1=sf0 u≤px)) fc

                 -- this is a kind of maximality, so we cannot prove this without <-monotonicity
                 --
                 cfcs : {a b w : Ordinal }
                     → a o< b → b o≤ x → supf1 a o< b  → FClosure A f (supf1 a) w → odef (UnionCF A f ay supf1 b) w
                 cfcs {a} {b} {w} a<b b≤x sa<b fc with x<y∨y≤x  (supf0 a) px
                 ... | case2 px≤sa = z50 where
                      a<x : a o< x
                      a<x = ordtrans<-≤ a<b b≤x
                      a≤px : a o≤ px
                      a≤px = subst (λ k → a o< k) (sym (Oprev.oprev=x op)) (ordtrans<-≤ a<b b≤x)
                      --  supf0 a ≡ px we cannot use previous cfcs, it is in the chain because
                      --       supf0 a ≡ supf0 (supf0 a) ≡ supf0 px o< x
                      z50 : odef (UnionCF A f ay supf1 b) w
                      z50 with osuc-≡< px≤sa
                      ... | case1 px=sa = ⟪ A∋fc {A} _ f mf fc , cp  ⟫ where
                          sa≤px : supf0 a o≤ px
                          sa≤px = subst₂ (λ j k → j o< k) px=sa (sym (Oprev.oprev=x op)) px<x
                          spx=sa : supf0 px ≡ supf0 a
                          spx=sa = begin
                                supf0 px ≡⟨ cong supf0 px=sa  ⟩
                                supf0 (supf0 a) ≡⟨ ZChain.supf-idem zc a≤px sa≤px  ⟩
                                supf0 a ∎  where open ≡-Reasoning
                          z51 : supf0 px o< b
                          z51 = subst (λ k → k o< b ) (sym ( begin supf0 px ≡⟨ spx=sa ⟩
                                supf0 a ≡⟨ sym (sf1=sf0 a≤px) ⟩
                                supf1 a ∎ )) sa<b where open ≡-Reasoning
                          z52 : supf1 a ≡ supf1 (supf0 px)
                          z52 = begin supf1 a ≡⟨ sf1=sf0 a≤px ⟩
                                supf0 a ≡⟨ sym (ZChain.supf-idem zc a≤px sa≤px ) ⟩
                                supf0 (supf0 a) ≡⟨ sym (sf1=sf0 sa≤px)  ⟩
                                supf1 (supf0 a) ≡⟨ cong supf1 (sym spx=sa) ⟩
                                supf1 (supf0 px) ∎ where open ≡-Reasoning
                          z53 : supf1 (supf0 px) ≡ supf0 px
                          z53 = begin
                                supf1 (supf0 px)  ≡⟨ cong supf1 spx=sa ⟩
                                supf1 (supf0 a)  ≡⟨ sf1=sf0 sa≤px ⟩
                                supf0 (supf0 a)  ≡⟨ sym ( cong supf0 px=sa ) ⟩
                                supf0 px  ∎  where open ≡-Reasoning
                          cp : UChain ay b w
                          cp = ch-is-sup (supf0 px) z51 z53 (subst (λ k → FClosure A f k w) z52 fc)
                      ... | case2 px<sa = ⊥-elim ( ¬p<x<op ⟪ px<sa , subst₂ (λ j k → j o< k ) (sf1=sf0 a≤px) (sym (Oprev.oprev=x op)) z53 ⟫  ) where
                          z53  : supf1 a o< x
                          z53  = ordtrans<-≤ sa<b b≤x
                 ... | case1 sa<px with trio< a px
                 ... | tri< a<px ¬b ¬c = z50 where
                      z50 : odef (UnionCF A f ay supf1 b) w
                      z50 with osuc-≡< b≤x
                      ... | case2 lt with ZChain.cfcs zc a<b (subst (λ k → b o< k) (sym (Oprev.oprev=x op)) lt) sa<b fc
                      ... | ⟪ az , ch-init fc ⟫ = ⟪ az , ch-init fc ⟫
                      ... | ⟪ az , ch-is-sup u u<b su=u fc ⟫ = ⟪ az , ch-is-sup u u<b (trans (sym (sf=eq u<x)) su=u) (fcpu fc u≤px )  ⟫ where
                           u≤px : u o≤ px
                           u≤px = subst (λ k → u o< k) (sym (Oprev.oprev=x op))  (ordtrans<-≤ u<b b≤x )
                           u<x : u o< x
                           u<x = ordtrans<-≤ u<b b≤x
                      z50 | case1 eq with ZChain.cfcs zc a<px o≤-refl sa<px fc
                      ... | ⟪ az , ch-init fc ⟫ = ⟪ az , ch-init fc ⟫
                      ... | ⟪ az , ch-is-sup u u<px su=u fc ⟫ = ⟪ az , ch-is-sup u u<b (trans (sym (sf=eq u<x)) su=u) (fcpu fc (o<→≤ u<px)) ⟫  where -- u o< px → u o< b ?
                           u<b : u o< b
                           u<b = subst (λ k → u o< k ) (trans (Oprev.oprev=x op) (sym eq) ) (ordtrans u<px <-osuc )
                           u<x : u o< x
                           u<x = subst (λ k → u o< k ) (Oprev.oprev=x op) ( ordtrans u<px <-osuc )
                 ... | tri≈ ¬a a=px ¬c = csupf1 where
                      -- a ≡ px , b ≡ x, sp o≤ x
                      px<b : px o< b
                      px<b = subst₂ (λ j k → j o< k) a=px refl a<b
                      b=x : b ≡ x
                      b=x with trio< b x
                      ... | tri< a ¬b ¬c = ⊥-elim ( ¬p<x<op ⟪ px<b , subst (λ k → b o< k ) (sym (Oprev.oprev=x op)) a ⟫ ) --  px o< b o< x
                      ... | tri≈ ¬a b ¬c = b
                      ... | tri> ¬a ¬b c = ⊥-elim ( o≤> b≤x c ) --   x o< b
                      z51 : FClosure A f (supf1 px) w
                      z51 = subst (λ k → FClosure A f k w) (sym (trans (cong supf1 (sym a=px)) (sf1=sf0 (o≤-refl0 a=px) ))) fc
                      z53 : odef A w
                      z53 = A∋fc {A} _ f mf fc
                      csupf1 : odef (UnionCF A f ay supf1 b) w
                      csupf1 with x<y∨y≤x  px (supf0 px)
                      ... | case2 spx≤px = ⟪ z53 , ch-is-sup (supf0 px) z54 z52 fc1 ⟫  where
                          z54 : supf0 px o< b
                          z54 = subst (λ k → supf0 px o< k ) (trans (Oprev.oprev=x op) (sym b=x) ) spx≤px
                          z52 : supf1 (supf0 px) ≡ supf0 px
                          z52 = trans (sf1=sf0 spx≤px ) ( ZChain.supf-idem zc o≤-refl spx≤px  )
                          fc1 : FClosure A f (supf1 (supf0 px)) w
                          fc1 = subst (λ k → FClosure A f k w ) (trans (cong supf0 a=px) (sym z52) ) fc
                      ... | case1 px<spx = ⊥-elim (¬p<x<op ⟪ px<spx , z54  ⟫ ) where  -- supf1 px o≤ spuf1 x → supf1 px ≡ x o< x
                          z54 : supf0 px o≤ px
                          z54 = subst₂ (λ j k → supf0 j o< k ) a=px (trans b=x (sym (Oprev.oprev=x op))) sa<b

                 ... | tri> ¬a ¬b c = ⊥-elim ( ¬p<x<op ⟪ c , subst (λ k → a o< k ) (sym (Oprev.oprev=x op)) ( ordtrans<-≤ a<b b≤x) ⟫ ) --  px o< a o< b o≤ x

                 zc11 : {z : Ordinal} → odef (UnionCF A f ay supf1 x) z → odef pchainpx z
                 zc11 {z} ⟪ az , ch-init fc ⟫ = case1 ⟪ az , ch-init fc ⟫
                 zc11 {z} ⟪ az , ch-is-sup u u<x su=u fc ⟫ = zc21 fc where
                    zc21 : {z1 : Ordinal } → FClosure A f (supf1 u) z1 → odef pchainpx z1
                    zc21 {z1} (fsuc z2 fc ) with zc21 fc
                    ... | case1 ⟪ ua1 , ch-init fc₁ ⟫ = case1 ⟪ proj2 ( mf _ ua1)  , ch-init (fsuc _ fc₁)  ⟫
                    ... | case1 ⟪ ua1 ,  ch-is-sup u u<x su=u fc₁   ⟫ = case1 ⟪ proj2 ( mf _ ua1)  ,  ch-is-sup u u<x su=u (fsuc _ fc₁) ⟫
                    ... | case2 fc = case2 ⟪ fsuc _ (proj1 fc) , proj2 fc ⟫
                    zc21 (init {z1} asp eq ) with trio< (supf0 u) (supf0 px)
                    ... | tri< a ¬b ¬c = case1 ⟪ asp1 , ch-is-sup u u<px (trans (sym (sf1=sf0 (o<→≤ u<px))) su=u )(
                              init asp0 (sym (trans (sym eq) (sf1=sf0 (o<→≤ u<px)))) ) ⟫ where
                        u<px :  u o< px
                        u<px =  ZChain.supf-inject zc a
                        asp0 : odef A (supf0 u)
                        asp0 = ZChain.asupf zc
                        asp1 : odef A z1
                        asp1 = subst (λ k → odef A k ) eq asp
                    ... | tri≈ ¬a b ¬c = case2 ⟪ (init (subst (λ k → odef A k) b (ZChain.asupf zc) )
                        (sym (trans (trans (sym eq) (sf1=sf0 (zc-b<x _ u<x)  ))  b ))) , spx<x ⟫ where
                          spx<x : supf0 px o< x
                          spx<x = osucprev ( begin
                             osuc (supf0 px) ≡⟨ cong osuc (sym b) ⟩
                             osuc (supf0 u) ≡⟨ cong osuc  (sym (sf1=sf0 (zc-b<x _ u<x) ))  ⟩
                             osuc (supf1 u) ≡⟨ cong osuc  su=u ⟩
                             osuc u ≤⟨ osucc u<x ⟩
                             x ∎ ) where open o≤-Reasoning 
                    ... | tri> ¬a ¬b c = ⊥-elim ( ¬p<x<op ⟪ ZChain.supf-inject zc c , subst (λ k → u o< k ) (sym (Oprev.oprev=x op)) u<x  ⟫ )

                 is-minsup :  {z : Ordinal} → z o≤ x → IsMinSUP A (UnionCF A f ay supf1 z) (supf1 z)
                 is-minsup {z} z≤x with osuc-≡< z≤x
                 ... | case1 z=x = record { as = zc22 ; x≤sup = z23 ; minsup = z24  }  where
                    px<z : px o< z
                    px<z = subst (λ k → px o< k) (sym z=x) px<x
                    zc22 : odef A (supf1 z)
                    zc22 = subst (λ k → odef A k ) (sym (sf1=sp1 px<z ))  ( MinSUP.as sup1 )
                    z23 : {w : Ordinal } → odef ( UnionCF A f ay supf1 z ) w → w ≤ supf1 z
                    z23 {w} uz  = subst (λ k → w ≤ k ) (sym (sf1=sp1 px<z)) ( MinSUP.x≤sup sup1 (
                         zc11 (subst (λ k → odef (UnionCF A f ay supf1 k) w) z=x uz )))
                    z24 : {s : Ordinal } → odef A s → ( {w : Ordinal } → odef ( UnionCF A f ay supf1 z ) w → w ≤ s )
                        → supf1 z o≤ s
                    z24 {s} as sup = subst (λ k → k o≤ s ) (sym (sf1=sp1 px<z)) ( MinSUP.minsup sup1 as z25 ) where
                        z25 : {w : Ordinal } → odef pchainpx w → w ≤ s
                        z25 {w} (case2 fc) = sup ⟪ A∋fc _ f mf (proj1 fc) , ch-is-sup (supf0 px) z28 z27 fc1 ⟫ where
                            -- z=x , supf0 px o< x
                            z28 : supf0 px o< z --    supf0 px ≡ supf1 px o≤ supf1 x ≡ sp1 o≤ x ≡ z
                            z28 = subst (λ k → supf0 px o< k) (sym z=x) (proj2 fc)
                            z29 : supf0 px o≤ px
                            z29 = zc-b<x _ (proj2 fc)
                            z27 : supf1 (supf0 px) ≡ supf0 px
                            z27 = trans (sf1=sf0 z29) ( ZChain.supf-idem zc o≤-refl z29 )
                            fc1 : FClosure A f (supf1 (supf0 px)) w
                            fc1 = subst (λ k → FClosure A f k w) (sym z27) (proj1 fc)
                        z25 {w} (case1 ⟪ ua , ch-init fc ⟫) = sup ⟪ ua , ch-init fc ⟫
                        z25 {w} (case1 ⟪ ua , ch-is-sup u u<x su=u fc  ⟫) = sup ⟪ ua , ch-is-sup u u<z
                             (trans (sf1=sf0 u≤px)  su=u)  (fcpu fc u≤px)  ⟫ where
                            u≤px : u o< osuc px
                            u≤px = ordtrans u<x <-osuc
                            u<z : u o< z
                            u<z = ordtrans u<x (subst (λ k → px o< k ) (sym z=x) px<x )
                 ... | case2 z<x = record { as = zc22 ; x≤sup = z23 ; minsup = z24  } where
                    z≤px = zc-b<x _ z<x
                    m =  ZChain.is-minsup zc z≤px
                    zc22 : odef A (supf1 z)
                    zc22 = subst (λ k → odef A k ) (sym (sf1=sf0 z≤px))  ( IsMinSUP.as m )
                    z23 : {w : Ordinal } → odef ( UnionCF A f ay supf1 z ) w → w ≤ supf1 z
                    z23 {w} ⟪ ua , ch-init fc ⟫ = subst (λ k → w ≤ k ) (sym (sf1=sf0 z≤px)) ( ZChain.fcy<sup zc z≤px fc )
                    z23 {w} ⟪ ua ,  ch-is-sup u u<x su=u fc  ⟫ = subst (λ k → w ≤ k ) (sym (sf1=sf0 z≤px))
                       (IsMinSUP.x≤sup m ⟪ ua ,  ch-is-sup u u<x (trans (sym (sf1=sf0 u≤px )) su=u)  (fcup fc u≤px )  ⟫ ) where
                                u≤px : u o≤ px
                                u≤px = ordtrans u<x z≤px
                    z24 : {s : Ordinal } → odef A s → ( {w : Ordinal } → odef ( UnionCF A f ay supf1 z ) w → w ≤ s )
                        → supf1 z o≤ s
                    z24 {s} as sup = subst (λ k → k o≤ s ) (sym (sf1=sf0 z≤px)) ( IsMinSUP.minsup m as z25 ) where
                        z25 : {w : Ordinal } → odef ( UnionCF A f ay supf0 z ) w → w ≤ s
                        z25 {w} ⟪ ua , ch-init fc ⟫ = sup ⟪ ua , ch-init fc ⟫
                        z25 {w} ⟪ ua , ch-is-sup u u<x su=u fc  ⟫ = sup ⟪ ua , ch-is-sup u u<x
                             (trans (sf1=sf0 u≤px)  su=u)  (fcpu fc u≤px)  ⟫ where
                                u≤px : u o≤ px
                                u≤px = ordtrans u<x z≤px

                 zo≤sz : {z : Ordinal} →  z o≤ x → z o≤ supf1 z
                 zo≤sz {z} z≤x with osuc-≡< z≤x
                 ... | case2 z<x = subst (λ k → z o≤ k) (sym (sf1=sf0 (zc-b<x _ z<x ))) (ZChain.zo≤sz zc (zc-b<x _ z<x ))
                 ... | case1 eq with osuc-≡< (supf1-mono (o<→≤ (px<x))) --   px o≤ supf1 px o≤ supf1 x ≡ sp1 → x o≤ sp1
                 ... | case2 lt = begin
                     z ≡⟨ eq ⟩
                     x ≡⟨ sym (Oprev.oprev=x op) ⟩
                     osuc px ≤⟨ osucc (ZChain.zo≤sz zc o≤-refl)  ⟩
                     osuc (supf0 px) ≡⟨ sym (cong osuc (sf1=sf0 o≤-refl )) ⟩
                     osuc (supf1 px) ≤⟨ osucc lt ⟩
                     supf1 x ≡⟨ cong supf1 (sym eq) ⟩
                     supf1 z ∎ where open o≤-Reasoning 
                 ... | case1 spx=sx with osuc-≡< ( ZChain.zo≤sz zc o≤-refl )
                 ... | case2 lt = begin
                     z ≡⟨ eq ⟩
                     x ≡⟨ sym (Oprev.oprev=x op) ⟩
                     osuc px ≤⟨ osucc lt ⟩
                     supf0 px ≡⟨ sym (sf1=sf0 o≤-refl)  ⟩
                     supf1 px ≤⟨ supf1-mono (o<→≤ px<x)  ⟩
                     supf1 x ≡⟨ cong supf1 (sym eq) ⟩
                     supf1 z ∎ where open o≤-Reasoning 
                 ... | case1 px=spx =  ⊥-elim ( <<-irr zc40 (proj1 ( mf< (supf0 px) (ZChain.asupf zc))) ) where
                     zc37 : supf0 px ≡ px
                     zc37 = sym px=spx
                     zc39 : supf0 px ≡ sp1
                     zc39 = begin
                       supf0 px ≡⟨ sym (sf1=sf0 o≤-refl)  ⟩
                       supf1 px ≡⟨ spx=sx ⟩
                       supf1 x ≡⟨ sf1=sp1 px<x ⟩
                       sp1 ∎ where open ≡-Reasoning
                     zc40 :  f (supf0 px) ≤ supf0 px
                     zc40 = subst (λ k → f (supf0 px) ≤ k ) (sym zc39)
                           ( MinSUP.x≤sup sup1 (case2 ⟪ fsuc _ (init (ZChain.asupf zc) refl) , subst (λ k → k o< x) (sym zc37) px<x ⟫  ))

     ... | no0 lim with trio< x o∅
     ... | tri< a ¬b ¬c = ⊥-elim ( ¬x<0 a )
     ... | tri≈ ¬a x=0 ¬c = record { supf = λ _ → MinSUP.sup (ysup f mf ay) ; asupf = MinSUP.as (ysup f mf ay) ; supf-mono = λ _ → o≤-refl 
          ; zo≤sz = zo≤sz ; is-minsup = is-minsup ; cfcs = λ a<b b≤0 → ⊥-elim ( ¬x<0 (subst (λ k → _ o< k ) x=0 (ordtrans<-≤ a<b b≤0)))    } where
          -- initial case

          mf : ≤-monotonic-f A f
          mf x ax = ⟪ case2 mf00 , proj2 (mf< x ax ) ⟫ where
             mf00 : * x < * (f x)
             mf00 = proj1 ( mf< x ax )
          ym = MinSUP.sup (ysup f mf ay)

          zo≤sz : {z : Ordinal} → z o≤ x → z o≤ MinSUP.sup (ysup f mf ay)
          zo≤sz {z} z≤x with osuc-≡< z≤x
          ... | case1 eq = subst (λ k → k o≤ _) (trans  (sym x=0) (sym eq) ) o∅≤z 
          ... | case2 lt = ⊥-elim ( ¬x<0  (subst (λ k → z o< k ) x=0 lt ) )

          is-minsup : {z : Ordinal} → z o≤ x →
            IsMinSUP A (UnionCF A f ay (λ _ → MinSUP.sup (ysup f mf ay)) z) (MinSUP.sup (ysup f mf ay))
          is-minsup {z} z≤x with osuc-≡< z≤x
          ... | case1 eq = record { as = MinSUP.as  (ysup f mf ay) ; x≤sup = λ {w} uw → is00 (is03 w uw) ; minsup = λ {s} as sup → is01 as sup } where
              is00 : {w : Ordinal } → odef (UnionCF A f ay (λ _ → MinSUP.sup (ysup f mf ay)) x ) w → w ≤ MinSUP.sup (ysup f mf ay)
              is00 {w} ⟪ aw , ch-init fc ⟫ = MinSUP.x≤sup (ysup f mf ay) fc
              is00 {w} ⟪ aw , ch-is-sup u u<z su=u fc ⟫ = ⊥-elim (¬x<0 (subst (λ k → u o< k ) x=0 u<z ))
              is01 : { s : Ordinal } → odef A s →  ( {w : Ordinal  } → odef (UnionCF A f ay (λ _ → MinSUP.sup (ysup f mf ay)) z )  w → w ≤ s )
                  → ym o≤ s
              is01 {s} as sup = MinSUP.minsup (ysup f mf ay) as is02 where
                  is02 : {w : Ordinal } →  odef (uchain f mf ay) w → (w ≡ s) ∨ (w << s)
                  is02 fc = sup ⟪ A∋fc _ f mf fc , ch-init fc ⟫
              is03 : (w : Ordinal) → odef (UnionCF A f ay (λ _ → MinSUP.sup (ysup f mf ay)) z ) w
                                   → odef (UnionCF A f ay (λ _ → MinSUP.sup (ysup f mf ay)) x ) w
              is03 w uw = subst (λ k → odef (UnionCF A f ay (λ _ → MinSUP.sup (ysup f mf ay)) k ) w ) eq  uw
          ... | case2 lt = ⊥-elim ( ¬x<0  (subst (λ k → z o< k ) x=0 lt ) )

     ... | tri> ¬a ¬b 0<x = zc400 usup ssup where

      mf : ≤-monotonic-f A f
      mf x ax = ⟪ case2 mf00 , proj2 (mf< x ax ) ⟫ where
         mf00 : * x < * (f x)
         mf00 = proj1 ( mf< x ax )

      pzc : {z : Ordinal} → z o< x → ZChain A f mf< ay z
      pzc {z} z<x = prev z z<x

      ysp =  MinSUP.sup (ysup f mf ay)

      supfz : {z : Ordinal } → z o< x → Ordinal
      supfz {z} z<x = ZChain.supf (pzc  (ob<x lim z<x)) z

      pchainU : HOD
      pchainU = UnionIC A f ay supfz

      zeq : {xa xb z : Ordinal }
         → (xa<x : xa o< x) → (xb<x : xb o< x) → xa o≤ xb → z o≤ xa
         → ZChain.supf (pzc  xa<x) z ≡  ZChain.supf (pzc  xb<x) z
      zeq {xa} {xb} {z} xa<x xb<x xa≤xb z≤xa =  supf-unique A f mf< ay xa≤xb
          (pzc xa<x)  (pzc xb<x)  z≤xa

      -- iceq : {ix iy : Ordinal } → ix ≡ iy → {i<x : ix o< x } {i<y : iy o< x } → supfz i<x ≡ supfz i<y
      -- iceq refl = cong supfz  o<-irr

      IChain-i : {z : Ordinal } → IChain ay supfz z → Ordinal
      IChain-i (ic-init fc) = o∅
      IChain-i (ic-isup ia ia<x sa<x fca) = ia

      pic<x : {z : Ordinal } → (ic : IChain ay supfz z ) → osuc (IChain-i ic) o< x
      pic<x {z} (ic-init fc) = ob<x lim 0<x   -- 0<x ∧ lim x → osuc o∅ o< x
      pic<x {z} (ic-isup ia ia<x sa<x fca) = ob<x lim ia<x

      pchainU⊆chain : {z : Ordinal } → (pz : odef pchainU z) → odef (ZChain.chain (pzc (pic<x (proj2 pz)))) z
      pchainU⊆chain {z} ⟪ aw , ic-init fc ⟫ = ⟪ aw , ch-init fc ⟫
      pchainU⊆chain {z} ⟪ aw , (ic-isup ia ia<x sa<x fca) ⟫ = ZChain.cfcs (pzc (ob<x lim ia<x) ) <-osuc o≤-refl uz03 fca where
           uz02 : FClosure A f (ZChain.supf (pzc (ob<x lim ia<x)) ia ) z
           uz02 = fca
           uz03 : ZChain.supf (pzc (ob<x lim ia<x)) ia o≤ ia
           uz03 = sa<x

      chain⊆pchainU : {z w : Ordinal } → (z<x : z o< x) → odef (UnionCF A f ay (ZChain.supf (pzc (ob<x lim z<x))) z) w → odef pchainU w
      chain⊆pchainU {z} {w} z<x ⟪ aw , ch-init fc ⟫ = ⟪ aw , ic-init fc ⟫
      chain⊆pchainU {z} {w} z<x ⟪ aw , ch-is-sup u u<oz su=u fc ⟫
         = ⟪ aw , ic-isup u u<x (o≤-refl0 su≡u) (subst (λ  k → FClosure A f k w ) su=su fc) ⟫ where
             u<x : u o< x
             u<x = ordtrans u<oz z<x
             su=su : ZChain.supf (pzc (ob<x lim z<x)) u ≡ supfz u<x
             su=su = sym ( zeq _ _  (o<→≤ (osucc u<oz)) (o<→≤ <-osuc) )
             su≡u :  supfz u<x ≡ u
             su≡u = begin
                ZChain.supf (pzc (ob<x lim u<x )) u ≡⟨ sym su=su ⟩
                ZChain.supf (pzc (ob<x lim z<x)) u  ≡⟨ su=u ⟩
                u ∎ where open ≡-Reasoning

      IC⊆ : {a b : Ordinal } (ia : IChain ay supfz a ) (ib : IChain ay supfz b )
          → IChain-i ia o< IChain-i ib → odef (ZChain.chain (pzc (pic<x ib))) a
      IC⊆ {a} {b} (ic-init fc ) ib ia<ib = ⟪ A∋fc _ f mf fc , ch-init fc ⟫
      IC⊆ {a} {b} (ic-isup i i<x sa<x fc ) (ic-init fcb ) ia<ib = ⊥-elim ( ¬x<0 ia<ib  )
      IC⊆ {a} {b} (ic-isup i i<x sa<x fc ) (ic-isup j j<x sb<x fcb ) ia<ib
          = ZChain.cfcs (pzc (ob<x lim j<x) ) (o<→≤ ia<ib) o≤-refl (OrdTrans (ZChain.supf-mono (pzc (ob<x lim j<x)) (o<→≤ ia<ib)) sb<x)
              (subst (λ k → FClosure A f k a) (zeq _ _ (osucc (o<→≤ ia<ib)) (o<→≤ <-osuc)) fc )

      ptotalU : IsTotalOrderSet pchainU
      ptotalU {a} {b} ia ib with trio< (IChain-i (proj2 ia)) (IChain-i (proj2 ib))
      ... | tri< ia<ib ¬b ¬c = ZChain.f-total (pzc (pic<x (proj2 ib))) (IC⊆ (proj2 ia) (proj2 ib) ia<ib) (pchainU⊆chain ib)
      ... | tri≈ ¬a ia=ib ¬c = pcmp (proj2 ia) (proj2 ib) ia=ib  where
           pcmp : (ia : IChain ay supfz a) → (ib : IChain ay supfz b) → IChain-i ia ≡ IChain-i ib
               → Tri (* a < * b) (a ≡ b) (* b < * a )
           pcmp (ic-init fca) (ic-init fcb) eq = fcn-cmp _ f mf fca fcb
           pcmp (ic-init fca) (ic-isup i i<x s<x fcb) eq with ZChain.fcy<sup (pzc i<x) o≤-refl fca
           ... | case1 eq1 = ct22 where
               ct22 : Tri (* a < * b) (a ≡ b) (* b < * a )
               ct22 with subst (λ k → k ≤ b) (sym (zeq _ _ (o<→≤ <-osuc) o≤-refl )) (s≤fc _ f mf fcb )
               ... | case1 eq2 =  tri≈ (λ lt → ⊥-elim (<-irr (case1 (sym ct00)) lt)) ct00  (λ lt → ⊥-elim (<-irr (case1 ct00) lt)) where
                   ct00 : a ≡ b
                   ct00 = trans eq1 eq2
               ... | case2 lt = tri< fc11 (λ eq → <-irr (case1 (sym eq)) fc11) (λ lt → <-irr (case2 fc11) lt) where
                   fc11 : * a < * b
                   fc11 = subst (λ k →  k < * b ) (cong (*) (sym eq1)) lt
           ... | case2 lt = tri< fc11 (λ eq → <-irr (case1 (sym eq)) fc11) (λ lt → <-irr (case2 fc11) lt) where
               fc11 : * a < * b
               fc11 = ftrans<-≤ lt (subst (λ k → k ≤ b) (sym (zeq _ _ (o<→≤ <-osuc) o≤-refl )) (s≤fc _ f mf fcb ) )
           pcmp (ic-isup i i<x s<x fca) (ic-init fcb) eq with ZChain.fcy<sup (pzc i<x) o≤-refl fcb
           ... | case1 eq1 =  ct22 where
               ct22 : Tri (* a < * b) (a ≡ b) (* b < * a )
               ct22 with subst (λ k → k ≤ a) (sym (zeq _ _ (o<→≤ <-osuc) o≤-refl )) (s≤fc _ f mf fca )
               ... | case1 eq2 =  tri≈ (λ lt → ⊥-elim (<-irr (case1 (sym ct00)) lt)) ct00  (λ lt → ⊥-elim (<-irr (case1 ct00) lt)) where
                   ct00 : a ≡ b
                   ct00 = sym (trans eq1 eq2)
               ... | case2 lt = tri> (λ lt → <-irr (case2 fc11) lt) (λ eq → <-irr (case1 eq) fc11) fc11  where
                   fc11 : * b < * a
                   fc11 = subst (λ k →  k < * a ) (cong (*) (sym eq1)) lt
           ... | case2 lt = tri> (λ lt → <-irr (case2 fc12) lt) (λ eq → <-irr (case1 eq) fc12) fc12  where
               fc12 : * b < * a
               fc12 = ftrans<-≤ lt (subst (λ k → k ≤ a) (sym (zeq _ _ (o<→≤ <-osuc) o≤-refl )) (s≤fc _ f mf fca ) )
           pcmp (ic-isup i i<x s<i fca) (ic-isup j j<x s<j fcb) eq  = fcn-cmp _ f mf fca (subst (λ k → FClosure A f k b) (pc03 j<x i<x eq) fcb ) where
               pc03 : (j<x : j o< x ) → (i<x : i o< x ) → i ≡ j → supfz j<x ≡ supfz i<x
               pc03 j<x i<x refl  = cong supfz o<-irr
      ... | tri> ¬a ¬b ib<ia = ZChain.f-total (pzc (pic<x (proj2 ia))) (pchainU⊆chain ia) (IC⊆ (proj2 ib) (proj2 ia) ib<ia)


      usup : MinSUP A pchainU
      usup = minsupP pchainU (λ ic → proj1 ic ) ptotalU
      spu0 = MinSUP.sup usup


      pchainS : HOD
      pchainS = record { od = record { def = λ z →  (odef A z  ∧ IChain  ay supfz z )
            ∨ (FClosure A f spu0 z ∧ (spu0 o< x)) } ; odmax = & A ; <odmax = zc00 } where
           zc00 : {z : Ordinal } → (odef A z ∧ IChain ay supfz z ) ∨ (FClosure A f spu0 z ∧ (spu0 o< x) )→ z o< & A
           zc00 {z} (case1 lt) = z07 lt
           zc00 {z} (case2 fc) = odef< ( A∋fc spu0 f mf (proj1 fc) )

      zc02 : { a b : Ordinal } → odef A a ∧ IChain ay supfz a → FClosure A f spu0 b ∧ ( spu0 o< x) → a ≤ b
      zc02 {a} {b} ca fb = zc05 (proj1 fb) where
         zc05 : {b : Ordinal } → FClosure A f spu0 b → a ≤ b
         zc05 (fsuc b1 fb ) with proj1 ( mf b1 (A∋fc spu0 f mf fb ))
         ... | case1 eq = subst (λ k → a ≤ k ) eq (zc05 fb)
         ... | case2 lt = ≤-ftrans (zc05 fb) (case2 lt)
         zc05 (init b1 refl) = MinSUP.x≤sup usup ca

      ptotalS : IsTotalOrderSet pchainS
      ptotalS (case1 a) (case1 b) =  ptotalU a b
      ptotalS {a0} {b0} (case1 a) (case2 b) with zc02 a b
      ... | case1 eq = tri≈ (<-irr (case1 (sym eq))) eq (<-irr (case1 eq)) 
      ... | case2 lt = tri< lt (λ eq → <-irr (case1 (sym eq)) lt) (<-irr (case2 lt)) 
      ptotalS {b0} {a0} (case2 b) (case1 a) with zc02 a b
      ... | case1 eq = tri≈ (<-irr (case1 eq)) (sym eq) (<-irr (case1 (sym eq))) 
      ... | case2 lt = tri> (<-irr (case2 lt)) (λ eq → <-irr (case1 eq) lt) lt  
      ptotalS (case2 a) (case2 b) = fcn-cmp spu0 f mf (proj1 a) (proj1 b)

      S⊆A : pchainS ⊆ A
      S⊆A (case1 lt) = proj1 lt
      S⊆A (case2 fc) = A∋fc _ f mf (proj1 fc)

      ssup : MinSUP A pchainS
      ssup = minsupP pchainS S⊆A ptotalS

      zc400 : MinSUP A pchainU → MinSUP A pchainS → ZChain A f mf< ay x
      zc400 usup ssup = record { supf = supf1 ; asupf = asupf ; zo≤sz = zo≤sz   ; is-minsup = is-minsup ; cfcs = cfcs ; supf-mono = supf-mono  }  where

          spu = MinSUP.sup usup
          sps = MinSUP.sup ssup

          supf1 : Ordinal → Ordinal
          supf1 z with trio< z x
          ... | tri< a ¬b ¬c = ZChain.supf (pzc  (ob<x lim a)) z   -- each sup o< x
          ... | tri≈ ¬a b ¬c = spu                                 -- sup of all sup o< x
          ... | tri> ¬a ¬b c = sps                                 -- sup of spu which o< x
                                                --  if x o< spu, spu is not included in UnionCF x
          -- the chain

          pchain : HOD
          pchain = UnionCF A f ay supf1 x

          -- pchain ⊆ pchainU ⊆ pchianS

          sf1=sf : {z : Ordinal } → (a : z o< x ) → supf1 z ≡ ZChain.supf (pzc  (ob<x lim a)) z
          sf1=sf {z} z<x with trio< z x
          ... | tri< a ¬b ¬c = cong ( λ k → ZChain.supf (pzc (ob<x lim k)) z) o<-irr
          ... | tri≈ ¬a b ¬c = ⊥-elim (¬a z<x)
          ... | tri> ¬a ¬b c = ⊥-elim (¬a z<x)

          sf1=spu : {z : Ordinal } → x ≡ z → supf1 z ≡ spu
          sf1=spu {z} eq with trio< z x
          ... | tri< a ¬b ¬c = ⊥-elim (¬b (sym eq))
          ... | tri≈ ¬a b ¬c = refl
          ... | tri> ¬a ¬b c = ⊥-elim (¬b (sym eq))

          sf1=sps : {z : Ordinal } → (a : x o< z ) → supf1 z ≡ sps
          sf1=sps {z} x<z with trio< z x
          ... | tri< a ¬b ¬c = ⊥-elim (o<> x<z a)
          ... | tri≈ ¬a b ¬c = ⊥-elim (¬c x<z )
          ... | tri> ¬a ¬b c = refl

          asupf : {z : Ordinal } → odef A (supf1 z)
          asupf {z} with trio< z x
          ... | tri< a ¬b ¬c = ZChain.asupf (pzc  (ob<x lim a))
          ... | tri≈ ¬a b ¬c = MinSUP.as usup
          ... | tri> ¬a ¬b c = MinSUP.as ssup

          supf-mono : {z y : Ordinal } → z o≤ y → supf1 z o≤ supf1 y
          supf-mono {z} {y} z≤y with trio< y x
          ... | tri< y<x ¬b ¬c = zc01 where
               open o≤-Reasoning 
               zc01 : supf1 z o≤ ZChain.supf (pzc  (ob<x lim y<x)) y
               zc01 = begin
                  supf1 z ≡⟨ sf1=sf (ordtrans≤-< z≤y y<x)  ⟩
                  ZChain.supf (pzc  (ob<x lim (ordtrans≤-< z≤y y<x))) z ≡⟨ zeq _ _ (osucc z≤y) (o<→≤ <-osuc)  ⟩
                  ZChain.supf (pzc  (ob<x lim y<x)) z ≤⟨ ZChain.supf-mono (pzc  (ob<x lim y<x)) z≤y  ⟩
                  ZChain.supf (pzc  (ob<x lim y<x)) y ∎
          ... | tri≈ ¬a b ¬c = zc01 where  -- supf1 z o≤ spu
               open o≤-Reasoning 
               zc01 : supf1 z o≤ spu
               zc01 with osuc-≡< (subst (λ k → z o≤ k) b z≤y)
               ... | case1 z=x = o≤-refl0 (sf1=spu (sym z=x))
               ... | case2 z<x = subst (λ k → k o≤ spu ) (sym (sf1=sf z<x)) ( IsMinSUP.minsup (ZChain.is-minsup (pzc (ob<x lim z<x)) (o<→≤ <-osuc) )
                 (MinSUP.as usup) (λ uw → MinSUP.x≤sup usup (chain⊆pchainU z<x uw)) )
          ... | tri> ¬a ¬b c = zc01 where  -- supf1 z o≤ sps
               zc01 : supf1 z o≤ sps
               zc01 with trio< z x
               ... | tri< z<x ¬b ¬c = IsMinSUP.minsup (ZChain.is-minsup (pzc (ob<x lim z<x)) (o<→≤ <-osuc) )
                 (MinSUP.as ssup) (λ uw → MinSUP.x≤sup ssup (case1 (chain⊆pchainU z<x uw)) )
               ... | tri≈ ¬a z=x ¬c = MinSUP.minsup usup (MinSUP.as ssup) (λ uw → MinSUP.x≤sup ssup (case1 uw) )
               ... | tri> ¬a ¬b c = o≤-refl -- (sf1=sps c)

          is-minsup :  {z : Ordinal} → z o≤ x → IsMinSUP A (UnionCF A f ay supf1 z) (supf1 z)
          is-minsup {z} z≤x with osuc-≡< z≤x
          ... | case1 z=x = record { as = asupf ; x≤sup = zm00 ; minsup = zm01 } where
               zm00 : {w : Ordinal } → odef (UnionCF A f ay supf1 z) w → w ≤ supf1 z
               zm00 {w} ⟪ az , ch-init fc ⟫ = subst (λ k → w ≤ k ) (sym (sf1=spu (sym z=x))) ( MinSUP.x≤sup usup ⟪ az , ic-init fc ⟫ )
               zm00 {w} ⟪ az , ch-is-sup u u<b su=u fc ⟫ = subst (λ k → w ≤ k ) (sym (sf1=spu (sym z=x)))
                   ( MinSUP.x≤sup usup  ⟪ az , ic-isup u u<x (o≤-refl0 zm05) (subst (λ k → FClosure A f k w) (sym zm06) fc)  ⟫  ) where
                       u<x : u o< x
                       u<x = subst (λ k → u o< k) z=x u<b
                       zm06 : supfz (subst (λ k → u o< k) z=x u<b) ≡ supf1 u
                       zm06 = trans (zeq _ _  o≤-refl (o<→≤ <-osuc) ) (sym (sf1=sf u<x ))
                       zm05 : supfz (subst (λ k → u o< k) z=x u<b) ≡ u
                       zm05 = trans zm06 su=u
               zm01 : { s : Ordinal } → odef A s →  ( {x : Ordinal  } → odef (UnionCF A f ay supf1 z) x → x ≤ s )  → supf1 z o≤ s
               zm01 {s} as sup = subst (λ k → k o≤ s ) (sym (sf1=spu (sym z=x))) ( MinSUP.minsup usup as zm02 ) where
                   zm02 : {w : Ordinal } →  odef pchainU w → w ≤ s
                   zm02 {w} uw with pchainU⊆chain uw
                   ... | ⟪ az , ch-init fc ⟫ = sup ⟪ az , ch-init fc ⟫
                   ... | ⟪ az , ch-is-sup u1 u<b su=u fc ⟫ = sup  ⟪ az , ch-is-sup u1 (ordtrans u<b zm05) (trans zm03 su=u) zm04 ⟫  where
                       zm05 : osuc (IChain-i (proj2 uw)) o< z
                       zm05 = subst (λ k → osuc  (IChain-i (proj2 uw)) o< k) (sym z=x) ( pic<x (proj2 uw) )
                       u<x : u1 o< x
                       u<x = subst (λ k → u1 o< k) z=x ( ordtrans u<b zm05 )
                       zm03 : supf1 u1 ≡ ZChain.supf (prev (osuc (IChain-i (proj2 uw))) (pic<x (proj2 uw))) u1
                       zm03 = trans (sf1=sf u<x) (zeq _ _ (osucc u<b) (o<→≤ <-osuc) )
                       zm04 : FClosure A f (supf1 u1) w
                       zm04 = subst (λ k → FClosure A f k w) (sym zm03) fc
          ... | case2 z<x = record { as = asupf ; x≤sup = zm00 ; minsup = zm01 } where
               supf0 = ZChain.supf (pzc (ob<x lim z<x))
               msup : IsMinSUP A (UnionCF A f ay supf0 z) (supf0 z)
               msup = ZChain.is-minsup (pzc (ob<x lim z<x)) (o<→≤ <-osuc)
               s1=0 : {u : Ordinal } → u o< z → supf1 u ≡ supf0 u
               s1=0 {u} u<z = trans (sf1=sf (ordtrans u<z z<x)) (zeq _ _ (o<→≤ (osucc u<z))  (o<→≤ <-osuc) )
               zm00 : {w : Ordinal } → odef (UnionCF A f ay supf1 z) w → w ≤ supf1 z
               zm00 {w} ⟪ az , ch-init fc ⟫ = subst (λ k → w ≤ k ) (sym (sf1=sf z<x)) ( IsMinSUP.x≤sup msup  ⟪ az , ch-init fc ⟫ )
               zm00 {w} ⟪ az , ch-is-sup u u<b su=u fc ⟫ = subst (λ k → w ≤ k ) (sym (sf1=sf z<x))
                  ( IsMinSUP.x≤sup msup  ⟪ az , ch-is-sup u u<b (trans (sym (s1=0 u<b)) su=u)  (subst (λ k → FClosure A f k w) (s1=0 u<b) fc)  ⟫  )
               zm01 : { s : Ordinal } → odef A s →  ( {x : Ordinal  } → odef (UnionCF A f ay supf1 z) x → x ≤ s )  → supf1 z o≤ s
               zm01 {s} as sup = subst (λ k → k o≤ s ) (sym (sf1=sf z<x)) ( IsMinSUP.minsup msup as zm02 ) where
                   zm02 : {w : Ordinal } →  odef (UnionCF A f ay supf0 z) w → w ≤ s
                   zm02 {w} ⟪ az , ch-init fc ⟫ = sup ⟪ az , ch-init fc ⟫
                   zm02 {w} ⟪ az , ch-is-sup u u<b su=u fc ⟫ = sup
                       ⟪ az , ch-is-sup u u<b (trans (s1=0 u<b) su=u) (subst (λ k → FClosure A f k w) (sym (s1=0 u<b)) fc) ⟫


          cfcs :  {a b w : Ordinal } → a o< b → b o≤ x →  supf1 a o< b → FClosure A f (supf1 a) w → odef (UnionCF A f ay supf1 b) w
          cfcs {a} {b} {w} a<b b≤x sa<b fc with osuc-≡< b≤x
          ... | case1 b=x with trio< a x
          ... | tri< a<x ¬b ¬c = zc40 where
               sa = ZChain.supf (pzc  (ob<x lim a<x)) a
               m =  omax a sa     -- x is limit ordinal, so we have sa o< m o< x
               m<x : m o< x
               m<x with trio< a sa 
               ... | tri< a<sa ¬b ¬c = ob<x lim (ordtrans<-≤ sa<b b≤x )
               ... | tri≈ ¬a a=sa ¬c = zc41 where 
                   zc41 : osuc a o< x
                   zc41 = osucprev ( begin
                       osuc ( osuc  a ) ≤⟨ o<→≤ (ob<x lim (ob<x lim a<x))  ⟩
                       x ∎ ) where open o≤-Reasoning 
               ... | tri> ¬a ¬b c = ob<x lim a<x
               sam = ZChain.supf (pzc (ob<x lim m<x)) a
               zc42 : osuc a o≤ osuc m
               zc42 = osucc (o<→≤ ( omax-x _ _ ) )
               sam<m : sam o< m
               sam<m = subst (λ k → k o< m ) (supf-unique A f mf< ay zc42 (pzc (ob<x lim a<x)) (pzc (ob<x lim m<x)) (o<→≤ <-osuc)) ( omax-y _ _ )
               fcm : FClosure A f (ZChain.supf (pzc (ob<x lim m<x)) a) w
               fcm = subst (λ k → FClosure A f k w ) (zeq (ob<x lim a<x) (ob<x lim m<x) zc42 (o<→≤ <-osuc) ) fc
               zcm : odef (UnionCF A f ay (ZChain.supf (pzc  (ob<x lim m<x))) (osuc (omax a sa))) w
               zcm = ZChain.cfcs (pzc  (ob<x lim m<x)) (o<→≤ (omax-x _ _)) o≤-refl (o<→≤ sam<m) fcm
               zc40 : odef (UnionCF A f ay supf1 b) w
               zc40 with ZChain.cfcs (pzc  (ob<x lim m<x)) (o<→≤ (omax-x _ _)) o≤-refl (o<→≤ sam<m) fcm
               ... | ⟪ az , ch-init fc ⟫ = ⟪ az , ch-init fc ⟫
               ... | ⟪ az , ch-is-sup u u<x su=u fc ⟫ = ⟪ az , ch-is-sup u u<b (trans zc45 su=u) zc44 ⟫ where
                   u<b : u o< b
                   u<b = osucprev ( begin
                       osuc u ≤⟨ osucc u<x ⟩
                       osuc m ≤⟨ osucc m<x ⟩
                       x ≡⟨ sym b=x ⟩
                       b ∎ ) where open o≤-Reasoning 
                   zc45 : supf1 u ≡  ZChain.supf (pzc  (ob<x lim m<x)) u
                   zc45 = begin
                       supf1 u ≡⟨ sf1=sf (subst (λ k → u o< k) b=x u<b )  ⟩
                       ZChain.supf (pzc  (ob<x lim (subst (λ k → u o< k) b=x u<b ))) u  ≡⟨ zeq _ _ (osucc u<x) (o<→≤ <-osuc)  ⟩
                       ZChain.supf (pzc  (ob<x lim m<x)) u ∎  where open ≡-Reasoning
                   zc44 : FClosure A f (supf1 u) w
                   zc44 = subst (λ k → FClosure A f k w ) (sym zc45) fc
          ... | tri≈ ¬a b ¬c = ⊥-elim ( ¬a (ordtrans<-≤ a<b b≤x))
          ... | tri> ¬a ¬b c = ⊥-elim ( ¬a (ordtrans<-≤ a<b b≤x))
          cfcs {a} {b} {w} a<b b≤x sa<b fc | case2 b<x = zc40 where
               supfb =  ZChain.supf (pzc (ob<x lim b<x))
               sb=sa : {a : Ordinal } → a o< b → supf1 a ≡ ZChain.supf (pzc (ob<x lim b<x)) a
               sb=sa {a} a<b = trans (sf1=sf (ordtrans<-≤ a<b b≤x)) (zeq _ _ (o<→≤ (osucc a<b)) (o<→≤ <-osuc) )
               fcb : FClosure A f (supfb a) w
               fcb = subst (λ k → FClosure A f k w) (sb=sa a<b) fc
               --  supfb a o< b assures it is in Union b
               zcb : odef (UnionCF A f ay supfb b) w
               zcb = ZChain.cfcs (pzc (ob<x lim b<x)) a<b (o<→≤ <-osuc) (subst (λ k → k o< b) (sb=sa a<b) sa<b) fcb
               zc40 : odef (UnionCF A f ay supf1 b) w
               zc40 with zcb
               ... | ⟪ az , ch-init fc ⟫ = ⟪ az , ch-init fc ⟫
               ... | ⟪ az , ch-is-sup u u<x su=u fc ⟫ = ⟪ az , ch-is-sup u u<x (trans zc45 su=u) zc44  ⟫ where
                   zc45 : supf1 u ≡  ZChain.supf (pzc  (ob<x lim b<x)) u
                   zc45 = begin
                       supf1 u ≡⟨ sf1=sf (ordtrans u<x b<x)  ⟩
                       ZChain.supf (pzc  (ob<x lim (ordtrans u<x b<x) )) u  ≡⟨ zeq _ _ (o<→≤ (osucc u<x)) (o<→≤ <-osuc)  ⟩
                       ZChain.supf (pzc  (ob<x lim b<x )) u ∎  where open ≡-Reasoning
                   zc44 : FClosure A f (supf1 u) w
                   zc44 = subst (λ k → FClosure A f k w ) (sym zc45) fc

          zo≤sz : {z : Ordinal} →  z o≤ x → z o≤ supf1 z
          zo≤sz {z} z≤x with osuc-≡< z≤x
          ... | case2 z<x = subst (λ k → z o≤ k) (sym (trans (sf1=sf z<x) (sym (zeq _ _ (o<→≤ <-osuc) o≤-refl)))) ( ZChain.zo≤sz (pzc z<x) o≤-refl )
          ... | case1 eq with x<y∨y≤x (supf1 spu) x
          ... | case2 x≤ssp = z40 where
                   z40 : z o≤ supf1 z
                   z40 with  x<y∨y≤x z spu
                   ... | case1 z<spu = subst (λ k →  z o≤ supf1 k) (sym eq) (o<→≤ ( subst (λ k → z o< k ) (sym (sf1=spu refl)) z<spu ) )
                   ... | case2 spu≤z =  begin   -- x ≡ supf1 spu ≡ spu ≡ supf1 x
                      z ≡⟨ eq ⟩
                      x ≤⟨ x≤ssp ⟩
                      supf1 spu ≤⟨ supf-mono spu≤z ⟩
                      supf1 z ∎   where open o≤-Reasoning 
          ... | case1 ssp<x = z49 where 
               z47 : x o≤ spu
               z47 with x<y∨y≤x spu x
               ... | case2 lt = lt
               ... | case1 spu<x = ⊥-elim ( <<-irr (MinSUP.x≤sup usup z48) (proj1 ( mf< spu (MinSUP.as usup))))  where
                   z70 : odef (UnionCF A f ay supf1 z) (supf1 spu)
                   z70 = subst (λ k →  odef (UnionCF A f ay supf1 k) (supf1 spu)) (sym eq) ( cfcs spu<x o≤-refl ssp<x (init asupf refl ) )
                   z73 : IsSUP A (UnionCF A f ay (ZChain.supf (pzc (ob<x lim spu<x))) spu) spu
                   z73 = record { ax = MinSUP.as usup ; x≤sup = λ uw → MinSUP.x≤sup usup (chain⊆pchainU spu<x uw ) }
                   z49 : supfz spu<x ≡ spu
                   z49 = begin
                      supfz spu<x ≡⟨ ZChain.sup=u (pzc (ob<x lim spu<x)) (MinSUP.as usup) (o<→≤ <-osuc) z73 ⟩
                      spu ∎ where open ≡-Reasoning
                   z50 : supfz spu<x o≤ spu
                   z50 = o≤-refl0 z49
                   z48 : odef pchainU (f spu)
                   z48 = ⟪  proj2 (mf _ (MinSUP.as usup) ) , ic-isup _ (subst (λ k → k o< x) refl spu<x) z50
                        (fsuc _ (init (ZChain.asupf (pzc (ob<x lim spu<x))) z49)) ⟫
               z49 : z o≤ supf1 z
               z49 = begin
                   z ≡⟨ eq ⟩
                   x ≤⟨ z47 ⟩
                   spu ≡⟨ sym (sf1=spu (sym eq)) ⟩
                   supf1 z ∎   where open o≤-Reasoning 

     ---
     --- the maximum chain  has fix point of any ≤-monotonic function
     ---

     SZ : ( f : Ordinal → Ordinal ) → (mf< : <-monotonic-f A f ) → {y : Ordinal} (ay : odef A y) → (x : Ordinal) → ZChain A f mf< ay x
     SZ f mf< {y} ay x = TransFinite {λ z → ZChain A f mf< ay z  } (λ x → ind f mf< ay x   ) x

     msp0 : ( f : Ordinal → Ordinal ) → (mf< : <-monotonic-f A f ) {x y : Ordinal} (ay : odef A y)
         → (zc : ZChain A f mf< ay x )
         → MinSUP A (UnionCF A f ay (ZChain.supf zc) x)
     msp0 f mf< {x} ay zc = minsupP (UnionCF A f ay (ZChain.supf zc) x) (ZChain.chain⊆A zc) (ZChain.f-total zc)

     -- f eventualy stop
     --    we can prove contradict here, it is here for a historical reason
     --
     fixpoint :  ( f : Ordinal → Ordinal ) → (mf : ≤-monotonic-f A f ) (mf< : <-monotonic-f A f )  (zc : ZChain A f mf< as (& A) )
            → (sp1 : MinSUP A (ZChain.chain zc))
            → f (MinSUP.sup sp1)  ≡ MinSUP.sup sp1
     fixpoint f mf mf< zc sp1 = z14 where
           chain = ZChain.chain zc
           supf = ZChain.supf zc
           sp : Ordinal
           sp = MinSUP.sup sp1
           asp : odef A sp
           asp = MinSUP.as sp1
           ay = as
           z10 :  {a b : Ordinal } → (ca : odef chain a ) → b o< (& A) → (ab : odef A b )
              →  HasPrev A chain f b  ∨  IsSUP A (UnionCF A f ay (ZChain.supf zc) b) b
              → * a < * b  → odef chain b
           z10 = ZChain1.is-max (SZ1 f mf mf< as zc (& A) o≤-refl )
           z22 : sp o< & A
           z22 = odef< asp
           z12 : odef chain sp
           z12 with o≡? (& s) sp
           ... | yes0 eq = subst (λ k → odef chain k) eq ( ZChain.chain∋init zc )
           ... | no0 ne = ZChain1.is-max (SZ1 f mf mf< as zc (& A) o≤-refl) {& s} {sp} ( ZChain.chain∋init zc ) (odef< asp) asp (case2 z19 ) z13 where
               z13 :  * (& s) < * sp
               z13 with MinSUP.x≤sup sp1 ( ZChain.chain∋init zc )
               ... | case1 eq = ⊥-elim ( ne eq )
               ... | case2 lt = lt
               z19 : IsSUP A (UnionCF A f ay (ZChain.supf zc) sp) sp
               z19 = record { ax = asp ;   x≤sup = z20 }  where
                   z20 : {y : Ordinal} → odef (UnionCF A f ay (ZChain.supf zc) sp) y → (y ≡ sp) ∨ (y << sp)
                   z20 {y} zy with MinSUP.x≤sup sp1
                       (subst (λ k → odef chain k ) (sym &iso) (chain-mono f mf as supf (ZChain.supf-mono zc) (o<→≤ z22)  zy ))
                   ... | case1 y=p = case1 (subst (λ k → k ≡ _ ) &iso y=p )
                   ... | case2 y<p = case2 (subst (λ k → * k < _ ) &iso y<p )
           z14 :  f sp ≡ sp
           z14 with ZChain.f-total zc (subst (λ k → odef chain k) (sym &iso)  (ZChain.f-next zc z12 )) (subst (λ k → odef chain k) (sym &iso) z12 )
           ... | tri< a ¬b ¬c = ⊥-elim z16 where
               z16 : ⊥
               z16 with proj1 (mf (( MinSUP.sup sp1)) ( MinSUP.as sp1 ))
               ... | case1 eq = ⊥-elim (¬b (sym (trans &iso (trans eq (sym &iso) ))))
               ... | case2 lt = ⊥-elim (¬c (<-cong (==-sym *iso) (==-sym *iso) lt) )
           ... | tri≈ ¬a b ¬c = trans (sym &iso) (trans b &iso )
           ... | tri> ¬a ¬b c = ⊥-elim z17 where
               z15 : (f sp ≡ MinSUP.sup sp1) ∨ (* (f sp) < * (MinSUP.sup sp1) )
               z15  = MinSUP.x≤sup sp1 (ZChain.f-next zc z12 )
               z17 : ⊥
               z17 with z15
               ... | case1 eq = ¬b (trans &iso (trans eq (sym &iso)))
               ... | case2 lt = ¬a (<-cong (==-sym *iso) (==-sym *iso) lt )

     -- ZChain contradicts ¬ Maximal
     --
     -- ZChain forces fix point on any ≤-monotonic function (fixpoint)
     -- ¬ Maximal create cf which is a <-monotonic function by axiom of choice. This contradicts fix point of ZChain
     --

     ¬Maximal→¬cf-mono :  (nmx : ¬ Maximal A ) → (zc : ZChain A (cf nmx) (cf-is-<-monotonic nmx) as (& A)) → ⊥
     ¬Maximal→¬cf-mono nmx zc = <-irr  {cf nmx c} {c}
           -- (subst (λ k → odef A k ) (sym &iso) (proj1 (is-cf nmx (MinSUP.as  msp1 ))))
           -- (subst (λ k → odef A k) (sym &iso) (MinSUP.as msp1) )
           (case1 ( fixpoint (cf nmx) (cf-is-≤-monotonic nmx ) (cf-is-<-monotonic nmx ) zc msp1 )) -- x ≡ f x ̄
           (proj1 (cf-is-<-monotonic nmx c (MinSUP.as msp1)))  where          -- x < f x
          supf = ZChain.supf zc
          msp1 : MinSUP A (ZChain.chain zc)
          msp1 = msp0 (cf nmx) (cf-is-<-monotonic nmx) as zc
          c : Ordinal
          c = MinSUP.sup msp1

     zorn00 : Maximal A
     zorn00 with is-o∅ ( & HasMaximal )  
     ... | no0 not = record { maximal = minimal HasMaximal  (λ eq → not (=od∅→≡o∅ eq)) ; as = zorn01 ; ¬maximal<x  = zorn02 } where
         -- yes0 we have the maximal because of the axiom of choice 
         zorn03 :  odef HasMaximal ( & ( minimal HasMaximal  (λ eq → not (=od∅→≡o∅ eq)) ) )
         zorn03 =  x∋minimal  HasMaximal  (λ eq → not (=od∅→≡o∅ eq))   -- Axiom of choice
         zorn01 :  A ∋ minimal HasMaximal (λ eq → not (=od∅→≡o∅ eq))
         zorn01  = proj1  zorn03
         zorn02 : {x : HOD} → A ∋ x → ¬ (minimal HasMaximal (λ eq → not (=od∅→≡o∅ eq)) < x)
         zorn02 {x} ax m<x = proj2 zorn03 (& x) ax (<-cong (==-sym *iso) (==-sym *iso) m<x )
     ... | yes0 ¬Maximal = ⊥-elim ( ¬Maximal→¬cf-mono nmx (SZ (cf nmx) (cf-is-<-monotonic nmx) as (& A) )) where
         -- if we have no0 maximal, make ZChain, which contradict SUP condition
         nmx : ¬ Maximal A
         nmx mx =  ∅< {HasMaximal} zc5 ( ≡o∅→=od∅  ¬Maximal ) where
              zc5 : odef A (& (Maximal.maximal mx)) ∧ (( y : Ordinal ) →  odef A y → ¬ (* (& (Maximal.maximal mx)) < * y))
              zc5 = ⟪  Maximal.as mx , (λ y ay mx<y → Maximal.¬maximal<x mx (subst (λ k → odef A k ) (sym &iso) ay) (<-cong *iso ==-refl mx<y) ) ⟫

-- usage (see filter.agda )
--
--  import OD hiding ( _⊆_ )
-- _⊆_ : ( A B : HOD ) → Set n
-- _⊆_ A B = {x : Ordinal } → odef A x → odef B x
-- 
-- import zorn 
-- open zorn O _⊆_   -- Zorn on Set inclusion order 
-- 
-- open import  Relation.Binary.Structures

-- MaximumSubset : {L P : HOD}
--        → o∅ o< & L →  o∅ o< & P → P ⊆ L
--        → IsPartialOrderSet P _⊆_
--        → ( (B : HOD) → B ⊆ P → IsTotalOrderSet B _⊆_ → SUP P B _⊆_ )
--        → Maximal P (_⊆_)
-- MaximumSubset {L} {P} 0<L 0<P P⊆L PO SP  = Zorn-lemma {P} {_⊆_} 0<P PO SP
--

