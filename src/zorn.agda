{-# OPTIONS --allow-unsolved-metas #-}
open import Level hiding ( suc ; zero )
open import Ordinals
open import Relation.Binary 
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality
import OD 
module zorn {n : Level } (O : Ordinals {n}) (_<_ : (x y : OD.HOD O ) → Set n ) (PO : IsStrictPartialOrder _≡_ _<_ ) where

--
-- Zorn-lemma : { A : HOD } 
--     → o∅ o< & A 
--     → ( ( B : HOD) → (B⊆A : B ⊆ A) → IsTotalOrderSet B → SUP A B   ) -- SUP condition
--     → Maximal A 
--

open import zf
open import logic
-- open import partfunc {n} O

open import Relation.Nullary 
open import Data.Empty 
import BAlgbra 

open import Data.Nat hiding ( _<_ ; _≤_ )
open import Data.Nat.Properties 
open import nat 


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


open _∧_
open _∨_
open Bool


open HOD

--
-- Partial Order on HOD ( possibly limited in A )
--

_≤_ : (x y : HOD) → Set (Level.suc n)
x ≤ y = ( x ≡ y ) ∨ ( x < y )

≤-ftrans : {x y z : HOD} → x ≤ y → y ≤ z → x ≤ z 
≤-ftrans {x} {y} {z} (case1 refl ) (case1 refl ) = case1 refl
≤-ftrans {x} {y} {z} (case1 refl ) (case2 y<z) = case2 y<z
≤-ftrans {x} {_} {z} (case2 x<y ) (case1 refl ) = case2 x<y
≤-ftrans {x} {y} {z} (case2 x<y) (case2 y<z) = case2 ( IsStrictPartialOrder.trans PO x<y y<z )

<-irr : {a b : HOD} → (a ≡ b ) ∨ (a < b ) → b < a → ⊥
<-irr {a} {b} (case1 a=b) b<a = IsStrictPartialOrder.irrefl PO   (sym a=b) b<a
<-irr {a} {b} (case2 a<b) b<a = IsStrictPartialOrder.irrefl PO   refl
          (IsStrictPartialOrder.trans PO     b<a a<b)

open _==_
open _⊆_

--
-- Closure of ≤-monotonic function f has total order
--

≤-monotonic-f : (A : HOD) → ( Ordinal → Ordinal ) → Set (Level.suc n)
≤-monotonic-f A f = (x : Ordinal ) → odef A x → ( * x ≤ * (f x) ) ∧  odef A (f x )

-- immieate-f : (A : HOD) → ( f : Ordinal → Ordinal )  → Set n
-- immieate-f A f = { x y : Ordinal } → odef A x → odef A y → ¬ ( ( * x < * y ) ∧ ( * y < * (f x )) )

data FClosure (A : HOD) (f : Ordinal → Ordinal ) (s : Ordinal) : Ordinal → Set n where
   init : odef A s → FClosure A f s s
   fsuc : (x : Ordinal) ( p :  FClosure A f s x ) → FClosure A f s (f x)

A∋fc : {A : HOD} (s : Ordinal) {y : Ordinal } (f : Ordinal → Ordinal) (mf : ≤-monotonic-f A f) → (fcy : FClosure A f s y ) → odef A y
A∋fc {A} s f mf (init as) = as
A∋fc {A} s f mf (fsuc y fcy) = proj2 (mf y ( A∋fc {A} s  f mf fcy ) )

s≤fc : {A : HOD} (s : Ordinal ) {y : Ordinal } (f : Ordinal → Ordinal) (mf : ≤-monotonic-f A f) → (fcy : FClosure A f s y ) → * s ≤ * y
s≤fc {A} s {.s} f mf (init x) = case1 refl
s≤fc {A} s {.(f x)} f mf (fsuc x fcy) with proj1 (mf x (A∋fc s f mf fcy ) )
... | case1 x=fx = subst (λ k → * s ≤ * k ) (*≡*→≡ x=fx) ( s≤fc {A} s f mf fcy )
... | case2 x<fx with s≤fc {A} s f mf fcy 
... | case1 s≡x = case2 ( subst₂ (λ j k → j < k ) (sym s≡x) refl x<fx )
... | case2 s<x = case2 ( IsStrictPartialOrder.trans PO s<x x<fx )

fcn : {A : HOD} (s : Ordinal) { x : Ordinal} {f : Ordinal → Ordinal} → (mf : ≤-monotonic-f A f) → FClosure A f s x → ℕ
fcn s mf (init as) = zero
fcn {A} s {x} {f} mf (fsuc y p) with proj1 (mf y (A∋fc s f mf p))
... | case1 eq = fcn s mf p
... | case2 y<fy = suc (fcn s mf p )

fcn-inject : {A : HOD} (s : Ordinal) { x y : Ordinal} {f : Ordinal → Ordinal} → (mf : ≤-monotonic-f A f) 
     → (cx : FClosure A f s x ) (cy : FClosure A f s y ) → fcn s mf cx  ≡ fcn s mf cy → * x ≡ * y
fcn-inject {A} s {x} {y} {f} mf cx cy eq = fc00 (fcn s mf cx) (fcn s mf cy) eq cx cy refl refl where
     fc00 :  (i j : ℕ ) → i ≡ j  →  {x y : Ordinal } → (cx : FClosure A f s x ) (cy : FClosure A f s y ) → i ≡ fcn s mf cx  → j ≡ fcn s mf cy → * x ≡ * y
     fc00 zero zero refl (init _) (init x₁) i=x i=y = refl
     fc00 zero zero refl (init sa) (fsuc y cy) i=x i=y with proj1 (mf y (A∋fc s f mf cy ) )
     ... | case1 y=fy = subst (λ k → * s ≡ k ) y=fy ( fc00 zero zero refl (init sa) cy i=x i=y )
     fc00 zero zero refl (fsuc x cx) (init sa) i=x i=y with proj1 (mf x (A∋fc s f mf cx ) )
     ... | case1 x=fx = subst (λ k → k ≡ * s ) x=fx ( fc00 zero zero refl cx (init sa) i=x i=y )
     fc00 zero zero refl (fsuc x cx) (fsuc y cy) i=x i=y with proj1 (mf x (A∋fc s f mf cx ) ) | proj1 (mf y (A∋fc s f mf cy ) )
     ... | case1 x=fx  | case1 y=fy = subst₂ (λ j k → j ≡ k ) x=fx y=fy ( fc00 zero zero refl cx cy  i=x i=y )
     fc00 (suc i) (suc j) i=j {.(f x)} {.(f y)} (fsuc x cx) (fsuc y cy) i=x j=y with proj1 (mf x (A∋fc s f mf cx ) ) | proj1 (mf y (A∋fc s f mf cy ) )
     ... | case1 x=fx | case1 y=fy = subst₂ (λ j k → j ≡ k ) x=fx y=fy ( fc00 (suc i) (suc j) i=j cx cy  i=x j=y )
     ... | case1 x=fx | case2 y<fy = subst (λ k → k ≡ * (f y)) x=fx (fc02 x cx i=x) where
          fc02 : (x1 : Ordinal) → (cx1 : FClosure A f s x1 ) →  suc i ≡ fcn s mf cx1 → * x1 ≡ * (f y)
          fc02 .(f x1) (fsuc x1 cx1) i=x1 with proj1 (mf x1 (A∋fc s f mf cx1 ) )
          ... | case1 eq = trans (sym eq) ( fc02  x1 cx1 i=x1 )  -- derefence while f x ≡ x
          ... | case2 lt = subst₂ (λ j k → * (f j) ≡ * (f k )) &iso &iso ( cong (λ k → * ( f (& k ))) fc04) where
               fc04 : * x1 ≡ * y
               fc04 = fc00 i j (cong pred i=j) cx1 cy (cong pred i=x1) (cong pred j=y)
     ... | case2 x<fx | case1 y=fy = subst (λ k → * (f x) ≡ k ) y=fy (fc03 y cy j=y) where
          fc03 : (y1 : Ordinal) → (cy1 : FClosure A f s y1 ) →  suc j ≡ fcn s mf cy1 → * (f x)  ≡ * y1
          fc03 .(f y1) (fsuc y1 cy1) j=y1 with proj1 (mf y1 (A∋fc s f mf cy1 ) )
          ... | case1 eq = trans ( fc03  y1 cy1 j=y1 ) eq 
          ... | case2 lt = subst₂ (λ j k → * (f j) ≡ * (f k )) &iso &iso ( cong (λ k → * ( f (& k ))) fc05) where
               fc05 : * x ≡ * y1
               fc05 = fc00 i j (cong pred i=j) cx cy1 (cong pred i=x) (cong pred j=y1)
     ... | case2 x₁ | case2 x₂ = subst₂ (λ j k → * (f j) ≡ * (f k) ) &iso &iso (cong (λ k → * (f (& k))) (fc00 i j (cong pred i=j) cx cy (cong pred i=x) (cong pred j=y)))

fcn-< : {A : HOD} (s : Ordinal ) { x y : Ordinal} {f : Ordinal → Ordinal} → (mf : ≤-monotonic-f A f)
    → (cx : FClosure A f s x ) (cy : FClosure A f s y ) → fcn s mf cx Data.Nat.< fcn s mf cy  → * x < * y
fcn-< {A} s {x} {y} {f} mf cx cy x<y = fc01 (fcn s mf cy) cx cy refl x<y where
     fc01 : (i : ℕ ) → {y : Ordinal } → (cx : FClosure A f s x ) (cy : FClosure A f s y ) → (i ≡ fcn s mf cy ) → fcn s mf cx Data.Nat.< i → * x < * y
     fc01 (suc i) {y} cx (fsuc y1 cy) i=y (s≤s x<i) with proj1 (mf y1 (A∋fc s f mf cy ) )
     ... | case1 y=fy = subst (λ k → * x < k ) y=fy ( fc01 (suc i) {y1} cx cy i=y (s≤s x<i)  ) 
     ... | case2 y<fy with <-cmp (fcn s mf cx ) i
     ... | tri> ¬a ¬b c = ⊥-elim ( nat-≤> x<i c )
     ... | tri≈ ¬a b ¬c = subst (λ k → k < * (f y1) ) (fcn-inject s mf cy cx (sym (trans b (cong pred i=y) ))) y<fy 
     ... | tri< a ¬b ¬c = IsStrictPartialOrder.trans PO fc02 y<fy where
          fc03 :  suc i ≡ suc (fcn s mf cy) → i ≡ fcn s mf cy
          fc03 eq = cong pred eq 
          fc02 :  * x < * y1 
          fc02 =  fc01 i cx cy (fc03 i=y ) a

fcn-cmp : {A : HOD} (s : Ordinal) { x y : Ordinal } (f : Ordinal → Ordinal) (mf : ≤-monotonic-f A f) 
    → (cx : FClosure A f s x) → (cy : FClosure A f s y ) → Tri (* x < * y) (* x ≡ * y) (* y < * x )
fcn-cmp {A} s {x} {y} f mf cx cy with <-cmp ( fcn s mf cx ) (fcn s mf cy )
... | tri< a ¬b ¬c = tri< fc11 (λ eq → <-irr (case1 (sym eq)) fc11) (λ lt → <-irr (case2 fc11) lt) where
      fc11 : * x < * y
      fc11 = fcn-< {A} s {x} {y} {f} mf cx cy a
... | tri≈ ¬a b ¬c = tri≈ (λ lt → <-irr (case1 (sym fc10)) lt) fc10 (λ lt → <-irr (case1 fc10) lt) where
      fc10 : * x ≡ * y
      fc10 = fcn-inject {A} s {x} {y} {f} mf cx cy b
... | tri> ¬a ¬b c = tri> (λ lt → <-irr (case2 fc12) lt) (λ eq → <-irr (case1 eq) fc12) fc12  where 
      fc12 : * y < * x
      fc12 = fcn-< {A} s {y} {x} {f} mf cy cx c

-- open import Relation.Binary.Properties.Poset as Poset

IsTotalOrderSet : ( A : HOD ) → Set (Level.suc n)
IsTotalOrderSet A = {a b : HOD} → odef A (& a) → odef A (& b)  → Tri (a < b) (a ≡ b) (b < a )

      
record Maximal ( A : HOD )  : Set (Level.suc n) where
   field
      maximal : HOD
      A∋maximal : A ∋ maximal
      ¬maximal<x : {x : HOD} → A ∋ x  → ¬ maximal < x       -- A is Partial, use negative

--
-- inductive maxmum tree from x
-- tree structure
--

record Prev< (A B : HOD) {x : Ordinal } (xa : odef A x)  ( f : Ordinal → Ordinal )  : Set n where
   field
      y : Ordinal
      ay : odef B y
      x=fy :  x ≡ f y 

record SUP ( A B : HOD )  : Set (Level.suc n) where
   field
      sup : HOD
      A∋maximal : A ∋ sup
      x<sup : {x : HOD} → B ∋ x → (x ≡ sup ) ∨ (x < sup )   -- B is Total, use positive

SupCond : ( A B : HOD) → (B⊆A : B ⊆ A) → IsTotalOrderSet B → Set (Level.suc n)
SupCond A B _ _ = SUP A B  

record ZChain ( A : HOD )  {x : Ordinal} (ax : odef A x) ( f : Ordinal → Ordinal ) (mf : ≤-monotonic-f A f )
                 (sup : (C : Ordinal ) → (* C ⊆ A) → IsTotalOrderSet (* C) → Ordinal) ( z : Ordinal ) : Set (Level.suc n) where
   field
      chain : HOD
      chain⊆A : chain ⊆ A
      chain∋x : odef chain x
      initial : {y : Ordinal } → odef chain y → * x < * y
      f-total : IsTotalOrderSet chain 
      f-next : {a : Ordinal } → odef chain a → odef chain (f a)
      f-immediate : { x y : Ordinal } → odef chain x → odef chain y → ¬ ( ( * x < * y ) ∧ ( * y < * (f x )) )
      is-max :  {a b : Ordinal } → (ca : odef chain a ) →  b o< z  → (ba : odef A b) 
          → Prev< A chain ba f
               ∨  (sup (& chain) (subst (λ k → k  ⊆ A) (sym *iso) chain⊆A)  (subst (λ k → IsTotalOrderSet k) (sym *iso) f-total) ≡ b )
          → * a < * b  → odef chain b

Zorn-lemma : { A : HOD } 
    → o∅ o< & A 
    → ( ( B : HOD) → (B⊆A : B ⊆ A) → IsTotalOrderSet B → SUP A B   ) -- SUP condition
    → Maximal A 
Zorn-lemma {A}  0<A supP = zorn00 where
     supO : (C : Ordinal ) → (* C) ⊆ A → IsTotalOrderSet (* C) → Ordinal
     supO C C⊆A TC = & ( SUP.sup ( supP (* C)  C⊆A TC ))
     z01 : {a b : HOD} → A ∋ a → A ∋ b  → (a ≡ b ) ∨ (a < b ) → b < a → ⊥
     z01 {a} {b} A∋a A∋b = <-irr
     z07 :   {y : Ordinal} → {P : Set n} → odef A y ∧ P → y o< & A
     z07 {y} p = subst (λ k → k o< & A) &iso ( c<→o< (subst (λ k → odef A k ) (sym &iso ) (proj1 p )))
     s : HOD
     s = ODC.minimal O A (λ eq → ¬x<0 ( subst (λ k → o∅ o< k ) (=od∅→≡o∅ eq) 0<A )) 
     sa : A ∋ * ( & s  )
     sa =  subst (λ k → odef A (& k) ) (sym *iso) ( ODC.x∋minimal O A (λ eq → ¬x<0 ( subst (λ k → o∅ o< k ) (=od∅→≡o∅ eq) 0<A ))  )
     s<A : & s o< & A
     s<A = c<→o< (subst (λ k → odef A (& k) ) *iso sa )
     HasMaximal : HOD
     HasMaximal = record { od = record { def = λ x → odef A x ∧ ( (m : Ordinal) →  odef A m → ¬ (* x < * m)) }  ; odmax = & A ; <odmax = z07 } 
     no-maximum : HasMaximal =h= od∅ → (x : Ordinal) → odef A x ∧ ((m : Ordinal) →  odef A m →  odef A x ∧ (¬ (* x < * m) )) →  ⊥
     no-maximum nomx x P = ¬x<0 (eq→ nomx {x} ⟪ proj1 P , (λ m ma p → proj2 ( proj2 P m ma ) p ) ⟫ )  
     Gtx : { x : HOD} → A ∋ x → HOD
     Gtx {x} ax = record { od = record { def = λ y → odef A y ∧ (x < (* y)) } ; odmax = & A ; <odmax = z07 } 
     z08  : ¬ Maximal A →  HasMaximal =h= od∅
     z08 nmx  = record { eq→  = λ {x} lt → ⊥-elim ( nmx record {maximal = * x ; A∋maximal = subst (λ k → odef A k) (sym &iso) (proj1 lt)
         ; ¬maximal<x = λ {y} ay → subst (λ k → ¬ (* x < k)) *iso (proj2 lt (& y) ay) } ) ; eq← =  λ {y} lt → ⊥-elim ( ¬x<0 lt )}
     x-is-maximal : ¬ Maximal A → {x : Ordinal} → (ax : odef A x) → & (Gtx (subst (λ k → odef A k ) (sym &iso) ax)) ≡ o∅ → (m : Ordinal) → odef A m → odef A x ∧ (¬ (* x < * m))
     x-is-maximal nmx {x} ax nogt m am  = ⟪ subst (λ k → odef A k) &iso (subst (λ k → odef A k ) (sym &iso) ax) ,  ¬x<m  ⟫ where
        ¬x<m :  ¬ (* x < * m)
        ¬x<m x<m = ∅< {Gtx (subst (λ k → odef A k ) (sym &iso) ax)} {* m} ⟪ subst (λ k → odef A k) (sym &iso) am , subst (λ k → * x < k ) (cong (*) (sym &iso)) x<m ⟫  (≡o∅→=od∅ nogt) 

     -- Uncountable ascending chain by axiom of choice
     cf : ¬ Maximal A → Ordinal → Ordinal
     cf  nmx x with ODC.∋-p O A (* x)
     ... | no _ = o∅
     ... | yes ax with is-o∅ (& ( Gtx ax ))
     ... | yes nogt = -- no larger element, so it is maximal
         ⊥-elim (no-maximum (z08 nmx) x ⟪ subst (λ k → odef A k) &iso ax , x-is-maximal nmx (subst (λ k → odef A k ) &iso ax) nogt ⟫ )
     ... | no not =  & (ODC.minimal O (Gtx ax) (λ eq → not (=od∅→≡o∅ eq)))
     is-cf : (nmx : ¬ Maximal A ) → {x : Ordinal} → odef A x → odef A (cf nmx x) ∧ ( * x < * (cf nmx x) )
     is-cf nmx {x} ax with ODC.∋-p O A (* x)
     ... | no not = ⊥-elim ( not (subst (λ k → odef A k ) (sym &iso) ax ))
     ... | yes ax with is-o∅ (& ( Gtx ax ))
     ... | yes nogt = ⊥-elim (no-maximum (z08 nmx) x ⟪ subst (λ k → odef A k) &iso ax , x-is-maximal nmx (subst (λ k → odef A k ) &iso ax) nogt ⟫ )
     ... | no not = ODC.x∋minimal O (Gtx ax) (λ eq → not (=od∅→≡o∅ eq))
     cf-is-<-monotonic : (nmx : ¬ Maximal A ) → (x : Ordinal) →  odef A x → ( * x < * (cf nmx x) ) ∧  odef A (cf nmx x )
     cf-is-<-monotonic nmx x ax = ⟪ proj2 (is-cf nmx ax ) , proj1 (is-cf nmx ax ) ⟫
     cf-is-≤-monotonic : (nmx : ¬ Maximal A ) →  ≤-monotonic-f A ( cf nmx )
     cf-is-≤-monotonic nmx x ax = ⟪ case2 (proj1 ( cf-is-<-monotonic nmx x ax  ))  , proj2 ( cf-is-<-monotonic nmx x ax  ) ⟫

     zsup :  ( f : Ordinal → Ordinal ) → (mf : ≤-monotonic-f A f) →  (zc : ZChain A sa f mf supO (& A) ) → SUP A  (ZChain.chain zc) 
     zsup f mf zc = supP (ZChain.chain zc) (ZChain.chain⊆A zc) ( ZChain.f-total zc  )   
     A∋zsup :  (nmx : ¬ Maximal A ) (zc : ZChain A sa (cf nmx) (cf-is-≤-monotonic nmx) supO (& A) ) 
        →  A ∋ * ( & ( SUP.sup (zsup (cf nmx) (cf-is-≤-monotonic nmx) zc ) ))
     A∋zsup nmx zc = subst (λ k → odef A (& k )) (sym *iso) ( SUP.A∋maximal  (zsup (cf nmx) (cf-is-≤-monotonic nmx) zc ) )
     sp0 : ( f : Ordinal → Ordinal ) → (mf : ≤-monotonic-f A f ) (zc : ZChain A (subst (λ k → odef A k ) &iso sa ) f mf supO (& A) ) → SUP A (* (& (ZChain.chain zc)))
     sp0 f mf zc = supP (* (& (ZChain.chain zc))) (subst (λ k → k ⊆ A) (sym *iso) (ZChain.chain⊆A zc))
               (subst (λ k → IsTotalOrderSet k) (sym *iso) (ZChain.f-total zc) )
     zc< : {x y z : Ordinal} → {P : Set n} → (x o< y → P) → x o< z → z o< y → P
     zc< {x} {y} {z} {P} prev x<z z<y = prev (ordtrans x<z z<y)

     ---
     --- the maximum chain  has fix point of any ≤-monotonic function
     ---
     z03 :  ( f : Ordinal → Ordinal ) → (mf : ≤-monotonic-f A f ) (zc : ZChain A (subst (λ k → odef A k ) &iso sa ) f mf supO (& A) )
            → f (& (SUP.sup (sp0 f mf zc ))) ≡ & (SUP.sup (sp0 f mf zc ))
     z03 f mf zc = z14 where
           chain = ZChain.chain zc
           sp1 = sp0 f mf zc
           z10 :  {a b : Ordinal } → (ca : odef chain a ) → b o< & A → (ab : odef A b ) 
              →  Prev< A chain ab f
                   ∨  (supO (& chain) (subst (λ k → k  ⊆ A) (sym *iso) (ZChain.chain⊆A zc))  (subst (λ k → IsTotalOrderSet k) (sym *iso) (ZChain.f-total zc)) ≡ b )
              → * a < * b  → odef chain b
           z10 = ZChain.is-max zc
           z11 : & (SUP.sup sp1) o< & A
           z11 = c<→o< ( SUP.A∋maximal sp1)
           z12 : odef chain (& (SUP.sup sp1))
           z12 with o≡? (& s) (& (SUP.sup sp1))
           ... | yes eq = subst (λ k → odef chain k) eq ( ZChain.chain∋x zc )
           ... | no ne = z10 {& s} {& (SUP.sup sp1)} ( ZChain.chain∋x zc ) z11 (SUP.A∋maximal sp1)  (case2 refl ) z13 where
               z13 :  * (& s) < * (& (SUP.sup sp1))
               z13 with SUP.x<sup sp1 (subst (λ k → odef k (& s)) (sym *iso) ( ZChain.chain∋x zc ))
               ... | case1 eq = ⊥-elim ( ne (cong (&) eq) )
               ... | case2 lt = subst₂ (λ j k → j < k ) (sym *iso) (sym *iso) lt
           z14 :  f (& (SUP.sup (sp0 f mf zc))) ≡ & (SUP.sup (sp0 f mf zc))
           z14 with ZChain.f-total zc  (subst (λ k → odef chain k) (sym &iso)  (ZChain.f-next zc z12 )) z12 
           ... | tri< a ¬b ¬c = ⊥-elim z16 where
               z16 : ⊥
               z16 with proj1 (mf (& ( SUP.sup sp1)) ( SUP.A∋maximal sp1 ))
               ... | case1 eq = ⊥-elim (¬b (subst₂ (λ j k → j ≡ k ) refl *iso (sym eq) ))
               ... | case2 lt = ⊥-elim (¬c (subst₂ (λ j k → k < j ) refl *iso lt ))
           ... | tri≈ ¬a b ¬c = subst ( λ k → k ≡ & (SUP.sup sp1) ) &iso ( cong (&) b )
           ... | tri> ¬a ¬b c = ⊥-elim z17 where
               z15 : (* (f ( & ( SUP.sup sp1 ))) ≡ SUP.sup sp1) ∨ (* (f ( & ( SUP.sup sp1 ))) <  SUP.sup sp1)
               z15  = SUP.x<sup sp1 (subst₂ (λ j k → odef j k ) (sym *iso) (sym &iso)  (ZChain.f-next zc z12 ))
               z17 : ⊥
               z17 with z15
               ... | case1 eq = ¬b eq
               ... | case2 lt = ¬a lt

     -- ZChain contradicts ¬ Maximal
     --
     -- ZChain forces fix point on any ≤-monotonic function (z03)
     -- ¬ Maximal create cf which is a <-monotonic function by axiom of choice. This contradicts fix point of ZChain
     --
     z04 :  (nmx : ¬ Maximal A ) → (zc : ZChain A (subst (λ k → odef A k ) &iso sa ) (cf nmx) (cf-is-≤-monotonic nmx) supO (& A)) → ⊥
     z04 nmx zc = z01  {* (cf nmx c)} {* c} (subst (λ k → odef A k ) (sym &iso)
           (proj1 (is-cf nmx (SUP.A∋maximal  sp1))))
           (subst (λ k → odef A (& k)) (sym *iso) (SUP.A∋maximal sp1) ) (case1 ( cong (*)( z03 (cf nmx) (cf-is-≤-monotonic nmx ) zc )))
           (proj1 (cf-is-<-monotonic nmx c (SUP.A∋maximal sp1))) where
          sp1 = sp0 (cf nmx) (cf-is-≤-monotonic nmx) zc
          c = & (SUP.sup sp1)

     --
     -- create all ZChains under o< x
     --
     ind : ( f : Ordinal → Ordinal ) → (mf : ≤-monotonic-f A f ) → (x : Ordinal) →
            ((z : Ordinal) → z o< x → {y : Ordinal} → (ya : odef A y) → ZChain A ya f mf supO z ) → { y : Ordinal } → (ya : odef A y) → ZChain A ya f mf supO x
     ind f mf x prev {y} ay with Oprev-p x
     ... | yes op = zc4 where
          --
          -- we have previous ordinal to use induction
          --
          px = Oprev.oprev op
          zc0 : ZChain A ay f mf supO (Oprev.oprev op)
          zc0 = prev px (subst (λ k → px o< k) (Oprev.oprev=x op) <-osuc ) ay
          zc4 : ZChain A ay f mf supO x 
          zc4 with ODC.∋-p O A (* px)
          ... | no noapx =  -- ¬ A ∋ px, just skip
                 record { chain = ZChain.chain zc0 ; chain⊆A = ZChain.chain⊆A zc0 ; initial = ZChain.initial zc0 
                     ; f-total = ZChain.f-total zc0 ; f-next =  ZChain.f-next zc0
                     ; f-immediate =  ZChain.f-immediate zc0 ; chain∋x  = ZChain.chain∋x zc0 ; is-max = zc11 }  where -- no extention
                zc11 : {a b : Ordinal} → odef (ZChain.chain zc0) a → b o< x → (ba : odef A b) →
                    Prev< A (ZChain.chain zc0) ba f ∨ (& (SUP.sup (supP (* (& (ZChain.chain zc0)))
                       (subst (λ k → k ⊆ A) (sym *iso) (ZChain.chain⊆A zc0))
                       (subst IsTotalOrderSet (sym *iso) (ZChain.f-total zc0)))) ≡ b) →
                            * a < * b → odef (ZChain.chain zc0) b
                zc11 {a} {b} za b<x ba P a<b with osuc-≡< (subst (λ k → b o< k) (sym (Oprev.oprev=x op)) b<x) 
                ... | case1 eq = ⊥-elim ( noapx (subst (λ k → odef A k) (trans eq (sym &iso) ) ba ))
                ... | case2 lt = ZChain.is-max zc0 za lt ba P a<b
          ... | yes apx with ODC.p∨¬p O ( Prev< A (ZChain.chain zc0) apx f )   -- we have to check adding x preserve is-max ZChain A ay f mf supO px
          ... | case1 pr = zc9 where -- we have previous A ∋ z < x , f z ≡ x, so chain ∋ f z ≡ x because of f-next
                chain = ZChain.chain zc0
                zc17 :  {a b : Ordinal} → odef (ZChain.chain zc0) a → b o< x → (ba : odef A b) →
                            Prev< A (ZChain.chain zc0) ba f ∨ (supO (& (ZChain.chain zc0))
                             (subst (λ k → k ⊆ A) (sym *iso) (ZChain.chain⊆A zc0))
                             (subst IsTotalOrderSet (sym *iso) (ZChain.f-total zc0)) ≡ b) →
                            * a < * b → odef (ZChain.chain zc0) b
                zc17 {a} {b} za b<x ba P a<b with osuc-≡< (subst (λ k → b o< k) (sym (Oprev.oprev=x op)) b<x) 
                ... | case2 lt = ZChain.is-max zc0 za lt ba P a<b
                ... | case1 b=px = subst (λ k → odef chain k ) (trans (sym (Prev<.x=fy pr )) (trans &iso (sym b=px))) ( ZChain.f-next zc0 (Prev<.ay pr))
                zc9 :  ZChain A ay f mf supO x
                zc9 = record { chain = ZChain.chain zc0 ; chain⊆A = ZChain.chain⊆A zc0 ; f-total = ZChain.f-total zc0 ; f-next =  ZChain.f-next zc0
                     ; initial = ZChain.initial zc0 ; f-immediate =  ZChain.f-immediate zc0 ; chain∋x  = ZChain.chain∋x zc0 ; is-max = zc17 }  -- no extention
          ... | case2 ¬fy<x with ODC.p∨¬p O ( x ≡ & ( SUP.sup ( supP ( ZChain.chain zc0 ) (ZChain.chain⊆A zc0 ) (ZChain.f-total zc0) ) ))
          ... | case1 x=sup = -- previous ordinal is a sup of a smaller ZChain
                 record { chain = schain ; chain⊆A = {!!} ; f-total = {!!} ; f-next =  {!!}
                     ; initial = {!!} ; f-immediate =  {!!} ; chain∋x  = case1 (ZChain.chain∋x zc0) ; is-max = {!!} } where -- x is sup
                sp = SUP.sup ( supP ( ZChain.chain zc0 ) (ZChain.chain⊆A zc0 ) (ZChain.f-total zc0) ) 
                chain = ZChain.chain zc0
                schain : HOD
                schain = record { od = record { def = λ x → odef chain x ∨ (FClosure A f (& sp) x) } ; odmax = & A ; <odmax = {!!} }
          ... | case2 ¬x=sup =  -- x is not f y' nor sup of former ZChain from y
                   record { chain = ZChain.chain zc0 ; chain⊆A = ZChain.chain⊆A zc0 ; f-total = ZChain.f-total zc0 ; f-next = ZChain.f-next zc0
                     ; initial = ZChain.initial zc0 ; f-immediate = ZChain.f-immediate zc0 ; chain∋x  =  ZChain.chain∋x zc0 ; is-max = {!!} }  where -- no extention
                z18 :  {a b : Ordinal} → odef (ZChain.chain zc0) a → b o< x → (ba : odef A b) →
                            Prev< A (ZChain.chain zc0) ba f ∨ (& (SUP.sup (supP (* (& (ZChain.chain zc0)))
                               (subst (λ k → k ⊆ A) (sym *iso) (ZChain.chain⊆A zc0))
                               (subst IsTotalOrderSet (sym *iso) (ZChain.f-total zc0))))
                             ≡ b) →
                            * a < * b → odef (ZChain.chain zc0) b
                z18 {a} {b} za b<x ba (case1 p) a<b = {!!}
                z18 {a} {b} za b<x ba (case2 p) a<b = {!!}
     ... | no ¬ox =  {!!}  where --- limit ordinal case
         record UZFChain (z : Ordinal) : Set n where -- Union of ZFChain from y which has maximality o< x
            field
               u : Ordinal
               u<x : u o< x
               zuy : odef (ZChain.chain (prev u u<x {y} ay )) z
         Uz : HOD
         Uz = record { od = record { def = λ y → UZFChain y } ; odmax = & A ; <odmax = {!!} }
         u-total : IsTotalOrderSet Uz
         u-total {x} {y} ux uy = {!!}
         --- ux ⊆ uy ∨ uy ⊆ ux
         
     zorn00 : Maximal A 
     zorn00 with is-o∅ ( & HasMaximal )  -- we have no Level (suc n) LEM 
     ... | no not = record { maximal = ODC.minimal O HasMaximal  (λ eq → not (=od∅→≡o∅ eq)) ; A∋maximal = zorn01 ; ¬maximal<x  = zorn02 } where
         -- yes we have the maximal
         zorn03 :  odef HasMaximal ( & ( ODC.minimal O HasMaximal  (λ eq → not (=od∅→≡o∅ eq)) ) )
         zorn03 =  ODC.x∋minimal  O HasMaximal  (λ eq → not (=od∅→≡o∅ eq))
         zorn01 :  A ∋ ODC.minimal O HasMaximal (λ eq → not (=od∅→≡o∅ eq))
         zorn01  = proj1  zorn03  
         zorn02 : {x : HOD} → A ∋ x → ¬ (ODC.minimal O HasMaximal (λ eq → not (=od∅→≡o∅ eq)) < x)
         zorn02 {x} ax m<x = proj2 zorn03 (& x) ax (subst₂ (λ j k → j < k) (sym *iso) (sym *iso) m<x )
     ... | yes ¬Maximal = ⊥-elim ( z04 nmx zorn04) where
         -- if we have no maximal, make ZChain, which contradict SUP condition
         nmx : ¬ Maximal A 
         nmx mx =  ∅< {HasMaximal} zc5 ( ≡o∅→=od∅  ¬Maximal ) where
              zc5 : odef A (& (Maximal.maximal mx)) ∧ (( y : Ordinal ) →  odef A y → ¬ (* (& (Maximal.maximal mx)) < * y)) 
              zc5 = ⟪  Maximal.A∋maximal mx , (λ y ay mx<y → Maximal.¬maximal<x mx (subst (λ k → odef A k ) (sym &iso) ay) (subst (λ k → k < * y) *iso mx<y) ) ⟫
         zorn03 : ( f : Ordinal → Ordinal ) → (mf : ≤-monotonic-f A f ) → (ya : odef A (& s)) → ZChain A ya f mf supO (& A)
         zorn03 f mf = TransFinite {λ z → {y : Ordinal } → (ya : odef A y ) → ZChain A ya f mf supO z } (ind f mf) (& A)
         zorn04 : ZChain A (subst (λ k → odef A k ) &iso sa ) (cf nmx) (cf-is-≤-monotonic nmx) supO (& A)
         zorn04 = zorn03 (cf nmx) (cf-is-≤-monotonic nmx) (subst (λ k → odef A k ) &iso sa )

-- usage (see filter.agda )
--
-- _⊆'_ : ( A B : HOD ) → Set n
-- _⊆'_ A B = (x : Ordinal ) → odef A x → odef B x

-- MaximumSubset : {L P : HOD} 
--        → o∅ o< & L →  o∅ o< & P → P ⊆ L
--        → IsPartialOrderSet P _⊆'_
--        → ( (B : HOD) → B ⊆ P → IsTotalOrderSet B _⊆'_ → SUP P B _⊆'_ )
--        → Maximal P (_⊆'_)
-- MaximumSubset {L} {P} 0<L 0<P P⊆L PO SP  = Zorn-lemma {P} {_⊆'_} 0<P PO SP
