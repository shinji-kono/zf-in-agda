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

_<<_ : (x y : Ordinal ) → Set n    -- Set n order
x << y = * x < * y

POO : IsStrictPartialOrder _≡_ _<<_ 
POO = record { isEquivalence = record { refl = refl ; sym = sym ; trans = trans } 
   ; trans = IsStrictPartialOrder.trans PO 
   ; irrefl = λ x=y x<y → IsStrictPartialOrder.irrefl PO (cong (*) x=y) x<y
   ; <-resp-≈ =  record { fst = λ {x} {y} {y1} y=y1 xy1 → subst (λ k → x << k ) y=y1 xy1 ; snd = λ {x} {x1} {y} x=x1 x1y → subst (λ k → k << x ) x=x1 x1y } } 
 
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

ptrans =  IsStrictPartialOrder.trans PO

open _==_
open _⊆_

--
-- Closure of ≤-monotonic function f has total order
--

≤-monotonic-f : (A : HOD) → ( Ordinal → Ordinal ) → Set (Level.suc n)
≤-monotonic-f A f = (x : Ordinal ) → odef A x → ( * x ≤ * (f x) ) ∧  odef A (f x )

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
     fc00 zero zero refl (init as) (fsuc y cy) i=x i=y with proj1 (mf y (A∋fc s f mf cy ) )
     ... | case1 y=fy = subst (λ k → * s ≡ k ) y=fy ( fc00 zero zero refl (init as) cy i=x i=y )
     fc00 zero zero refl (fsuc x cx) (init as) i=x i=y with proj1 (mf x (A∋fc s f mf cx ) )
     ... | case1 x=fx = subst (λ k → k ≡ * s ) x=fx ( fc00 zero zero refl cx (init as) i=x i=y )
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


fcn-imm : {A : HOD} (s : Ordinal) { x y : Ordinal } (f : Ordinal → Ordinal) (mf : ≤-monotonic-f A f) 
    → (cx : FClosure A f s x) → (cy : FClosure A f s y ) → ¬ ( ( * x < * y ) ∧ ( * y < * (f x )) ) 
fcn-imm {A} s {x} {y} f mf cx cy ⟪ x<y , y<fx ⟫ = fc21 where
      fc20 : fcn s mf cy Data.Nat.< suc (fcn s mf cx) → (fcn s mf cy ≡ fcn s mf cx) ∨ ( fcn s mf cy Data.Nat.< fcn s mf cx )
      fc20 y<sx with <-cmp ( fcn s mf cy ) (fcn s mf cx )
      ... | tri< a ¬b ¬c = case2 a
      ... | tri≈ ¬a b ¬c = case1 b
      ... | tri> ¬a ¬b c = ⊥-elim ( nat-≤> y<sx (s≤s c))
      fc17 : {x y : Ordinal } → (cx : FClosure A f s x) → (cy : FClosure A f s y ) → suc (fcn s mf cx) ≡ fcn s mf cy → * (f x ) ≡ * y
      fc17 {x} {y} cx cy sx=y = fc18 (fcn s mf cy) cx cy refl sx=y  where
          fc18 : (i : ℕ ) → {y : Ordinal } → (cx : FClosure A f s x ) (cy : FClosure A f s y ) → (i ≡ fcn s mf cy ) → suc (fcn s mf cx) ≡  i → * (f x) ≡ * y
          fc18 (suc i) {y} cx (fsuc y1 cy)  i=y sx=i with proj1 (mf y1 (A∋fc s f mf cy ) )
          ... | case1 y=fy = subst (λ k → * (f x) ≡  k ) y=fy ( fc18 (suc i) {y1} cx cy i=y sx=i)  -- dereference
          ... | case2 y<fy = subst₂ (λ j k → * (f j) ≡ * (f k) ) &iso &iso (cong (λ k → * (f (& k) ) ) fc19) where
               fc19 : * x ≡ * y1
               fc19 = fcn-inject s mf cx cy (cong pred ( trans sx=i i=y ))
      fc21 :  ⊥
      fc21 with <-cmp (suc ( fcn s mf cx )) (fcn s mf cy )
      ... | tri< a ¬b ¬c = <-irr (case2 y<fx) (fc22 a) where -- suc ncx < ncy
           cxx :  FClosure A f s (f x)
           cxx = fsuc x cx 
           fc16 : (x : Ordinal ) → (cx : FClosure A f s x) → (fcn s mf cx  ≡ fcn s mf (fsuc x cx)) ∨ ( suc (fcn s mf cx ) ≡ fcn s mf (fsuc x cx))
           fc16 x (init as) with proj1 (mf s as )
           ... | case1 _ = case1 refl
           ... | case2 _ = case2 refl
           fc16 .(f x) (fsuc x cx ) with proj1 (mf (f x) (A∋fc s f mf (fsuc x cx)) )
           ... | case1 _ = case1 refl 
           ... | case2 _ = case2 refl
           fc22 : (suc ( fcn s mf cx ))  Data.Nat.< (fcn s mf cy ) → * (f x) < * y
           fc22 a with fc16 x cx
           ... | case1 eq = fcn-< s mf cxx cy (subst (λ k → k Data.Nat.< fcn s mf cy ) eq (<-trans a<sa a))
           ... | case2 eq = fcn-< s mf cxx cy (subst (λ k → k Data.Nat.< fcn s mf cy ) eq a )
      ... | tri≈ ¬a b ¬c = <-irr (case1 (fc17 cx cy b)) y<fx
      ... | tri> ¬a ¬b c with fc20 c -- ncy < suc ncx
      ... | case1 y=x = <-irr (case1 ( fcn-inject s mf cy cx  y=x ))  x<y
      ... | case2 y<x = <-irr (case2 x<y) (fcn-< s mf cy cx y<x ) 

-- open import Relation.Binary.Properties.Poset as Poset

IsTotalOrderSet : ( A : HOD ) → Set (Level.suc n)
IsTotalOrderSet A = {a b : HOD} → odef A (& a) → odef A (& b)  → Tri (a < b) (a ≡ b) (b < a )

⊆-IsTotalOrderSet : { A B : HOD } →  B ⊆ A  → IsTotalOrderSet A → IsTotalOrderSet B
⊆-IsTotalOrderSet {A} {B} B⊆A T  ax ay = T (incl B⊆A ax) (incl B⊆A ay)

_⊆'_ : ( A B : HOD ) → Set n
_⊆'_ A B = {x : Ordinal } → odef A x → odef B x

--
-- inductive maxmum tree from x
-- tree structure
--

record HasPrev (A B : HOD) {x : Ordinal } (xa : odef A x)  ( f : Ordinal → Ordinal )  : Set n where
   field
      y : Ordinal
      ay : odef B y
      x=fy :  x ≡ f y 

record IsSup (A B : HOD) {x : Ordinal } (xa : odef A x)     : Set n where
   field
      x<sup : {y : Ordinal} → odef B y → (y ≡ x ) ∨ (y << x )

record ZChain ( A : HOD )  (x : Ordinal)  ( f : Ordinal → Ordinal ) ( z : Ordinal ) : Set (Level.suc n) where
   field
      supf : Ordinal → HOD
   chain : HOD
   chain = supf z 
   field
      chain⊆A : chain ⊆' A
      chain∋x : odef chain x
      initial : {y : Ordinal } → odef chain y → * x ≤ * y
      f-next : {a : Ordinal } → odef chain a → odef chain (f a)
      is-max :  {a b : Ordinal } → (ca : odef chain a ) →  b o< osuc z  → (ab : odef A b) 
          → HasPrev A chain ab f ∨  IsSup A chain ab  
          → * a < * b  → odef chain b

--      chain-mono : {x y : Ordinal} → x o≤ y → y o≤ z →  supf x ⊆' supf y 
--      f-total : {x y : Ordinal} → x o≤ z → IsTotalOrderSet (supf x) 

ZChainSupUnique : ( A : HOD )  (x : Ordinal)  ( f : Ordinal → Ordinal ) (mf : ≤-monotonic-f A f ) ( a b : Ordinal )
   → ( za : ZChain A x f a ) → (zb : ZChain A x f b ) → {i : Ordinal } → a o< b → i o≤ a → ZChain.supf za i ≡ ZChain.supf zb i
ZChainSupUnique = {!!}

record Maximal ( A : HOD )  : Set (Level.suc n) where
   field
      maximal : HOD
      A∋maximal : A ∋ maximal
      ¬maximal<x : {x : HOD} → A ∋ x  → ¬ maximal < x       -- A is Partial, use negative

record SUP ( A B : HOD )  : Set (Level.suc n) where
   field
      sup : HOD
      A∋maximal : A ∋ sup
      x<sup : {x : HOD} → B ∋ x → (x ≡ sup ) ∨ (x < sup )   -- B is Total, use positive

SupCond : ( A B : HOD) → (B⊆A : B ⊆ A) → IsTotalOrderSet B → Set (Level.suc n)
SupCond A B _ _ = SUP A B  

Zorn-lemma : { A : HOD } 
    → o∅ o< & A 
    → ( ( B : HOD) → (B⊆A : B ⊆' A) → IsTotalOrderSet B → SUP A B   ) -- SUP condition
    → Maximal A 
Zorn-lemma {A}  0<A supP = zorn00 where
     supO : (C : HOD ) → C ⊆' A → IsTotalOrderSet C → Ordinal
     supO C C⊆A TC = & ( SUP.sup ( supP  C  C⊆A TC ))
     <-irr0 : {a b : HOD} → A ∋ a → A ∋ b  → (a ≡ b ) ∨ (a < b ) → b < a → ⊥
     <-irr0 {a} {b} A∋a A∋b = <-irr
     z07 :   {y : Ordinal} → {P : Set n} → odef A y ∧ P → y o< & A
     z07 {y} p = subst (λ k → k o< & A) &iso ( c<→o< (subst (λ k → odef A k ) (sym &iso ) (proj1 p )))
     s : HOD
     s = ODC.minimal O A (λ eq → ¬x<0 ( subst (λ k → o∅ o< k ) (=od∅→≡o∅ eq) 0<A )) 
     as : A ∋ * ( & s  )
     as =  subst (λ k → odef A (& k) ) (sym *iso) ( ODC.x∋minimal O A (λ eq → ¬x<0 ( subst (λ k → o∅ o< k ) (=od∅→≡o∅ eq) 0<A ))  )
     as0 : odef A  (& s  )
     as0 =  subst (λ k → odef A k ) &iso as
     s<A : & s o< & A
     s<A = c<→o< (subst (λ k → odef A (& k) ) *iso as )
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

     ---
     --- infintie ascention sequence of f
     ---
     cf-is-<-monotonic : (nmx : ¬ Maximal A ) → (x : Ordinal) →  odef A x → ( * x < * (cf nmx x) ) ∧  odef A (cf nmx x )
     cf-is-<-monotonic nmx x ax = ⟪ proj2 (is-cf nmx ax ) , proj1 (is-cf nmx ax ) ⟫
     cf-is-≤-monotonic : (nmx : ¬ Maximal A ) →  ≤-monotonic-f A ( cf nmx )
     cf-is-≤-monotonic nmx x ax = ⟪ case2 (proj1 ( cf-is-<-monotonic nmx x ax  ))  , proj2 ( cf-is-<-monotonic nmx x ax  ) ⟫

     zsup :  ( f : Ordinal → Ordinal ) → (mf : ≤-monotonic-f A f) →  (zc : ZChain A (& s) f (& A) ) → SUP A  (ZChain.chain zc) 
     zsup f mf zc = supP (ZChain.chain zc) (ZChain.chain⊆A zc) {!!}   
     A∋zsup : (nmx : ¬ Maximal A ) (zc : ZChain A (& s) (cf nmx)  (& A) ) 
        →  A ∋ * ( & ( SUP.sup (zsup (cf nmx) (cf-is-≤-monotonic nmx) zc )))
     A∋zsup nmx zc = subst (λ k → odef A (& k )) (sym *iso) ( SUP.A∋maximal  (zsup (cf nmx) (cf-is-≤-monotonic nmx) zc ) )
     sp0 : ( f : Ordinal → Ordinal ) → (mf : ≤-monotonic-f A f ) (zc : ZChain A (& s) f  (& A) ) → SUP A (ZChain.chain zc)
     sp0 f mf zc = supP (ZChain.chain zc) (ZChain.chain⊆A zc) {!!}   
     zc< : {x y z : Ordinal} → {P : Set n} → (x o< y → P) → x o< z → z o< y → P
     zc< {x} {y} {z} {P} prev x<z z<y = prev (ordtrans x<z z<y)

     ---
     --- the maximum chain  has fix point of any ≤-monotonic function
     ---
     fixpoint :  ( f : Ordinal → Ordinal ) → (mf : ≤-monotonic-f A f ) (zc : ZChain A (& s) f  (& A) )
            → ( {x y : Ordinal} → x o≤ (& A) → IsTotalOrderSet (ZChain.chain zc) )
            → f (& (SUP.sup (sp0 f mf zc ))) ≡ & (SUP.sup (sp0 f mf zc ))
     fixpoint f mf zc total = z14 where
           chain = ZChain.chain zc
           sp1 = sp0 f mf zc
           z10 :  {a b : Ordinal } → (ca : odef chain a ) → b o< osuc (& A) → (ab : odef A b ) 
              →  HasPrev A chain ab f ∨  IsSup A chain {b} ab -- (supO  chain  (ZChain.chain⊆A zc) (ZChain.f-total zc) ≡ b )
              → * a < * b  → odef chain b
           z10 = ZChain.is-max zc
           z11 : & (SUP.sup sp1) o< & A
           z11 = c<→o< ( SUP.A∋maximal sp1)
           z12 : odef chain (& (SUP.sup sp1))
           z12 with o≡? (& s) (& (SUP.sup sp1))
           ... | yes eq = subst (λ k → odef chain k) eq ( ZChain.chain∋x zc )
           ... | no ne = z10 {& s} {& (SUP.sup sp1)} ( ZChain.chain∋x zc ) (ordtrans z11 <-osuc ) (SUP.A∋maximal sp1)
                (case2 z19 ) z13 where
               z13 :  * (& s) < * (& (SUP.sup sp1))
               z13 with SUP.x<sup sp1 ( ZChain.chain∋x zc )
               ... | case1 eq = ⊥-elim ( ne (cong (&) eq) )
               ... | case2 lt = subst₂ (λ j k → j < k ) (sym *iso) (sym *iso) lt
               z19 : IsSup A chain {& (SUP.sup sp1)} (SUP.A∋maximal sp1)
               z19 = record {   x<sup = z20 }  where
                   z20 :  {y : Ordinal} → odef chain y → (y ≡ & (SUP.sup sp1)) ∨ (y << & (SUP.sup sp1))
                   z20 {y} zy with SUP.x<sup sp1 (subst (λ k → odef chain k ) (sym &iso) zy)
                   ... | case1 y=p = case1 (subst (λ k → k ≡ _ ) &iso ( cong (&) y=p ))
                   ... | case2 y<p = case2 (subst (λ k → * y < k ) (sym *iso) y<p )
                   -- λ {y} zy → subst (λ k → (y ≡ & k ) ∨ (y << & k)) ?  (SUP.x<sup sp1 ? ) }
           z14 :  f (& (SUP.sup (sp0 f mf zc))) ≡ & (SUP.sup (sp0 f mf zc))
           z14 with total {& A} {& A} o≤-refl (subst (λ k → odef chain k) (sym &iso)  (ZChain.f-next zc z12 )) z12 
           ... | tri< a ¬b ¬c = ⊥-elim z16 where
               z16 : ⊥
               z16 with proj1 (mf (& ( SUP.sup sp1)) ( SUP.A∋maximal sp1 ))
               ... | case1 eq = ⊥-elim (¬b (subst₂ (λ j k → j ≡ k ) refl *iso (sym eq) ))
               ... | case2 lt = ⊥-elim (¬c (subst₂ (λ j k → k < j ) refl *iso lt ))
           ... | tri≈ ¬a b ¬c = subst ( λ k → k ≡ & (SUP.sup sp1) ) &iso ( cong (&) b )
           ... | tri> ¬a ¬b c = ⊥-elim z17 where
               z15 : (* (f ( & ( SUP.sup sp1 ))) ≡ SUP.sup sp1) ∨ (* (f ( & ( SUP.sup sp1 ))) <  SUP.sup sp1)
               z15  = SUP.x<sup sp1 (subst (λ k → odef chain k ) (sym &iso) (ZChain.f-next zc z12 ))
               z17 : ⊥
               z17 with z15
               ... | case1 eq = ¬b eq
               ... | case2 lt = ¬a lt

     -- ZChain contradicts ¬ Maximal
     --
     -- ZChain forces fix point on any ≤-monotonic function (fixpoint)
     -- ¬ Maximal create cf which is a <-monotonic function by axiom of choice. This contradicts fix point of ZChain
     --
     z04 :  (nmx : ¬ Maximal A ) → (zc : ZChain A (& s) (cf nmx) (& A)) → ({x y : Ordinal} → x o≤ & A → IsTotalOrderSet (ZChain.chain zc)) → ⊥
     z04 nmx zc total = <-irr0  {* (cf nmx c)} {* c} (subst (λ k → odef A k ) (sym &iso) (proj1 (is-cf nmx (SUP.A∋maximal  sp1))))
                                               (subst (λ k → odef A (& k)) (sym *iso) (SUP.A∋maximal sp1) )
           (case1 ( cong (*)( fixpoint (cf nmx) (cf-is-≤-monotonic nmx ) zc total ))) -- x ≡ f x ̄
           (proj1 (cf-is-<-monotonic nmx c (SUP.A∋maximal sp1))) where          -- x < f x
          sp1 = sp0 (cf nmx) (cf-is-≤-monotonic nmx) zc
          c = & (SUP.sup sp1)

     --
     -- create all ZChains under o< x
     --

     ys : {y : Ordinal} → (ay : odef A y)  (f : Ordinal → Ordinal ) → (mf : ≤-monotonic-f A f ) → HOD
     ys {y} ay f mf = record { od = record { def = λ x →  FClosure A f y x  } ; odmax = & A ; <odmax = {!!} }
     init-chain : {y x : Ordinal} → (ay : odef A y) (f : Ordinal → Ordinal ) → (mf : ≤-monotonic-f A f ) → x o< osuc y → ZChain A y f x
     init-chain {y} {x} ay f mf x≤y = record { chain⊆A = λ fx →  A∋fc y f mf fx
                     ; f-next = λ {x} sx → fsuc x sx  ; supf = λ _ → ys ay f mf 
                     ; initial = {!!} ; chain∋x  = init ay ; is-max = is-max } where
               i-total : IsTotalOrderSet (ys ay f mf )
               i-total fa fb = subst₂ (λ a b → Tri (a < b) (a ≡ b) (b < a ) ) *iso *iso (fcn-cmp y f mf fa fb)
               is-max : {a b : Ordinal} → odef (ys ay f mf) a →
                    b o< osuc x → (ab : odef A b) → HasPrev A (ys ay f mf) ab f ∨ IsSup A (ys ay f mf) ab →
                    * a < * b → odef (ys ay f mf) b
               is-max {a} {b} yca b≤x ab P a<b = {!!}
               initial : {i : Ordinal} → odef (ys ay f mf) i → * y ≤ * i
               initial {i} (init ai) = case1 refl
               initial .{f x} (fsuc x lt) = {!!}

     sind : ( f : Ordinal → Ordinal ) → (mf : ≤-monotonic-f A f ) {y : Ordinal} (ay : odef A y) → (x : Ordinal)
         → ((z : Ordinal) → z o< x → HOD ) → HOD
     sind f mf {y} ay x prev  with Oprev-p x
     ... | yes op = sc4 where
          px = Oprev.oprev op
          sc : HOD
          sc = prev px (subst (λ k → px o< k) (Oprev.oprev=x op) <-osuc ) 

          sc4 : HOD
          sc4 with ODC.∋-p O A (* x)
          ... | no noax = {!!}
          ... | yes ax with ODC.p∨¬p O ( HasPrev A sc ax f )   
          ... | case1 pr = sc
          ... | case2 ¬fy<x with ODC.p∨¬p O (IsSup A sc ax )
          ... | case1 is-sup =  schain where
                -- A∋sc -- x is a sup of zc 
                sup0 : SUP A sc 
                sup0 = record { sup = * x ; A∋maximal = ax ; x<sup = x21 } where
                        x21 :  {y : HOD} → sc ∋ y → (y ≡ * x) ∨ (y < * x)
                        x21 {y} zy with IsSup.x<sup is-sup zy 
                        ... | case1 y=x = case1 ( subst₂ (λ j k → j ≡ * k  ) *iso &iso ( cong (*) y=x)  )
                        ... | case2 y<x = case2 (subst₂ (λ j k → j < * k ) *iso &iso y<x  )
                sp : HOD
                sp = SUP.sup sup0 
                schain : HOD
                schain = record { od = record { def = λ x → odef sc x ∨ (FClosure A f (& sp) x) } ; odmax = & A ; <odmax = λ {y} sy → {!!}  }
          ... | case2 ¬x=sup =  sc
     ... | no ¬ox with trio< x y
     ... | tri< a ¬b ¬c = {!!}
     ... | tri≈ ¬a b ¬c = {!!}
     ... | tri> ¬a ¬b y<x = Uz where
         record Usup (z : Ordinal) : Set n where -- Union of supf from y which has maximality o< x
            field
               u : Ordinal
               u<x : u o< x
               chain∋z : odef (prev u u<x ) z
         Uz : HOD
         Uz = record { od = record { def = λ y → Usup y } ; odmax = & A
             ; <odmax = {!!} } -- λ lt → subst (λ k → k o< & A ) &iso (c<→o< (subst (λ k → odef A k ) (sym &iso) (Uz⊆A lt))) }


     ind : ( f : Ordinal → Ordinal ) → (mf : ≤-monotonic-f A f ) {y : Ordinal} (ay : odef A y) → (x : Ordinal)
         → ((z : Ordinal) → z o< x → ZChain A y f z) → ZChain A y f x
     ind f mf {y} ay x prev with Oprev-p x
     ... | yes op = zc4 where
          --
          -- we have previous ordinal to use induction
          --
          px = Oprev.oprev op
          supf : Ordinal → HOD
          supf = ZChain.supf (prev px (subst (λ k → px o< k) (Oprev.oprev=x op) <-osuc ) )
          zc : ZChain A y f (Oprev.oprev op)
          zc = prev px (subst (λ k → px o< k) (Oprev.oprev=x op) <-osuc ) 
          zc-b<x : (b : Ordinal ) → b o< x → b o< osuc px
          zc-b<x b lt = subst (λ k → b o< k ) (sym (Oprev.oprev=x op)) lt 
          px<x : px o< x
          px<x = subst (λ k → px o< k) (Oprev.oprev=x op) <-osuc

          -- if previous chain satisfies maximality, we caan reuse it
          --
          no-extenion : ( {a b : Ordinal} → odef (ZChain.chain zc) a → b o< osuc x → (ab : odef A b) →
                    HasPrev A (ZChain.chain zc) ab f ∨  IsSup A (ZChain.chain zc) ab →
                            * a < * b → odef (ZChain.chain zc) b ) → ZChain A y f x
          no-extenion is-max = record { supf = supf0 ;  chain⊆A = subst (λ k → k ⊆' A ) seq (ZChain.chain⊆A zc)
                     ; initial = subst (λ k →  {y₁ : Ordinal} → odef k y₁ → * y ≤ * y₁ ) seq (ZChain.initial zc)
                     ; f-next =  subst (λ k → {a : Ordinal} → odef k a → odef k (f a) ) seq (ZChain.f-next zc) 
                     ; chain∋x  = subst (λ k → odef k y ) seq (ZChain.chain∋x  zc)
                             ; is-max = subst (λ k → {a b : Ordinal} → odef k a → b o< osuc x → (ab : odef A b) →
                                 HasPrev A k ab f ∨  IsSup A k ab → * a < * b → odef k b  ) seq is-max } where
                supf0 : Ordinal → HOD
                supf0 z with trio< z x
                ... | tri< a ¬b ¬c = supf z
                ... | tri≈ ¬a b ¬c = ZChain.chain zc
                ... | tri> ¬a ¬b c = ZChain.chain zc 
                seq : ZChain.chain zc ≡ supf0 x 
                seq with trio< x x
                ... | tri< a ¬b ¬c = ⊥-elim ( ¬b refl )
                ... | tri≈ ¬a b ¬c = refl 
                ... | tri> ¬a ¬b c = refl 
                seq<x : {b : Ordinal } → b o< x →  supf b  ≡ supf0 b
                seq<x {b} b<x with trio< b x
                ... | tri< a ¬b ¬c = refl
                ... | tri≈ ¬a b₁ ¬c = ⊥-elim (¬a  b<x )
                ... | tri> ¬a ¬b c  = ⊥-elim (¬a  b<x )

          zc4 : ZChain A y f x 
          zc4 with ODC.∋-p O A (* x)
          ... | no noax = no-extenion zc1  where -- ¬ A ∋ p, just skip
                zc1 : {a b : Ordinal} → odef (ZChain.chain zc) a → b o< osuc x → (ab : odef A b) →
                    HasPrev A (ZChain.chain zc) ab f ∨  IsSup A (ZChain.chain zc) ab →
                            * a < * b → odef (ZChain.chain zc) b
                zc1 {a} {b} za b<ox ab P a<b with osuc-≡< b<ox
                ... | case1 eq = ⊥-elim ( noax (subst (λ k → odef A k) (trans eq (sym &iso)) ab ) )
                ... | case2 lt = ZChain.is-max zc za (zc-b<x b lt)  ab P a<b
          ... | yes ax with ODC.p∨¬p O ( HasPrev A (ZChain.chain zc) ax f )   -- we have to check adding x preserve is-max ZChain A y f mf supO x
          ... | case1 pr = no-extenion zc7  where -- we have previous A ∋ z < x , f z ≡ x, so chain ∋ f z ≡ x because of f-next
                chain0 = ZChain.chain zc
                zc7 :  {a b : Ordinal} → odef (ZChain.chain zc) a → b o< osuc x → (ab : odef A b) →
                            HasPrev A (ZChain.chain zc) ab f ∨ IsSup A (ZChain.chain zc) ab →
                            * a < * b → odef (ZChain.chain zc) b
                zc7 {a} {b} za b<ox ab P a<b with osuc-≡< b<ox
                ... | case2 lt = ZChain.is-max zc za (zc-b<x b lt) ab P a<b
                ... | case1 b=x = subst (λ k → odef chain0 k ) (trans (sym (HasPrev.x=fy pr )) (trans &iso (sym b=x)) ) ( ZChain.f-next zc (HasPrev.ay pr))
          ... | case2 ¬fy<x with ODC.p∨¬p O (IsSup A (ZChain.chain zc) ax )
          ... | case1 is-sup = -- x is a sup of zc 
                record {  chain⊆A = {!!} ; f-next = {!!} 
                     ; initial = {!!} ; chain∋x  = {!!} ; is-max = {!!}   ; supf = supf0 } where
                sup0 : SUP A (ZChain.chain zc) 
                sup0 = record { sup = * x ; A∋maximal = ax ; x<sup = x21 } where
                        x21 :  {y : HOD} → ZChain.chain zc ∋ y → (y ≡ * x) ∨ (y < * x)
                        x21 {y} zy with IsSup.x<sup is-sup zy 
                        ... | case1 y=x = case1 ( subst₂ (λ j k → j ≡ * k  ) *iso &iso ( cong (*) y=x)  )
                        ... | case2 y<x = case2 (subst₂ (λ j k → j < * k ) *iso &iso y<x  )
                sp : HOD
                sp = SUP.sup sup0 
                x=sup : x ≡ & sp 
                x=sup = sym &iso 
                chain0 = ZChain.chain zc
                sc<A : {y : Ordinal} → odef chain0 y ∨ FClosure A f (& sp) y → y o< & A
                sc<A {y} (case1 zx) = subst (λ k → k o< (& A)) &iso ( c<→o< (ZChain.chain⊆A zc (subst (λ k → odef chain0 k) (sym &iso) zx )))
                sc<A {y} (case2 fx) = subst (λ k → k o< (& A)) &iso ( c<→o< (subst (λ k → odef A k ) (sym &iso) (A∋fc (& sp) f mf fx )) )
                schain : HOD
                schain = record { od = record { def = λ x → odef chain0 x ∨ (FClosure A f (& sp) x) } ; odmax = & A ; <odmax = λ {y} sy → sc<A {y} sy  }
                supf0 : Ordinal → HOD
                supf0 z with trio< z x
                ... | tri< a ¬b ¬c = supf z
                ... | tri≈ ¬a b ¬c = schain 
                ... | tri> ¬a ¬b c = schain
                A∋schain : {x : HOD } → schain ∋ x → A ∋ x
                A∋schain (case1 zx ) = ZChain.chain⊆A zc zx 
                A∋schain {y} (case2 fx ) = A∋fc (& sp) f mf fx 
                s⊆A : schain ⊆' A
                s⊆A {x} (case1 zx) = ZChain.chain⊆A zc zx
                s⊆A {x} (case2 fx) = A∋fc (& sp) f mf fx 
                cmp  : {a b : HOD} (za : odef chain0 (& a)) (fb : FClosure A f (& sp) (& b)) → Tri (a < b) (a ≡ b) (b < a )
                cmp {a} {b} za fb  with SUP.x<sup sup0 za | s≤fc (& sp) f mf fb  
                ... | case1 sp=a | case1 sp=b = tri≈ (λ lt → <-irr (case1 (sym eq)) lt ) eq (λ lt → <-irr (case1 eq) lt ) where
                        eq : a ≡ b
                        eq = trans sp=a (subst₂ (λ j k → j ≡ k ) *iso *iso sp=b )
                ... | case1 sp=a | case2 sp<b = tri< a<b (λ eq → <-irr (case1 (sym eq)) a<b ) (λ lt → <-irr (case2 a<b) lt ) where
                        a<b : a < b
                        a<b = subst (λ k → k < b ) (sym sp=a) (subst₂ (λ j k → j < k ) *iso *iso sp<b )
                ... | case2 a<sp | case1 sp=b = tri< a<b (λ eq → <-irr (case1 (sym eq)) a<b ) (λ lt → <-irr (case2 a<b) lt ) where
                        a<b : a < b
                        a<b = subst (λ k → a < k ) (trans sp=b *iso ) (subst (λ k → a < k ) (sym *iso) a<sp )
                ... | case2 a<sp | case2 sp<b  = tri< a<b (λ eq → <-irr (case1 (sym eq)) a<b ) (λ lt → <-irr (case2 a<b) lt ) where
                        a<b : a < b
                        a<b = ptrans  (subst (λ k → a < k ) (sym *iso) a<sp ) ( subst₂ (λ j k → j < k ) refl *iso sp<b )
                scmp : {a b : HOD} → odef schain (& a) → odef schain (& b) → Tri (a < b) (a ≡ b) (b < a )
                scmp {a} {b} (case1 za) (case1 zb) = {!!} -- ZChain.f-total zc {px} {px} o≤-refl za zb
                scmp {a} {b} (case1 za) (case2 fb) = cmp za fb 
                scmp  (case2 fa) (case1 zb) with  cmp zb fa
                ... | tri< a ¬b ¬c = tri> ¬c (λ eq → ¬b (sym eq))  a
                ... | tri≈ ¬a b ¬c = tri≈ ¬c (sym b) ¬a
                ... | tri> ¬a ¬b c = tri< c (λ eq → ¬b (sym eq))  ¬a
                scmp (case2 fa) (case2 fb) = subst₂ (λ a b → Tri (a < b) (a ≡ b) (b < a ) ) *iso *iso (fcn-cmp (& sp) f mf fa fb)
                scnext : {a : Ordinal} → odef schain a → odef schain (f a)
                scnext {x} (case1 zx) = case1 (ZChain.f-next zc zx)
                scnext {x} (case2 sx) = case2 ( fsuc x sx )
                scinit :  {x : Ordinal} → odef schain x → * y ≤ * x
                scinit {x} (case1 zx) = ZChain.initial zc zx
                scinit {x} (case2 sx) with  (s≤fc (& sp) f mf sx ) |  SUP.x<sup sup0 (subst (λ k → odef chain0 k ) (sym &iso) ( ZChain.chain∋x zc ) )
                ... | case1 sp=x | case1 y=sp = case1 (trans y=sp (subst (λ k → k ≡ * x ) *iso sp=x ) )
                ... | case1 sp=x | case2 y<sp = case2 (subst (λ k → * y < k ) (trans (sym *iso) sp=x) y<sp )
                ... | case2 sp<x | case1 y=sp = case2 (subst (λ k → k < * x ) (trans *iso (sym y=sp )) sp<x )
                ... | case2 sp<x | case2 y<sp = case2 (ptrans y<sp (subst (λ k → k < * x ) *iso sp<x) )
                A∋za : {a : Ordinal } → odef chain0 a → odef A a
                A∋za za = ZChain.chain⊆A zc za 
                za<sup :  {a : Ordinal } → odef chain0 a → ( * a ≡ sp ) ∨  ( * a < sp )
                za<sup za =  SUP.x<sup sup0 (subst (λ k → odef chain0 k ) (sym &iso) za )
                s-ismax : {a b : Ordinal} → odef schain a → b o< osuc x → (ab : odef A b)
                    → HasPrev A schain ab f ∨ IsSup A schain ab   
                    → * a < * b → odef schain b
                s-ismax {a} {b} sa b<ox ab p a<b with osuc-≡< b<ox -- b is x?
                ... | case1 b=x = case2 (subst (λ k → FClosure A f (& sp) k ) (sym (trans b=x x=sup )) (init (SUP.A∋maximal sup0) ))
                s-ismax {a} {b} (case1 za) b<ox ab (case1 p) a<b | case2 b<x = z21 p where   -- has previous
                     z21 : HasPrev A schain ab f → odef schain b
                     z21 record { y = y ; ay = (case1 zy) ; x=fy = x=fy } = 
                           case1 (ZChain.is-max zc za (zc-b<x b b<x) ab (case1 record { y = y ; ay = zy ; x=fy = x=fy }) a<b )
                     z21 record { y = y ; ay = (case2 sy) ; x=fy = x=fy } = subst (λ k → odef schain k) (sym x=fy) (case2 (fsuc y sy) )
                s-ismax {a} {b} (case1 za) b<ox ab (case2 p) a<b | case2 b<x = case1 (ZChain.is-max zc za (zc-b<x b b<x) ab (case2 z22) a<b ) where -- previous sup
                     z22 : IsSup A (ZChain.chain zc)   ab 
                     z22 = record { x<sup = λ {y} zy → IsSup.x<sup p (case1 zy ) }
                s-ismax {a} {b} (case2 sa) b<ox ab (case1 p)  a<b | case2 b<x with HasPrev.ay p
                ... | case1 zy = case1 (subst (λ k → odef chain0 k ) (sym (HasPrev.x=fy p)) (ZChain.f-next zc zy ))               -- in previous closure of f
                ... | case2 sy = case2 (subst (λ k → FClosure A f (& (* x)) k ) (sym (HasPrev.x=fy p)) (fsuc (HasPrev.y p) sy ))  -- in current  closure of f
                s-ismax {a} {b} (case2 sa) b<ox ab (case2 p)  a<b | case2 b<x = case1 z23 where -- sup o< x is already in zc
                     z24 : IsSup A schain ab → IsSup A (ZChain.chain zc) ab 
                     z24 p = record { x<sup = λ {y} zy → IsSup.x<sup p (case1 zy ) }
                     z23 : odef chain0 b
                     z23 with IsSup.x<sup (z24 p) ( ZChain.chain∋x zc )
                     ... | case1 y=b  = subst (λ k → odef chain0 k )  y=b ( ZChain.chain∋x zc )
                     ... | case2 y<b  = ZChain.is-max zc (ZChain.chain∋x zc ) (zc-b<x b b<x) ab (case2 (z24 p)) y<b
                seq : schain ≡ supf0 x 
                seq with trio< x x
                ... | tri< a ¬b ¬c = ⊥-elim ( ¬b refl )
                ... | tri≈ ¬a b ¬c = refl
                ... | tri> ¬a ¬b c = refl
                seq<x : {b : Ordinal } → b o< x →  supf b  ≡ supf0 b
                seq<x {b} b<x with trio< b x
                ... | tri< a ¬b ¬c = refl
                ... | tri≈ ¬a b₁ ¬c = ⊥-elim (¬a  b<x )
                ... | tri> ¬a ¬b c  = ⊥-elim (¬a  b<x )
                mono : {a b  : Ordinal}  → a o≤ b → b o< osuc x → supf0 a ⊆' supf0 b 
                mono {a} {b} a≤b b<ox = {!!}

          ... | case2 ¬x=sup =  no-extenion z18 where -- x is not f y' nor sup of former ZChain from y -- no extention
                z18 :  {a b : Ordinal} → odef (ZChain.chain zc) a → b o< osuc x → (ab : odef A b) →
                            HasPrev A (ZChain.chain zc) ab f ∨ IsSup A (ZChain.chain zc)   ab →
                            * a < * b → odef (ZChain.chain zc) b
                z18 {a} {b} za b<x ab p a<b with osuc-≡< b<x
                ... | case2 lt = ZChain.is-max zc za (zc-b<x b lt) ab p a<b 
                ... | case1 b=x with p
                ... | case1 pr = ⊥-elim ( ¬fy<x record {y = HasPrev.y pr ; ay = HasPrev.ay pr ; x=fy = trans (trans &iso (sym b=x) ) (HasPrev.x=fy pr ) } )
                ... | case2 b=sup = ⊥-elim ( ¬x=sup record { 
                      x<sup = λ {y} zy → subst (λ k → (y ≡ k) ∨ (y << k)) (trans b=x (sym &iso)) (IsSup.x<sup b=sup zy)  } ) 
     ... | no ¬ox with trio< x y
     ... | tri< a ¬b ¬c = init-chain ay f mf {!!}
     ... | tri≈ ¬a b ¬c = init-chain ay f mf {!!}
     ... | tri> ¬a ¬b y<x = record { supf = supf0 ; chain⊆A = {!!} ; f-next = {!!} 
                     ; initial = {!!} ; chain∋x  = {!!} ; is-max = {!!} }   where --- limit ordinal case
         record UZFChain (z : Ordinal) : Set n where -- Union of ZFChain from y which has maximality o< x
            field
               u : Ordinal
               u<x : u o< x
               chain∋z : odef (ZChain.chain (prev u u<x  )) z
         Uz⊆A : {z : Ordinal} → UZFChain z → odef A z
         Uz⊆A {z} u = ZChain.chain⊆A ( prev (UZFChain.u u) (UZFChain.u<x u) ) (UZFChain.chain∋z u)
         uzc : {z : Ordinal} → (u : UZFChain z) → ZChain A y f (UZFChain.u u)
         uzc {z} u =  prev (UZFChain.u u) (UZFChain.u<x u) 
         Uz : HOD
         Uz = record { od = record { def = λ y → UZFChain y } ; odmax = & A
             ; <odmax = λ lt → subst (λ k → k o< & A ) &iso (c<→o< (subst (λ k → odef A k ) (sym &iso) (Uz⊆A lt))) }
         u-next : {z : Ordinal} → odef Uz z → odef Uz (f z)
         u-next {z} u = record { u = UZFChain.u u ; u<x = UZFChain.u<x u ; chain∋z = ZChain.f-next ( uzc u ) (UZFChain.chain∋z u)  }
         u-initial :  {z : Ordinal} → odef Uz z → * y ≤ * z 
         u-initial {z} u = ZChain.initial ( uzc u )  (UZFChain.chain∋z u)
         u-chain∋x :  odef Uz y
         u-chain∋x = record { u = y ; u<x = y<x ; chain∋z = ZChain.chain∋x (prev y y<x ) }
         supf0 : Ordinal → HOD
         supf0 z with trio< z x
         ... | tri< a ¬b ¬c = ZChain.supf (prev z a ) z
         ... | tri≈ ¬a b ¬c = Uz 
         ... | tri> ¬a ¬b c = Uz
         seq : Uz ≡ supf0 x
         seq with trio< x x
         ... | tri< a ¬b ¬c = ⊥-elim ( ¬b refl )
         ... | tri≈ ¬a b ¬c = refl
         ... | tri> ¬a ¬b c = refl
         seq<x : {b : Ordinal } → (b<x : b o< x ) →  ZChain.supf (prev b b<x ) b  ≡ supf0 b
         seq<x {b} b<x with trio< b x
         ... | tri< a ¬b ¬c = cong (λ k → ZChain.supf (prev b k ) b) o<-irr --  b<x ≡ a
         ... | tri≈ ¬a b₁ ¬c = ⊥-elim (¬a  b<x )
         ... | tri> ¬a ¬b c  = ⊥-elim (¬a  b<x )
         ord≤< : {x y z : Ordinal} → x o< z → z o≤ y → x o< y
         ord≤< {x} {y} {z} x<z z≤y  with  osuc-≡< z≤y
         ... | case1 z=y  = subst (λ k → x o< k ) z=y x<z
         ... | case2 z<y  = ordtrans x<z z<y
         u-mono :  {z : Ordinal} {w : Ordinal} → z o≤ w → w o≤ x → supf0 z ⊆' supf0 w
         u-mono {z} {w} z≤w w≤x {i} with trio< z x | trio< w x
         ... | tri< a ¬b ¬c | tri< a₁ ¬b₁ ¬c₁ = um00 where -- ZChain.chain-mono (prev w ? ay) ? ? lt
             um00 : odef  (ZChain.supf (prev z a ) z) i → odef  (ZChain.supf (prev w a₁ ) w) i 
             um00 = {!!}
             um01 : odef  (ZChain.supf (prev z a ) z) i → odef  (ZChain.supf (prev z {!!} ) w) i 
             um01 = {!!} -- ZChain.chain-mono (prev z a ay) {!!} {!!}
         ... | tri< a ¬b ¬c | tri≈ ¬a b ¬c₁ = λ lt → record { u = z ; u<x = a ; chain∋z = lt }
         ... | tri< a ¬b ¬c | tri> ¬a ¬b₁ c = ⊥-elim ( osuc-< w≤x c )
         ... | tri≈ ¬a z=x ¬c | tri< w<x ¬b ¬c₁ = ⊥-elim ( osuc-< z≤w (subst (λ k → w o< k ) (sym z=x) w<x ) )
         ... | tri≈ ¬a b ¬c | tri≈ ¬a₁ b₁ ¬c₁ = λ lt → lt 
         ... | tri≈ ¬a b ¬c | tri> ¬a₁ ¬b c = ⊥-elim ( osuc-< w≤x c ) -- o<> c ( ord≤< w≤x )) -- z≡w x o< w
         ... | tri> ¬a ¬b c | t = ⊥-elim ( osuc-< w≤x (ord≤< c  z≤w ) ) -- x o< z → x o< w 
         
     SZ : ( f : Ordinal → Ordinal ) → (mf : ≤-monotonic-f A f ) → {y : Ordinal} (ya : odef A y) → ZChain A y f (& A)
     SZ f mf {y} ay = TransFinite {λ z → ZChain A y f z  } (ind f mf ay ) (& A)

     ind-mono : ( f : Ordinal → Ordinal ) → (mf : ≤-monotonic-f A f ) { y : Ordinal} (ay : odef A y) → (x : Ordinal)
         → (prev : (z : Ordinal) → z o< x → ZChain A y f z) 
         → (z : Ordinal) → (z<x : z o< x) → ZChain.chain  (prev z z<x )  ⊆'  ZChain.chain ( ind f mf ay x prev )
     ind-mono f mf ay x prev z z<x = {!!}

     postulate
       TFcomm :  { ψ : Ordinal  → Set (Level.suc n) }
          → (ind :  (x : Ordinal)  → ( (y : Ordinal  ) → y o< x → ψ y ) → ψ x )
          →  ∀ (x : Ordinal)  →   ind  x (λ y _ → TransFinite ind  y )  ≡ TransFinite ind  x

     SZ-mono : ( f : Ordinal → Ordinal ) → (mf : ≤-monotonic-f A f ) → {y : Ordinal} → (ay : odef A y) 
         → {a b : Ordinal } → a o< b →
         ZChain.chain (TransFinite {λ z → ZChain A y f z  } (ind f mf ay ) a )  ⊆' 
         ZChain.chain (TransFinite {λ z → ZChain A y f z  } (ind f mf ay ) b )
     SZ-mono f mf {y} ay {a} {b} a<b = TransFinite0 {λ b → a o< b →  ZChain.chain (TransFinite {λ z → ZChain A y f z  } (ind f mf ay ) a )  ⊆'
         ZChain.chain (TransFinite {λ z → ZChain A y f z  } (ind f mf ay ) b ) } szind b a<b where
          szind :  (x : Ordinal) → ((y₁ : Ordinal) → y₁ o< x → a o< y₁ →
             ZChain.chain (TransFinite (ind f mf ay) a) ⊆' ZChain.chain (TransFinite (ind f mf ay) y₁)) →
            a o< x → ZChain.chain (TransFinite (ind f mf ay) a) ⊆' ZChain.chain (TransFinite (ind f mf ay) x)
          szind = {!!}  --


     zorn00 : Maximal A 
     zorn00 with is-o∅ ( & HasMaximal )  -- we have no Level (suc n) LEM 
     ... | no not = record { maximal = ODC.minimal O HasMaximal  (λ eq → not (=od∅→≡o∅ eq)) ; A∋maximal = zorn01 ; ¬maximal<x  = zorn02 } where
         -- yes we have the maximal
         zorn03 :  odef HasMaximal ( & ( ODC.minimal O HasMaximal  (λ eq → not (=od∅→≡o∅ eq)) ) )
         zorn03 =  ODC.x∋minimal  O HasMaximal  (λ eq → not (=od∅→≡o∅ eq))   -- Axiom of choice
         zorn01 :  A ∋ ODC.minimal O HasMaximal (λ eq → not (=od∅→≡o∅ eq))
         zorn01  = proj1  zorn03  
         zorn02 : {x : HOD} → A ∋ x → ¬ (ODC.minimal O HasMaximal (λ eq → not (=od∅→≡o∅ eq)) < x)
         zorn02 {x} ax m<x = proj2 zorn03 (& x) ax (subst₂ (λ j k → j < k) (sym *iso) (sym *iso) m<x )
     ... | yes ¬Maximal = ⊥-elim ( z04 nmx zorn04 {!!} ) where
         -- if we have no maximal, make ZChain, which contradict SUP condition
         nmx : ¬ Maximal A 
         nmx mx =  ∅< {HasMaximal} zc5 ( ≡o∅→=od∅  ¬Maximal ) where
              zc5 : odef A (& (Maximal.maximal mx)) ∧ (( y : Ordinal ) →  odef A y → ¬ (* (& (Maximal.maximal mx)) < * y)) 
              zc5 = ⟪  Maximal.A∋maximal mx , (λ y ay mx<y → Maximal.¬maximal<x mx (subst (λ k → odef A k ) (sym &iso) ay) (subst (λ k → k < * y) *iso mx<y) ) ⟫
         zorn04 : ZChain A (& s) (cf nmx) (& A)
         zorn04 = SZ (cf nmx) (cf-is-≤-monotonic nmx) (subst (λ k → odef A k ) &iso as )

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
