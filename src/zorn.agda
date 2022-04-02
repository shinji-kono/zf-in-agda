open import Level
open import Ordinals
module zorn {n : Level } (O : Ordinals {n})   where

open import zf
open import logic
-- open import partfunc {n} O
import OD 

open import Relation.Nullary 
open import Relation.Binary 
open import Data.Empty 
open import Relation.Binary
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality
import BAlgbra 


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

record Element (A : HOD) : Set (suc n) where
    field
       elm : HOD
       is-elm : A ∋ elm

open Element

TotalOrderSet : ( A : HOD ) →  (_<_ : (x y : HOD) → Set n )  → Set (suc n)
TotalOrderSet A _<_ = Trichotomous (λ (x : Element A) y → elm x ≡ elm y ) (λ x y → elm x < elm y )  

PartialOrderSet : ( A : HOD ) →  (_<_ : (x y : HOD) → Set n )  → Set (suc n)
PartialOrderSet A _<_ = (a b :  Element A)
     → (elm a < elm b → (¬ (elm b < elm a) ∧ (¬ (elm a ≡ elm b) ))) ∧ (elm a ≡ elm b → (¬ elm a < elm b) ∧ (¬ elm b < elm a))

me : { A a : HOD } → A ∋ a → Element A
me {A} {a} lt = record { elm = a ; is-elm = lt }

record SUP ( A B : HOD ) (_<_ : (x y : HOD) → Set n ) : Set (suc n) where
   field
      sup : HOD
      A∋maximal : A ∋ sup
      x≤sup : {x : HOD} → B ∋ x → (x ≡ sup ) ∨ (x < sup )   -- B is Total

record Maximal ( A : HOD ) (_<_ : (x y : HOD) → Set n ) : Set (suc n) where
   field
      maximal : HOD
      A∋maximal : A ∋ maximal
      ¬maximal<x : {x : HOD} → A ∋ x  → ¬ maximal < x       -- A is Partial, use negative

open _==_
open _⊆_

record ZChain ( A : HOD ) (y : Ordinal)  (_<_ : (x y : HOD) → Set n ) : Set (suc n) where
   field
      B : HOD
      B⊆A : B ⊆ A 
      total : TotalOrderSet B _<_
      fb : {x : HOD } → A ∋ x  → HOD
      B∋fb : (x : HOD ) → (ax : A ∋ x)  → B ∋ fb ax
      ¬x≤sup : (sup : HOD) → (as : A ∋ sup ) → & sup o< osuc y → sup < fb as

Zorn-lemma : { A : HOD } → { _<_ : (x y : HOD) → Set n }
    → o∅ o< & A 
    → PartialOrderSet A _<_
    → ( ( B : HOD) → (B⊆A : B ⊆ A) → TotalOrderSet B _<_ → SUP A B  _<_  ) -- SUP condition
    → Maximal A _<_ 
Zorn-lemma {A} {_<_} 0<A PO supP = zorn00 where
     someA : HOD
     someA = ODC.minimal O A (λ eq → ¬x<0 ( subst (λ k → o∅ o< k ) (=od∅→≡o∅ eq) 0<A )) 
     isSomeA : A ∋ someA
     isSomeA =  ODC.x∋minimal O A (λ eq → ¬x<0 ( subst (λ k → o∅ o< k ) (=od∅→≡o∅ eq) 0<A )) 
     HasMaximal : HOD
     HasMaximal = record { od = record { def = λ x → (m : Ordinal) →  odef A m → odef A x ∧ (¬ (* x < * m))} ; odmax = & A ; <odmax = {!!} } where
         z07 :  {y : Ordinal} → ((m : Ordinal) → odef A y ∧ odef A m ∧ (¬ (* y < * m))) → y o< & A
         z07 {y} p = subst (λ k → k o< & A) &iso ( c<→o< (subst (λ k → odef A k ) (sym &iso ) (proj1 (p (& someA)) )))
     no-maximum : HasMaximal =h= od∅ → (x : Ordinal) → ((m : Ordinal) →  odef A m →  odef A x ∧ (¬ (* x < * m) )) →  ⊥
     no-maximum nomx x P = ¬x<0 (eq→ nomx {x} (λ m am → P m am )) 
     Gtx : { x : HOD} → A ∋ x → HOD
     Gtx {x} ax = record { od = record { def = λ y → odef A y ∧ (x < (* y)) } ; odmax = & A ; <odmax = {!!} } 
     z01 : {a b : HOD} → A ∋ a → A ∋ b  → (a ≡ b ) ∨ (a < b ) → b < a → ⊥
     z01 {a} {b} A∋a A∋b (case1 a=b) b<a = proj1 (proj2 (PO (me  A∋b) (me A∋a)) (sym a=b)) b<a
     z01 {a} {b} A∋a A∋b (case2 a<b) b<a = proj1 (PO (me  A∋b) (me A∋a)) b<a ⟪ a<b , (λ b=a → proj1 (proj2 (PO (me  A∋b) (me A∋a)) b=a ) b<a ) ⟫
     -- ZChain is not compatible with the SUP condition
     ZChain→¬SUP :  (z : ZChain A (& A) _<_ ) →  ¬ (SUP A (ZChain.B z) _<_ )
     ZChain→¬SUP z sp = ⊥-elim (z02 (ZChain.fb z (SUP.A∋maximal sp)) (ZChain.B∋fb z  _ (SUP.A∋maximal sp)) (ZChain.¬x≤sup z _  (SUP.A∋maximal sp) z03 )) where
         z03 : & (SUP.sup sp) o< osuc (& A)
         z03 = ordtrans (c<→o< (SUP.A∋maximal sp)) <-osuc
         z02 :  (x : HOD) → ZChain.B z ∋ x → SUP.sup sp < x → ⊥
         z02 x xe s<x = z01 (incl (ZChain.B⊆A z) xe) (SUP.A∋maximal sp) (SUP.x≤sup sp xe) s<x 
     ind :  HasMaximal =h= od∅
         → (x : Ordinal) → ((y : Ordinal) → y o< x →  ZChain A y _<_ )
         →  ZChain A x _<_
     ind nomx x prev with Oprev-p x
     ... | yes op with ODC.∋-p O A (* x)
     ... | no ¬Ax = record  { B = ZChain.B zc1 ; B⊆A =  ZChain.B⊆A  zc1 ; total = ZChain.total zc1 ; fb = ZChain.fb zc1 ; B∋fb = ZChain.B∋fb zc1 ; ¬x≤sup = z04 } where
          -- we have previous ordinal and ¬ A ∋ x, use previous Zchain
          px = Oprev.oprev op
          zc1 : ZChain A px _<_
          zc1 = prev px (subst (λ k → px o< k) (Oprev.oprev=x op) <-osuc) 
          z04 :  (sup : HOD) (as : A ∋ sup) → & sup o< osuc x → sup < ZChain.fb zc1 as
          z04 sup as s<x with trio< (& sup) x
          ... | tri≈ ¬a b ¬c = ⊥-elim (¬Ax (subst (λ k → odef A k) (trans b (sym &iso)) as) )  
          ... | tri< a ¬b ¬c  = ZChain.¬x≤sup zc1 _ as ( subst (λ k → & sup o< k ) (sym (Oprev.oprev=x op)) a )
          ... | tri> ¬a ¬b c with  osuc-≡< s<x
          ... | case1 eq = ⊥-elim (¬Ax (subst (λ k → odef A k) (trans eq (sym &iso)) as) )  
          ... | case2 lt = ⊥-elim (¬a lt )
     ... | yes ax = z06 where -- we have previous ordinal and A ∋ x
          px = Oprev.oprev op
          zc1 : ZChain A px _<_
          zc1 = prev px (subst (λ k → px o< k) (Oprev.oprev=x op) <-osuc) 
          z06 : ZChain A x _<_
          z06 with is-o∅ (& (Gtx ax))
          ... | yes nogt = ⊥-elim (no-maximum nomx x x-is-maximal ) where -- no larger element, so it is maximal
              x-is-maximal :  (m : Ordinal) → odef A m → odef A x ∧ (¬ (* x < * m))
              x-is-maximal m am  = ⟪ subst (λ k → odef A k) &iso ax ,  ¬x<m  ⟫ where
                 ¬x<m :  ¬ (* x < * m)
                 ¬x<m x<m = ∅< {Gtx ax} {* m} ⟪ subst (λ k → odef A k) (sym &iso) am , subst (λ k → * x < k ) (cong (*) (sym &iso)) x<m ⟫  (≡o∅→=od∅ nogt) 
          ... | no not = record { B = Bx     --  we have larger element, let's create ZChain
              ; B⊆A = B⊆A ; total = {!!} ; fb = {!!} ; B∋fb = {!!} ; ¬x≤sup = {!!} } where
                 B = ZChain.B zc1 
                 Bx : HOD
                 Bx = record { od = record { def = λ y → (x ≡ y) ∨ odef B y } ; odmax = & A ; <odmax = {!!}  }  -- Union (B , x)
                 B⊆A : Bx ⊆ A
                 B⊆A = record { incl = λ {y} by → z07 y by  } where
                     z07 : (y : HOD) → Bx ∋ y → A ∋ y
                     z07 y (case1 x=y) = subst (λ k → odef A k ) (trans &iso x=y) ax
                     z07 y (case2 by) = incl (ZChain.B⊆A zc1 ) by
                 m = ODC.minimal O (Gtx ax) (λ eq → not (=od∅→≡o∅ eq))
     ind nomx x prev | no ¬ox with trio< (& A) x   --- limit ordinal case
     ... | tri< a ¬b ¬c = record { B = ZChain.B zc1
              ; B⊆A = ZChain.B⊆A zc1 ; total = ZChain.total zc1 ; fb = ZChain.fb zc1 ; B∋fb = ZChain.B∋fb zc1 ; ¬x≤sup = {!!} } where
          zc1 : ZChain A (& A) _<_
          zc1 = prev (& A) a 
     ... | tri≈ ¬a b ¬c = record { B = B
              ; B⊆A = {!!} ; total = {!!} ; fb = {!!} ; B∋fb = {!!} ; ¬x≤sup = {!!} } where
          B : HOD
          B = record { od = record { def = λ y → (y<x : y o< x ) → odef (ZChain.B (prev y y<x)) y } ; odmax = & A ; <odmax = {!!} } 
     ... | tri> ¬a ¬b c = {!!}
     zorn00 : Maximal A _<_
     zorn00 with is-o∅ ( & HasMaximal )
     ... | no not = record { maximal = ODC.minimal O HasMaximal  (λ eq → not (=od∅→≡o∅ eq)) ; A∋maximal = zorn01 ; ¬maximal<x  = zorn02 } where
         -- yes we have the maximal
         zorn03 :  odef HasMaximal ( & ( ODC.minimal O HasMaximal  (λ eq → not (=od∅→≡o∅ eq)) ) )
         zorn03 =  ODC.x∋minimal  O HasMaximal  (λ eq → not (=od∅→≡o∅ eq))
         zorn01 :  A ∋ ODC.minimal O HasMaximal (λ eq → not (=od∅→≡o∅ eq))
         zorn01 =  proj1 (zorn03 (& someA) isSomeA ) 
         zorn02 : {x : HOD} → A ∋ x → ¬ (ODC.minimal O HasMaximal (λ eq → not (=od∅→≡o∅ eq)) < x)
         zorn02 {x} ax m<x = proj2 (zorn03 (& x) ax) (subst₂ (λ j k → j < k) (sym *iso) (sym *iso) m<x )
     ... | yes ¬Maximal = ⊥-elim ( ZChain→¬SUP (z (& A) (≡o∅→=od∅ ¬Maximal)) ( supP B (ZChain.B⊆A (z (& A) (≡o∅→=od∅ ¬Maximal))) (ZChain.total (z (& A) (≡o∅→=od∅ ¬Maximal))) )) where
         -- if we have no maximal, make ZChain, which contradict SUP condition
         z : (x : Ordinal) → HasMaximal =h= od∅  → ZChain A x _<_ 
         z x nomx = TransFinite (ind nomx) x
         B = ZChain.B (z (& A) (≡o∅→=od∅ ¬Maximal)  )

