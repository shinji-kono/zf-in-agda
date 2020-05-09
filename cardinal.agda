open import Level
open import Ordinals
module cardinal {n : Level } (O : Ordinals {n}) where

open import zf
open import logic
import OD 
import ODC
import OPair
open import Data.Nat renaming ( zero to Zero ; suc to Suc ;  ℕ to Nat ; _⊔_ to _n⊔_ ) 
open import Relation.Binary.PropositionalEquality
open import Data.Nat.Properties 
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.Core

open inOrdinal O
open OD O
open OD.OD
open OPair O
open ODAxiom odAxiom

open _∧_
open _∨_
open Bool
open _==_

-- we have to work on Ordinal to keep OD Level n
-- since we use p∨¬p which works only on Level n

    
∋-p : (A x : OD ) → Dec ( A ∋ x ) 
∋-p A x with ODC.p∨¬p O ( A ∋ x )
∋-p A x | case1 t = yes t
∋-p A x | case2 t = no t

_⊗_  : (A B : OD) → OD
A ⊗ B  = record { def = λ x → def ZFProduct x ∧ ( { x : Ordinal } → (p : def ZFProduct x ) → checkAB p ) } where
    checkAB : { p : Ordinal } → def ZFProduct p → Set n
    checkAB (pair x y) = def A x ∧ def B y

func→od0  : (f : Ordinal → Ordinal ) → OD
func→od0  f = record { def = λ x → def ZFProduct x ∧ ( { x : Ordinal } → (p : def ZFProduct x ) → checkfunc p ) } where
    checkfunc : { p : Ordinal } → def ZFProduct p → Set n
    checkfunc (pair x y) = f x ≡ y

--  Power (Power ( A ∪ B )) ∋ ( A ⊗ B )

Func :  ( A B : OD ) → OD
Func A B = record { def = λ x → def (Power (A ⊗ B)) x } 

-- power→ :  ( A t : OD) → Power A ∋ t → {x : OD} → t ∋ x → ¬ ¬ (A ∋ x)

func→od : (f : Ordinal → Ordinal ) → ( dom : OD ) → OD 
func→od f dom = Replace dom ( λ x →  < x , ord→od (f (od→ord x)) > )

record Func←cd { dom cod : OD } {f : Ordinal }  : Set n where
   field
      func-1 : Ordinal → Ordinal
      func→od∈Func-1 :  Func dom cod ∋  func→od func-1 dom
 
od→func : { dom cod : OD } → {f : Ordinal }  → def (Func dom cod ) f  → Func←cd {dom} {cod} {f} 
od→func {dom} {cod} {f} lt = record { func-1 = λ x → sup-o ( λ y → lemma x {!!} ) ; func→od∈Func-1 = record { proj1 = {!!} ; proj2 = {!!} } } where
   lemma : Ordinal → Ordinal → Ordinal
   lemma x y with IsZF.power→ isZF (dom ⊗ cod) (ord→od f) (subst (λ k → def (Power (dom ⊗ cod)) k ) (sym diso) lt ) | ∋-p (ord→od f) (ord→od y)
   lemma x y | p | no n  = o∅
   lemma x y | p | yes f∋y = lemma2 (proj1 (ODC.double-neg-eilm O ( p {ord→od y} f∋y ))) where -- p : {y : OD} → f ∋ y → ¬ ¬ (dom ⊗ cod ∋ y) 
           lemma2 : {p : Ordinal} → ord-pair p  → Ordinal
           lemma2 (pair x1 y1) with ODC.decp O ( x1 ≡ x)
           lemma2 (pair x1 y1) | yes p = y1
           lemma2 (pair x1 y1) | no ¬p = o∅
   fod : OD
   fod = Replace dom ( λ x →  < x , ord→od (sup-o ( λ y → lemma (od→ord x) {!!} )) > )


open Func←cd

-- contra position of sup-o<
--

-- postulate
--   -- contra-position of mimimulity of supermum required in Cardinal
--   sup-x  : ( Ordinal  → Ordinal ) →  Ordinal 
--   sup-lb : { ψ : Ordinal  →  Ordinal } → {z : Ordinal }  →  z o< sup-o ψ → z o< osuc (ψ (sup-x ψ))

------------
--
-- Onto map
--          def X x ->  xmap
--     X ---------------------------> Y
--          ymap   <-  def Y y
--
record Onto  (X Y : OD )  : Set n where
   field
       xmap : Ordinal 
       ymap : Ordinal 
       xfunc : def (Func X Y) xmap 
       yfunc : def (Func Y X) ymap 
       onto-iso   : {y :  Ordinal  } → (lty : def Y y ) →
          func-1 ( od→func {X} {Y} {xmap} xfunc ) ( func-1 (od→func  yfunc) y )  ≡ y 

open Onto

onto-restrict : {X Y Z : OD} → Onto X Y → Z ⊆ Y  → Onto X Z
onto-restrict {X} {Y} {Z} onto  Z⊆Y = record {
     xmap = xmap1
   ; ymap = zmap
   ; xfunc = xfunc1
   ; yfunc = zfunc
   ; onto-iso = onto-iso1
  } where
       xmap1 : Ordinal 
       xmap1 = od→ord (Select (ord→od (xmap onto)) {!!} ) 
       zmap : Ordinal 
       zmap = {!!}
       xfunc1 : def (Func X Z) xmap1
       xfunc1 = {!!}
       zfunc : def (Func Z X) zmap 
       zfunc = {!!}
       onto-iso1   : {z :  Ordinal  } → (ltz : def Z z ) → func-1 (od→func  xfunc1 )  (func-1 (od→func  zfunc ) z )  ≡ z
       onto-iso1   = {!!}


record Cardinal  (X  : OD ) : Set n where
   field
       cardinal : Ordinal 
       conto : Onto X (Ord cardinal)  
       cmax : ( y : Ordinal  ) → cardinal o< y → ¬ Onto X (Ord y)  

cardinal :  (X  : OD ) → Cardinal X
cardinal  X = record {
       cardinal = sup-o ( λ x → proj1 ( cardinal-p {!!}) )
     ; conto = onto
     ; cmax = cmax
   } where
    cardinal-p : (x  : Ordinal ) →  ( Ordinal  ∧ Dec (Onto X (Ord x) ) )
    cardinal-p x with ODC.p∨¬p O ( Onto X (Ord x)  ) 
    cardinal-p x | case1 True  = record { proj1 = x  ; proj2 = yes True }
    cardinal-p x | case2 False = record { proj1 = o∅ ; proj2 = no False }
    S = sup-o (λ x → proj1 (cardinal-p {!!}))
    lemma1 :  (x : Ordinal) → ((y : Ordinal) → y o< x → Lift (suc n) (y o< (osuc S) → Onto X (Ord y))) →
                    Lift (suc n) (x o< (osuc S) → Onto X (Ord x) )
    lemma1 x prev with trio< x (osuc S)
    lemma1 x prev | tri< a ¬b ¬c with osuc-≡< a
    lemma1 x prev | tri< a ¬b ¬c | case1 x=S = lift ( λ lt → {!!} )
    lemma1 x prev | tri< a ¬b ¬c | case2 x<S = lift ( λ lt → lemma2 ) where
         lemma2 : Onto X (Ord x) 
         lemma2 with prev {!!} {!!}
         ... | lift t = t {!!}
    lemma1 x prev | tri≈ ¬a b ¬c = lift ( λ lt → ⊥-elim ( o<¬≡ b lt ))
    lemma1 x prev | tri> ¬a ¬b c = lift ( λ lt → ⊥-elim ( o<> c lt ))
    onto : Onto X (Ord S) 
    onto with TransFinite {λ x → Lift (suc n) ( x o< osuc S → Onto X (Ord x) ) } lemma1 S 
    ... | lift t = t <-osuc  
    cmax : (y : Ordinal) → S o< y → ¬ Onto X (Ord y) 
    cmax y lt ontoy = o<> lt (o<-subst  {_} {_} {y} {S}
       (sup-o<  {λ x → proj1 ( cardinal-p {!!})}{{!!}}  ) lemma refl ) where
          lemma : proj1 (cardinal-p y) ≡ y
          lemma with  ODC.p∨¬p O ( Onto X (Ord y) )
          lemma | case1 x = refl
          lemma | case2 not = ⊥-elim ( not ontoy )


-----
--  All cardinal is ℵ0,  since we are working on Countable Ordinal, 
--  Power ω is larger than ℵ0, so it has no cardinal.



