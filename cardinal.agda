open import Level
open import Ordinals
module cardinal {n : Level } (O : Ordinals {n}) where

open import zf
open import logic
import OD 
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

open _∧_
open _∨_
open Bool

-- we have to work on Ordinal to keep OD Level n
-- since we use p∨¬p which works only on Level n

func→od : (f : Ordinal → Ordinal ) → ( dom : OD ) → OD 
func→od f dom = Replace dom ( λ x →  x , (ord→od (f (od→ord x) )))

record _⊗_  (A B : Ordinal) : Set n where
   field
      π1 : Ordinal
      π2 : Ordinal
      A∋π1 : def (ord→od A)  π1
      B∋π2 : def (ord→od B)  π2

-- Clearly wrong. We need ordered pair
Func :  ( A B : OD ) → OD
Func A B = record { def = λ x → (od→ord A) ⊗ (od→ord B) }

open  _⊗_

func←od : { dom cod : OD } → (f : OD )  → Func dom cod ∋ f → (Ordinal → Ordinal )
func←od {dom} {cod} f lt x = sup-o ( λ y → lemma  y ) where
   lemma : Ordinal → Ordinal
   lemma y with p∨¬p ( _⊗_.π1 lt ≡ x )
   lemma y | case1 refl = _⊗_.π2 lt
   lemma y | case2 not = o∅

-- contra position of sup-o<
--

postulate
  -- contra-position of mimimulity of supermum required in Cardinal
  sup-x  : ( Ordinal  → Ordinal ) →  Ordinal 
  sup-lb : { ψ : Ordinal  →  Ordinal } → {z : Ordinal }  →  z o< sup-o ψ → z o< osuc (ψ (sup-x ψ))

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
       onto-iso   : {y :  Ordinal  } → (lty : def Y y ) → func←od (ord→od xmap) xfunc ( func←od (ord→od ymap) yfunc y )  ≡ y

open Onto

onto-restrict : {X Y Z : OD} → Onto X Y → ({x : OD} → _⊆_ Z Y {x}) → Onto X Z
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
       onto-iso1   : {z :  Ordinal  } → (ltz : def Z z ) → func←od (ord→od xmap1) xfunc1 ( func←od (ord→od zmap) zfunc z )  ≡ z
       onto-iso1   = {!!}


record Cardinal  (X  : OD ) : Set n where
   field
       cardinal : Ordinal 
       conto : Onto X (Ord cardinal)  
       cmax : ( y : Ordinal  ) → cardinal o< y → ¬ Onto X (Ord y)  

cardinal :  (X  : OD ) → Cardinal X
cardinal  X = record {
       cardinal = sup-o ( λ x → proj1 ( cardinal-p x) )
     ; conto = onto
     ; cmax = cmax
   } where
    cardinal-p : (x  : Ordinal ) →  ( Ordinal  ∧ Dec (Onto X (Ord x) ) )
    cardinal-p x with p∨¬p ( Onto X (Ord x)  ) 
    cardinal-p x | case1 True  = record { proj1 = x  ; proj2 = yes True }
    cardinal-p x | case2 False = record { proj1 = o∅ ; proj2 = no False }
    S = sup-o (λ x → proj1 (cardinal-p x))
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
       (sup-o<  {λ x → proj1 ( cardinal-p x)}{y}  ) lemma refl ) where
          lemma : proj1 (cardinal-p y) ≡ y
          lemma with  p∨¬p ( Onto X (Ord y) )
          lemma | case1 x = refl
          lemma | case2 not = ⊥-elim ( not ontoy )


-----
--  All cardinal is ℵ0,  since we are working on Countable Ordinal, 
--  Power ω is larger than ℵ0, so it has no cardinal.



