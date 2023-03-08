open import Level
open import Ordinals
module PFOD {n : Level } (O : Ordinals {n})   where

import filter 
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
open import Data.Nat renaming ( zero to Zero ; suc to Suc ;  ℕ to Nat ; _⊔_ to _n⊔_ ) 
import BAlgebra 

open BAlgebra O

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

open filter O

open _∧_
open _∨_
open Bool


open HOD

-------
--    the set of finite partial functions from ω to 2
--
--

open import Data.List hiding (filter)
open import Data.Maybe 

open import ZProduct O

data Hω2 :  (i : Nat) ( x : Ordinal  ) → Set n where
  hφ :  Hω2 0 o∅
  h0 : {i : Nat} {x : Ordinal  } → Hω2 i x  →
    Hω2 (Suc i) (& (Union ((< nat→ω i , nat→ω 0 >) ,  * x )))
  h1 : {i : Nat} {x : Ordinal  } → Hω2 i x  →
    Hω2 (Suc i) (& (Union ((< nat→ω i , nat→ω 1 >) ,  * x )))
  he : {i : Nat} {x : Ordinal  } → Hω2 i x  →
    Hω2 (Suc i) x

record  Hω2r (x : Ordinal) : Set n where
  field
    count : Nat
    hω2 : Hω2 count x

open Hω2r

HODω2 :  HOD
HODω2 = record { od = record { def = λ x → Hω2r x } ; odmax = next o∅ ; <odmax = odmax0 } where
    P  : (i j : Nat) (x : Ordinal ) → HOD
    P  i j x = ((nat→ω i , nat→ω i) , (nat→ω i , nat→ω j)) , * x
    nat1 : (i : Nat) (x : Ordinal) → & (nat→ω i) o< next x
    nat1 i x =  next< nexto∅ ( <odmax infinite (ω∋nat→ω {i}))
    lemma1 : (i j : Nat) (x : Ordinal ) → osuc (& (P i j x)) o< next x
    lemma1 i j x = osuc<nx (pair-<xy (pair-<xy (pair-<xy (nat1 i x) (nat1 i x) ) (pair-<xy (nat1 i x) (nat1 j x) ) )
         (subst (λ k → k o< next x) (sym &iso) x<nx ))
    lemma : (i j : Nat) (x : Ordinal ) → & (Union (P i j x)) o< next x
    lemma i j x = next< (lemma1 i j x ) ho<
    odmax0 :  {y : Ordinal} → Hω2r y → y o< next o∅ 
    odmax0 {y} r with hω2 r
    ... | hφ = x<nx
    ... | h0 {i} {x} t = next< (odmax0 record { count = i ; hω2 = t }) (lemma i 0 x)
    ... | h1 {i} {x} t = next< (odmax0 record { count = i ; hω2 = t }) (lemma i 1 x)
    ... | he {i} {x} t = next< (odmax0 record { count = i ; hω2 = t }) x<nx

3→Hω2 : List (Maybe Two) → HOD
3→Hω2 t = list→hod t 0 where
   list→hod : List (Maybe Two) → Nat → HOD
   list→hod [] _ = od∅
   list→hod (just i0 ∷ t) i = Union (< nat→ω i , nat→ω 0 > , ( list→hod t (Suc i) )) 
   list→hod (just i1 ∷ t) i = Union (< nat→ω i , nat→ω 1 > , ( list→hod t (Suc i) )) 
   list→hod (nothing ∷ t) i = list→hod t (Suc i ) 

Hω2→3 : (x :  HOD) → HODω2 ∋ x → List (Maybe Two) 
Hω2→3 x = lemma where
   lemma : { y : Ordinal } →  Hω2r y → List (Maybe Two)
   lemma record { count = 0 ; hω2 = hφ } = []
   lemma record { count = (Suc i) ; hω2 = (h0 hω3) } = just i0 ∷ lemma record { count = i ; hω2 =  hω3 }
   lemma record { count = (Suc i) ; hω2 = (h1 hω3) } = just i1 ∷ lemma record { count = i ; hω2 =  hω3 }
   lemma record { count = (Suc i) ; hω2 = (he hω3) } = nothing ∷ lemma record { count = i ; hω2 =  hω3 }

ω→2 : HOD
ω→2 = Power infinite

ω2→f : (x : HOD) → ω→2 ∋ x → Nat → Two
ω2→f x lt n with ODC.∋-p O x (nat→ω n)
ω2→f x lt n | yes p = i1
ω2→f x lt n | no ¬p = i0

fω→2-sel : ( f : Nat → Two ) (x : HOD) → Set n
fω→2-sel f x = (infinite ∋ x) ∧ ( (lt : odef infinite (&  x) ) → f (ω→nat x lt) ≡ i1 )

fω→2 : (Nat → Two) → HOD
fω→2 f = Select infinite (fω→2-sel f)

open _==_

import Axiom.Extensionality.Propositional
postulate f-extensionality : { n m : Level}  → Axiom.Extensionality.Propositional.Extensionality n m

ω2∋f : (f : Nat → Two) → ω→2 ∋ fω→2 f
ω2∋f f = power← infinite (fω→2 f) (λ {x} lt →  proj1 ((proj2 (selection {fω→2-sel f} {infinite} )) lt))

ω→2f≡i1 : (X i : HOD) → (iω : infinite ∋ i) → (lt : ω→2 ∋ X ) → ω2→f X lt (ω→nat i iω)  ≡ i1 → X ∋ i
ω→2f≡i1 X i iω lt eq with ODC.∋-p O X (nat→ω (ω→nat i iω))
ω→2f≡i1 X i iω lt eq | yes p = subst (λ k → X ∋ k ) (nat→ω-iso iω) p

ω2→f-iso : (X : HOD) → ( lt : ω→2 ∋ X ) → fω→2 ( ω2→f X lt )  =h= X
eq→ (ω2→f-iso X lt) {x} ⟪ ωx , ⟪ ωx1 , iso ⟫ ⟫ = le00 where
    le00 : odef X x
    le00 = subst (λ k → odef X k) &iso ( ω→2f≡i1 _ _ ωx1 lt  (iso ωx1)  )
eq← (ω2→f-iso X lt) {x} Xx = ⟪ subst (λ k → odef infinite k) &iso le02  , ⟪ le02 , le01 ⟫ ⟫ where
    le02 : infinite ∋ * x
    le02 = power→ infinite _ lt (subst (λ k → odef X k) (sym &iso) Xx) 
    le01 : (wx : odef infinite (& (* x))) → ω2→f X lt (ω→nat (* x) wx) ≡ i1
    le01 wx   with ODC.∋-p O X (nat→ω (ω→nat _ wx) )
    ... | yes p  = refl
    ... | no ¬p  = ⊥-elim ( ¬p (subst (λ k → odef X k ) le03 Xx )) where
        le03 :  x ≡ & (nat→ω (ω→nato wx))
        le03 = subst₂ (λ j k → j ≡ k ) &iso refl (cong (&) (sym ( nat→ω-iso wx ) ) )

fω→2-iso : (f : Nat → Two) → ω2→f ( fω→2 f ) (ω2∋f f) ≡ f
fω→2-iso f = f-extensionality (λ x → le01 x ) where
    le01 : (x : Nat) → ω2→f (fω→2 f) (ω2∋f f) x ≡ f x
    le01 x with  ODC.∋-p O (fω→2 f) (nat→ω x) 
    le01 x | yes p = subst (λ k → i1 ≡ f k ) (ω→nat-iso0 x (proj1 (proj2 p)) (trans *iso *iso)) (sym ((proj2 (proj2 p)) le02)) where
        le02 :  infinite-d (& (* (& (nat→ω x))))
        le02 = proj1 (proj2 p )
    le01 x | no ¬p = sym ( ¬i1→i0 le04 ) where
        le04 : ¬ f x ≡ i1
        le04 fx=1 = ¬p ⟪ ω∋nat→ω {x} , ⟪ subst (λ k → infinite-d k) (sym &iso) (ω∋nat→ω {x})  , le05 ⟫ ⟫ where
            le05 : (lt : infinite-d (& (* (& (nat→ω x))))) → f (ω→nato lt) ≡ i1
            le05 lt = trans (cong f (ω→nat-iso0 x lt (trans *iso *iso))) fx=1

