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
import BAlgbra 

open BAlgbra O

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

import OPair
open OPair O

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

ω→2f : (x : HOD) → ω→2 ∋ x → Nat → Two
ω→2f x lt n with ODC.∋-p O x (nat→ω n)
ω→2f x lt n | yes p = i1
ω→2f x lt n | no ¬p = i0

fω→2-sel : ( f : Nat → Two ) (x : HOD) → Set n
fω→2-sel f x = (infinite ∋ x) ∧ ( (lt : odef infinite (&  x) ) → f (ω→nat x lt) ≡ i1 )

fω→2 : (Nat → Two) → HOD
fω→2 f = Select infinite (fω→2-sel f)

open _==_

import Axiom.Extensionality.Propositional
postulate f-extensionality : { n m : Level}  → Axiom.Extensionality.Propositional.Extensionality n m

ω2∋f : (f : Nat → Two) → ω→2 ∋ fω→2 f
ω2∋f f = power← infinite (fω→2 f) (λ {x} lt →  proj1 ((proj2 (selection {fω→2-sel f} {infinite} )) lt))

ω→2f≡i1 : (X i : HOD) → (iω : infinite ∋ i) → (lt : ω→2 ∋ X ) → ω→2f X lt (ω→nat i iω)  ≡ i1 → X ∋ i
ω→2f≡i1 X i iω lt eq with ODC.∋-p O X (nat→ω (ω→nat i iω))
ω→2f≡i1 X i iω lt eq | yes p = subst (λ k → X ∋ k ) (nat→ω-iso iω) p

open _⊆_

-- someday ...
-- postulate 
--    ω→2f-iso : (X : HOD) → ( lt : ω→2 ∋ X ) → fω→2 ( ω→2f X lt )  =h= X
--    fω→2-iso : (f : Nat → Two) → ω→2f ( fω→2 f ) (ω2∋f f) ≡ f

