{-# OPTIONS --cubical-compatible --safe #-}
open import Level
open import Ordinals
open import logic
open import Relation.Nullary

open import Level
open import Ordinals
import HODBase
import OD
open import Relation.Nullary
module VL {n : Level } (O : Ordinals {n} ) (HODAxiom : HODBase.ODAxiom O)  (ho< : OD.ODAxiom-ho< O HODAxiom ) where

open import  Relation.Binary.PropositionalEquality hiding ( [_] )
open import Data.Empty

import OrdUtil

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


open import Relation.Nullary
open import Relation.Binary
open import Data.Empty
open import Relation.Binary
open import Relation.Binary.Core
open import  Relation.Binary.PropositionalEquality
open import Data.Nat renaming ( zero to Zero ; suc to Suc ;  ℕ to Nat ; _⊔_ to _n⊔_ )


-- The cumulative hierarchy 
--    V 0 := ∅ 
--    V α + 1 := P ( V α ) 
--    V α := ⋃ { V β | β < α }

V1 : (x : Ordinal ) → ( ( y : Ordinal) → y o< x → HOD )  → HOD
V1 x V0 with trio< x o∅
V1 x V0 | tri< a ¬b ¬c = ⊥-elim ( ¬x<0 a)
V1 x V0 | tri≈ ¬a refl ¬c = Ord o∅
V1 x V0 | tri> ¬a ¬b c with Oprev-p  x
V1 x V0 | tri> ¬a ¬b c | yes p = Power ( V0 (Oprev.oprev p ) (subst (λ k → _ o< k) (Oprev.oprev=x  p) <-osuc ))
V1 x V0 | tri> ¬a ¬b c | no ¬p = 
    record { od = record { def = λ y → (y o< x ) ∧ ((lt : y o< x ) →  odef (V0 y lt) x ) } ; odmax = x; <odmax = λ {x} lt → proj1 lt }

record VOrd (x : Ordinal) : Set n where
   field 
     β : Ordinal
     ov : odef (TransFinite  V1 β) x 

V : OD
V = record { def = λ x → VOrd x }

record Vn : Set n where
   field
     x  : Ordinal
     β  : Ordinal
     ov : odef (TransFinite  V1 β) x 

-- Vn∅ : Vn
-- Vn∅ = record { x = o∅ ; β = o∅ ; ov = ? }

-- vsuc : Vn → Vn
-- vsuc v = ?

-- v< : Vn → Vn → Set n
-- v< x y = ?

-- IsVOrd : IsOrdinals Vn Vn∅ vsuc ?
-- IsVOrd = ?

