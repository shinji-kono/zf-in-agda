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
open import Data.Unit
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
V1 x V0 | tri> ¬a ¬b c | yes0 p = Power ( V0 (Oprev.oprev p ) (subst (λ k → _ o< k) (Oprev.oprev=x  p) <-osuc ))
V1 x V0 | tri> ¬a ¬b c | no0 ¬p = 
    record { od = record { def = λ y → (y o< x ) ∧ ((lt : y o< x ) →  odef (V0 y lt) x ) } ; odmax = x; <odmax = λ {x} lt → proj1 lt }

record VOrd (x : Ordinal) : Set n where
   field 
     β : Ordinal
     ov : (& (TransFinite {λ x → HOD } V1 β)) ≡ x 

V : OD
V = record { def = λ x → VOrd x }

-- V=Ord : V == Ords
--  This is not true, there may be an ordinal which cannot be reached by Power or Union

-- 
-- record ODElement (A : OD) : Set n where
--    field
--       elt : Ordinal
--       A∋elt : HODBase.OD.def A elt
-- 
-- lem-V03 : (x : Ordinal) → TransFinite {λ x → HOD } V1 x ⊆ Ord x
-- lem-V03 = ?
-- 
-- lem-V00 : & (TransFinite V1 o∅) ≡ o∅
-- lem-V00 = Ordinals.inOrdinal.TransFinite0 O {λ x → & (TransFinite V1 o∅) ≡ o∅ } lem00 o∅ where
--    lem00 : (x : Ordinal) → ((y : Ordinal) → y o< x → & (TransFinite V1 o∅) ≡ o∅) → & (TransFinite V1 o∅) ≡ o∅ 
--    lem00 x prev with trio< x o∅
--    ... | tri< a ¬b ¬c = ⊥-elim (¬x<0 a)
--    ... | tri≈ ¬a refl ¬c = trans (==→o≡ ?  ) ord-od∅
--    ... | tri> ¬a ¬b c with Oprev-p  x
--    ... | yes0 yy = {! !}
--    ... | no0 nn = {! !}
-- 
-- lem-V01 : (x y : Ordinal) → x o< y → (& (TransFinite V1 x)) o< (& (TransFinite V1 y))  
-- lem-V01 = ?
-- 
-- lem-V02 : (v : ODElement V) → ODElement V
-- lem-V02 = ?
-- 
-- VOrdinal : Ordinals {n}
-- VOrdinal = record {
--      Ordinal = ODElement V
--    ; o∅ = record { elt = o∅ ; A∋elt = record { β = o∅ ; ov = ? } }
--    ; osuc = ?
--    ; _o<_ = ?
--    ; isOrdinal = record {
--          ordtrans = ?
--      ;   trio<    = ?
--      ;   ¬x<0     = ?
--      ;   <-osuc   = ?
--      ;   osuc-≡<  = ?
--      ;   Oprev-p  = ?
--      ;   o<-irr   = ?
--      ;   TransFinite = ?
--      } }
-- 
-- 
-- VHODAxiom : HODBase.ODAxiom VOrdinal
-- VHODAxiom = ?
-- 
-- -- V is an Ordinal
-- --  and ODAxiom can be constructed?
-- 
-- -- record Vn : Set n where
-- --    field
-- --      x  : Ordinal
-- --      β  : Ordinal
-- --      ov : odef (TransFinite  V1 β) x 
-- 
-- -- Vn∅ : Vn
-- -- Vn∅ = record { x = o∅ ; β = o∅ ; ov = ? }
-- 
-- -- vsuc : Vn → Vn
-- -- vsuc v = ?
-- 
-- -- v< : Vn → Vn → Set n
-- -- v< x y = ?
-- 
-- -- IsVOrd : IsOrdinals Vn Vn∅ vsuc ?
-- -- IsVOrd = ?
-- 
