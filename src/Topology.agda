open import Level
open import Ordinals
module Topology {n : Level } (O : Ordinals {n})   where

open import zf
open import logic
open _∧_
open _∨_
open Bool

import OD 
open import Relation.Nullary 
open import Data.Empty 
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality
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
open ODC O

open import filter O
open import OPair O


record Topology  ( L : HOD ) : Set (suc n) where
   field
       OS    : HOD
       OS⊆PL :  OS ⊆ Power L 
       o∪ : { P : HOD }  →  P  ⊆ OS           → OS ∋ Union P
       o∩ : { p q : HOD } → OS ∋ p →  OS ∋ q  → OS ∋ (p ∩ q)
-- closed Set
   CS : HOD
   CS = record { od = record { def = λ x → odef OS (& ( L ＼ (* x ))) } ; odmax = & L ; <odmax = tp02 } where
       tp02 : {y : Ordinal } → odef OS (& (L ＼ * y)) → y o< & L
       tp02 {y} nop = ?
       -- ∈∅< ( proj1 nop )

open Topology


record _covers_ ( P q : HOD  ) : Set (suc n) where
   field
       cover   : {x : HOD} → q ∋ x → HOD
       P∋cover : {x : HOD} → {lt : q ∋ x} → P ∋ cover lt
       isCover : {x : HOD} → {lt : q ∋ x} → cover lt ∋ x

-- Base
-- The elements of B cover X ; For any U , V ∈ B and any point x ∈ U ∩ V there is a W ∈ B such that 
-- W ⊆ U ∩ V and x ∈ W .

data genTop (P : HOD) : HOD → Set (suc n) where
   gi : {x : HOD} → P ∋ x → genTop P x
   g∩ : {x y : HOD} → genTop P x → genTop P y → genTop P (x ∩ y)
   g∪ : {Q x : HOD} → Q ⊆ P → genTop P (Union Q)

-- Limit point

record LP { L : HOD}  (top : Topology L) ( S x : HOD ) (S⊆PL :  S ⊆ Power L ) ( S∋x : S ∋ x ) : Set (suc n) where
   field
      neip   : {y : HOD} → OS top ∋ y → y ∋ x → HOD
      isNeip : {y : HOD} → (o∋y : OS top ∋ y ) → (y∋x : y ∋ x ) → ¬ ( x ≡ neip o∋y y∋x) ∧ ( y ∋ neip o∋y y∋x )
       
-- Finite Intersection Property

data Finite-∩ (S : HOD) : HOD → Set (suc n) where
   fin-e : {x : HOD} → S ∋ x → Finite-∩ S x
   fin-∩ : {x y : HOD} → Finite-∩ S x → Finite-∩ S y → Finite-∩ S (x ∩ y)

record FIP {L : HOD} (top : Topology L) : Set (suc n) where
   field
       fipS⊆PL :  L ⊆ CS top
       fip≠φ : { x : HOD } → Finite-∩ L x → ¬ ( x ≡ od∅ )

-- Compact

data Finite-∪ (S : HOD) : HOD → Set (suc n) where
   fin-e : {x : HOD} → S ∋ x → Finite-∪ S x
   fin-∪  : {x y : HOD} → Finite-∪ S x → Finite-∪ S y → Finite-∪ S (x ∪ y)

record Compact  {L : HOD} (top : Topology L)  : Set (suc n) where
   field
       finCover  : {X : HOD} → X ⊆ OS top → X covers L → HOD
       isCover   : {X : HOD} → (xo : X ⊆ OS top) → (xcp : X covers L ) → (finCover xo xcp ) covers L
       isFinite  : {X : HOD} → (xo : X ⊆ OS top) → (xcp : X covers L ) → Finite-∪ X (finCover xo xcp  )

-- FIP is Compact

FIP→Compact : {L : HOD} → (top : Topology L ) → FIP top  → Compact top 
FIP→Compact {L} TL fip = record { finCover = ? ; isCover = ? ; isFinite = ? }

Compact→FIP : {L : HOD} → (top : Topology L ) → Compact top  → FIP top 
Compact→FIP = {!!}

-- Product Topology

open ZFProduct 

record BaseP {P : HOD} (TP : Topology P ) (Q : HOD) (x : Ordinal) : Set n where
   field
       p : Ordinal
       q : Ordinal
       op : odef (OS TP) p
       qq : odef Q q
       prod : x ≡ & < * p , * q >

record BaseQ (P : HOD) {Q : HOD} (TQ : Topology Q ) (x : Ordinal) : Set n where
   field
       p : Ordinal
       q : Ordinal
       oq : odef (OS TQ) q
       pp : odef P p
       prod : x ≡ & < * p , * q >

_Top⊗_ : {P Q : HOD} → Topology P → Topology Q → Topology (ZFP P Q)
_Top⊗_ {P} {Q} TP TQ = record {
       OS    = POS
    ;  OS⊆PL = ?
    ;  o∪ = ?
    ;  o∩ = ?
  } where
        box : HOD
        box = ZFP (OS TP) (OS TQ) 
        --  B : (OS P ∋ x →  proj⁻¹ x ) ∨ (OS Q ∋ y  →  proj⁻¹ y )
        --  U ⊂ ZFP P Q  ∧ ( U ∋ ∀ x → B ∋ ∃ b → b ∋ x ∧  b ⊂ U )
        base : HOD
        base = record { od = record { def = λ x → BaseP TP Q x ∨ BaseQ P TQ x } ; odmax = & (ZFP P Q) ; <odmax = ? }
        POS : HOD
        POS = record { od = record { def = λ x → {b : Ordinal } → odef (Power base) b ∧ odef (Union (* b)) x } 
            ; odmax = & (ZFP P Q) ; <odmax = ? }

-- existence of Ultra Filter 

open Filter 

-- Ultra Filter has limit point

record UFLP {P : HOD} (TP : Topology P) {L : HOD} (LP : L ⊆ Power P ) (F : Filter LP )  (uf : ultra-filter {L} {P} {LP} F) : Set (suc (suc n)) where
   field
       limit : Ordinal
       P∋limit : odef P limit
       is-limit : {o : Ordinal} → odef (OS TP) o → odef (* o) limit → (* o) ⊆ filter F

-- FIP is UFL

FIP→UFLP : {P : HOD} (TP : Topology P) →  FIP TP 
   →  {L : HOD} (LP : L ⊆ Power P ) (F : Filter LP )  (uf : ultra-filter {L} {P} {LP} F) → UFLP TP LP F uf 
FIP→UFLP {P} TP fip {L} LP F uf = record { limit = ? ; P∋limit = ? ; is-limit = ? }

UFLP→FIP : {P : HOD} (TP : Topology P) → 
   ( {L : HOD} (LP : L ⊆ Power P ) (F : Filter LP )  (uf : ultra-filter {L} {P} {LP} F) → UFLP TP LP F uf ) → FIP TP 
UFLP→FIP {P} TP uflp = record { fipS⊆PL = ? ; fip≠φ = ? }

-- Product of UFL has limit point (Tychonoff)

Tychonoff : {P Q : HOD } → (TP : Topology P) → (TQ : Topology Q)  → Compact TP → Compact TQ   → Compact (TP Top⊗ TQ)
Tychonoff {P} {Q} TP TQ CP CQ = FIP→Compact (TP Top⊗ TQ) (UFLP→FIP (TP Top⊗ TQ) uflp ) where
    uflp : {L : HOD} (LP : L ⊆ Power (ZFP P Q)) (F : Filter LP)
            (uf : ultra-filter {L} {_} {LP} F) → UFLP (TP Top⊗ TQ) LP F uf
    uflp {L} LP F uf = record { limit = ? ; P∋limit = ? ; is-limit = ? }






