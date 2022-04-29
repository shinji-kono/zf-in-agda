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

open import filter

record Topology  ( L : HOD ) : Set (suc n) where
   field
       OS    : HOD
       OS⊆PL :  OS ⊆ Power L 
       o∪ : { P : HOD }  →  P  ⊆ OS           → OS ∋ Union P
       o∩ : { p q : HOD } → OS ∋ p →  OS ∋ q  → OS ∋ (p ∩ q)

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

record LP ( L S x : HOD ) (top : Topology L) (S⊆PL :  S ⊆ Power L ) ( S∋x : S ∋ x ) : Set (suc n) where
   field
      neip   : {y : HOD} → OS top ∋ y → y ∋ x → HOD
      isNeip : {y : HOD} → (o∋y : OS top ∋ y ) → (y∋x : y ∋ x ) → ¬ ( x ≡ neip o∋y y∋x) ∧ ( y ∋ neip o∋y y∋x )
       
-- Finite Intersection Property

data Finite-∩ (S : HOD) : HOD → Set (suc n) where
   fin-∩e : {x : HOD} → S ∋ x → Finite-∩ S x
   fin-∩  : {x y : HOD} → Finite-∩ S x → Finite-∩ S y → Finite-∩ S (x ∩ y)

record FIP  ( L P : HOD ) : Set (suc n) where
   field
       fipS⊆PL :  P ⊆ Power L 
       fip≠φ : { x : HOD } → Finite-∩ P x → ¬ ( x ≡ od∅ )

-- Compact

data Finite-∪ (S : HOD) : HOD → Set (suc n) where
   fin-∪e : {x : HOD} → S ∋ x → Finite-∪ S x
   fin-∪  : {x y : HOD} → Finite-∪ S x → Finite-∪ S y → Finite-∪ S (x ∪ y)

record Compact  ( L P : HOD ) : Set (suc n) where
   field
       finCover        : {X y : HOD} → X covers P         → P ∋ y →  HOD
       isFinCover      : {X y : HOD} → (xp : X covers P ) → (P∋y : P ∋ y ) → finCover xp P∋y ∋ y
       isFininiteCover : {X y : HOD} → (xp : X covers P ) → (P∋y : P ∋ y ) → Finite-∪ X (finCover xp P∋y )

-- FIP is Compact

FIP→Compact : {L P : HOD} → Topology L → FIP L P → Compact L P
FIP→Compact = {!!}

Compact→FIP : {L P : HOD} → Topology L → Compact L P → FIP L P
Compact→FIP = {!!}

-- Product Topology

_Top⊗_ : {P Q : HOD} → Topology P → Topology Q → Topology {!!}
_Top⊗_ = {!!}

-- existence of Ultra Filter 

-- Ultra Filter has limit point

-- FIP is UFL

-- Product of UFL has limit point (Tychonoff)

