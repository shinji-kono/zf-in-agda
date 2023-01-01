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
       o∩ : { p q : HOD } → OS ∋ p →  OS ∋ q      → OS ∋ (p ∩ q)
       o∪ : { P : HOD }  →  P ⊂ OS                → OS ∋ Union P
-- closed Set
   CS : HOD
   CS = record { od = record { def = λ x → odef OS (& ( L ＼ (* x ))) } ; odmax = & L ; <odmax = tp02 } where
       tp02 : {y : Ordinal } → odef OS (& (L ＼ * y)) → y o< & L
       tp02 {y} nop = ?
   os⊆L :  {x : HOD} → OS ∋ x → x ⊆ L
   os⊆L {x} Ox {y} xy = ( OS⊆PL Ox ) _ (subst (λ k → odef k y) (sym *iso) xy  )
       -- ∈∅< ( proj1 nop )

open Topology

-- Base
-- The elements of B cover X ; For any U , V ∈ B and any point x ∈ U ∩ V there is a W ∈ B such that
-- W ⊆ U ∩ V and x ∈ W .

data Subbase (P : HOD) : Ordinal → Set n where
   gi : {x : Ordinal } → odef P x → Subbase P x
   g∩ : {x y : Ordinal } → Subbase P x → Subbase P y → Subbase P (& (* x ∩ * y))

sbp :  (P : HOD) {x : Ordinal } → Subbase P x → Ordinal
sbp P {x} (gi {y} px) = x
sbp P {.(& (* _ ∩ * _))} (g∩ sb sb₁) = sbp P sb

is-sbp :  (P : HOD) {x y : Ordinal } → (px : Subbase P x) → odef (* x) y  → odef P (sbp P px ) ∧ odef (* (sbp P px)) y
is-sbp P {x} (gi px) xy = ⟪ px , xy ⟫
is-sbp P {.(& (* _ ∩ * _))} (g∩ {x} {y} px px₁) xy = is-sbp P px (proj1 (subst (λ k → odef k _ ) *iso  xy))

--  OS = { U ⊂ L | ∀ x ∈ U → ∃ b ∈ P →  x ∈ b ⊂ U }

record Base (L P : HOD) (u x : Ordinal) : Set n where
   field
       b   : Ordinal 
       u⊂L : * u ⊆ L
       sb  : Subbase P b
       b⊆u : * b ⊆ * u
       bx  : odef (* b) x

SO : (L P : HOD) → HOD
SO L P = record { od = record { def = λ u → {x : Ordinal } → odef (* u) x → Base L P u x } ; odmax = ? ; <odmax = ? }

record IsSubBase (L P : HOD) : Set (suc n) where
   field
       P⊆PL  : P ⊆ Power L

--  we may need these if OS ∋ L is necessary
--     p    : {x : HOD} → L ∋ x → HOD
--     Pp : {x : HOD} → {lx : L ∋ x } → P ∋ p lx
--     px   : {x : HOD} → {lx : L ∋ x } → p lx ∋ x

GeneratedTopogy : (L P : HOD) → IsSubBase L P  → Topology L
GeneratedTopogy L P isb = record { OS = SO L P ; OS⊆PL = tp00
         ; o∪ = tp02 ; o∩ = tp01 } where
    tp00 : SO L P ⊆ Power L
    tp00 {u} ou x ux  with ou ux
    ... | record { b = b ; u⊂L = u⊂L ; sb = sb ; b⊆u = b⊆u ; bx = bx } = u⊂L (b⊆u bx)
    tp01 :  {p q : HOD} → SO L P ∋ p → SO L P ∋ q → SO L P ∋ (p ∩ q)
    tp01 {p} {q} op oq {x} ux =  record { b = b ; u⊂L = subst (λ k → k ⊆ L) (sym *iso) ul  
      ; sb = g∩ (Base.sb (op px)) (Base.sb (oq qx))   ; b⊆u = tp08 ; bx = tp14 } where
        px : odef (* (& p)) x
        px = subst (λ k → odef k x ) (sym *iso) ( proj1 (subst (λ k → odef k _ ) *iso ux ) )
        qx : odef (* (& q)) x
        qx = subst (λ k → odef k x ) (sym *iso) ( proj2 (subst (λ k → odef k _ ) *iso ux ) )
        b : Ordinal
        b = & (* (Base.b (op px)) ∩ * (Base.b (oq qx)))
        tp08 :  * b ⊆ * (& (p ∩ q) )
        tp08 =  subst₂ (λ j k → j ⊆ k ) (sym *iso)  (sym *iso) (⊆∩-dist {(* (Base.b (op px)) ∩ * (Base.b (oq qx)))} {p} {q} tp09 tp10 ) where 
             tp11 : * (Base.b (op px))  ⊆ * (& p )
             tp11 = Base.b⊆u (op px)
             tp12 : * (Base.b (oq qx))  ⊆ * (& q )
             tp12 = Base.b⊆u (oq qx)
             tp09 : (* (Base.b (op px)) ∩ * (Base.b (oq qx))) ⊆ p 
             tp09 = ⊆∩-incl-1 {* (Base.b (op px))} {* (Base.b (oq qx))} {p} (subst (λ k → (* (Base.b (op px))) ⊆ k ) *iso tp11)
             tp10 : (* (Base.b (op px)) ∩ * (Base.b (oq qx))) ⊆ q 
             tp10 = ⊆∩-incl-2 {* (Base.b (oq qx))} {* (Base.b (op px))} {q} (subst (λ k → (* (Base.b (oq qx))) ⊆ k ) *iso tp12)
        tp14 : odef (* (& (* (Base.b (op px)) ∩ * (Base.b (oq qx))))) x
        tp14 = subst (λ k → odef k x ) (sym *iso) ⟪ Base.bx (op px) , Base.bx (oq qx) ⟫
        ul :  (p ∩ q) ⊆ L
        ul = subst (λ k → k ⊆ L ) *iso (λ {z} pq →  (Base.u⊂L (op px)) (pz pq) )  where
            pz : {z : Ordinal } → odef (* (& (p ∩ q))) z → odef (* (& p)) z
            pz {z} pq = subst (λ k → odef k z ) (sym *iso) ( proj1 (subst (λ k → odef k _ ) *iso pq ) )
    tp02 : { q : HOD} → q ⊂ SO L P → SO L P ∋ Union q
    tp02 {q} q⊂O {x} ux with subst (λ k → odef k x) *iso ux
    ... | record { owner = y ; ao = qy ; ox = yx } with proj2 q⊂O qy yx
    ... | record { b = b ; u⊂L = u⊂L ; sb = sb ; b⊆u = b⊆u ; bx = bx } = record { b = b ; u⊂L = subst (λ k → k ⊆ L) (sym *iso) tp04 
           ; sb = sb ; b⊆u = subst ( λ k → * b ⊆ k ) (sym *iso) tp06  ; bx = bx } where
        tp05 :  Union q ⊆ L
        tp05 {z} record { owner = y ; ao = qy ; ox = yx } with proj2 q⊂O qy yx
        ... | record { b = b ; u⊂L = u⊂L ; sb = sb ; b⊆u = b⊆u ; bx = bx } 
           = IsSubBase.P⊆PL isb (proj1 (is-sbp P sb bx )) _ (proj2 (is-sbp P sb bx ))
        tp04 :  Union q ⊆ L
        tp04 = tp05 
        tp06 : * b ⊆ Union q
        tp06 {z} bz = record { owner = y ; ao = qy ; ox = b⊆u bz  } 

-- covers

record _covers_ ( P q : HOD  ) : Set (suc n) where
   field
       cover   : {x : HOD} → q ∋ x → HOD
       P∋cover : {x : HOD} → {lt : q ∋ x} → P ∋ cover lt
       isCover : {x : HOD} → {lt : q ∋ x} → cover lt ∋ x

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
       p q : Ordinal
       op : odef (OS TP) p
       prod : x ≡ & (ZFP (* p) Q )

record BaseQ (P : HOD) {Q : HOD} (TQ : Topology Q ) (x : Ordinal) : Set n where
   field
       p q  : Ordinal
       oq : odef (OS TQ) q
       prod : x ≡ & (ZFP P (* q ))

-- box : HOD
-- box = ZFP (OS TP) (OS TQ)

base : {P Q : HOD} → Topology P → Topology Q → HOD
base {P} {Q} TP TQ = record { od = record { def = λ x → BaseP TP Q x ∨ BaseQ P TQ x } ; odmax = & (ZFP P Q) ; <odmax = ? }

_Top⊗_ : {P Q : HOD} → Topology P → Topology Q → Topology (ZFP P Q)
_Top⊗_ {P} {Q} TP TQ =  GeneratedTopogy (ZFP P Q) (base TP TQ) record { P⊆PL = tp00 } where
    tp00 : base TP TQ ⊆ Power (ZFP P Q)
    tp00 {z} (case1 record { p = p ; q = q ; op = op ; prod = prod }) = subst (λ k → odef (Power (ZFP P Q)) k ) (sym prod) tp01  where
        tp01 : odef (Power (ZFP P Q)) (& (ZFP (* p) Q))
        tp01 w wz with subst (λ k → odef k w ) *iso wz
        ... | ab-pair {a} {b} pa qb = ZFP→ (subst (λ k → odef P k ) (sym &iso) tp03 ) (subst (λ k → odef Q k ) (sym &iso) qb ) where
            tp03 : odef P a
            tp03 =  os⊆L TP (subst (λ k → odef (OS TP) k) (sym &iso) op) pa
    tp00 {z} (case2 record { p = p ; q = q ; oq = oq ; prod = prod }) = subst (λ k → odef (Power (ZFP P Q)) k ) (sym prod) tp01  where
        tp01 : odef (Power (ZFP P Q)) (& (ZFP P (* q) ))
        tp01 w wz with subst (λ k → odef k w ) *iso wz
        ... | ab-pair {a} {b} pa qb = ZFP→ (subst (λ k → odef P k ) (sym &iso) pa ) (subst (λ k → odef Q k ) (sym &iso) tp03 )  where
            tp03 : odef Q b
            tp03 =  os⊆L TQ (subst (λ k → odef (OS TQ) k) (sym &iso) oq) qb

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
    uflp : {L : HOD} (LPQ : L ⊆ Power (ZFP P Q)) (F : Filter LPQ)
            (uf : ultra-filter {L} {_} {LPQ} F) → UFLP (TP Top⊗ TQ) LPQ F uf
    uflp {L} LPQ F uf = record { limit = & < * ( UFLP.limit uflpp) , ? >  ; P∋limit = ? ; is-limit = ? } where
         LP : (L : HOD ) (LPQ : L ⊆ Power (ZFP P Q)) → HOD
         LP L LPQ = Replace' L ( λ x lx → Replace' x ( λ z xz → * ( zπ1 (LPQ lx (& z) (subst (λ k → odef k (& z)) (sym *iso) xz )))) )
         LPP : (L : HOD) (LPQ : L ⊆ Power (ZFP P Q)) → LP L LPQ ⊆ Power P
         LPP L LPQ record { z = z ; az = az ; x=ψz = x=ψz } w xw = tp02 (subst (λ k → odef k w)
           (subst₂ (λ j k → j ≡ k) refl *iso (cong (*) x=ψz) )  xw) where
             tp02 : Replace' (* z) (λ z₁ xz → * (zπ1 (LPQ (subst (odef L) (sym &iso) az) (& z₁) (subst (λ k → odef k (& z₁)) (sym *iso) xz)))) ⊆ P
             tp02 record { z = z1 ; az = az1 ; x=ψz = x=ψz1 } = subst (λ k → odef P k ) (trans (sym &iso) (sym x=ψz1)  )
                  (zp1 (LPQ (subst (λ k → odef L k) (sym &iso) az) _ (tp03 az1 ))) where
                    tp03 : odef (* z) z1 →  odef (* (& (* z))) (& (* z1))
                    tp03 lt = subst (λ k → odef k (& (* z1))) (sym *iso) (subst (odef (* z)) (sym &iso) lt)
         FP : Filter (LPP L LPQ)
         FP = record { filter = LP (filter F) (λ x → LPQ (f⊆L F x )) ; f⊆L = tp04 ; filter1 = ? ; filter2 = ? } where
             tp04 : LP (filter F) (λ x → LPQ (f⊆L F x )) ⊆ LP L LPQ
             tp04 record { z = z ; az = az ; x=ψz = x=ψz } = record { z = z ; az = f⊆L F az ; x=ψz = ? }
         uFP : ultra-filter FP
         uFP = record { proper = ? ; ultra = ? }
         uflpp : UFLP {P} TP {LP L LPQ} (LPP L LPQ) FP uFP
         uflpp = FIP→UFLP TP (Compact→FIP TP CP) (LPP L LPQ) FP uFP
         LQ : HOD
         LQ = Replace' L ( λ x lx → Replace' x ( λ z xz → * ( zπ2 (LPQ lx (& z) (subst (λ k → odef k (& z)) (sym *iso) xz )))) )
         LQQ : LQ ⊆ Power Q
         LQQ = ?

