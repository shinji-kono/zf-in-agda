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
open ODC O

open import filter O
open import OPair O

record Topology  ( L : HOD ) : Set (suc n) where
   field
       OS    : HOD
       OS⊆PL :  OS ⊆ Power L
       o∩ : { p q : HOD } → OS ∋ p →  OS ∋ q      → OS ∋ (p ∩ q)
       o∪ : { P : HOD }  →  P ⊂ OS                → OS ∋ Union P
       OS∋od∅ : OS ∋ od∅
-- closed Set
   CS : HOD
   CS = record { od = record { def = λ x → (* x ⊆ L) ∧ odef OS (& ( L ＼ (* x ))) } ; odmax = osuc (& L) ; <odmax = tp02 } where
       tp02 : {y : Ordinal } → (* y ⊆ L) ∧ odef OS (& (L ＼ * y)) → y o< osuc (& L)
       tp02 {y} nop = subst (λ k → k o≤ & L ) &iso ( ⊆→o≤ (λ {x} yx → proj1 nop yx ))
   os⊆L :  {x : HOD} → OS ∋ x → x ⊆ L
   os⊆L {x} Ox {y} xy = ( OS⊆PL Ox ) _ (subst (λ k → odef k y) (sym *iso) xy  )
   cs⊆L :  {x : HOD} → CS ∋ x → x ⊆ L
   cs⊆L {x} Cx {y} xy = proj1 Cx (subst (λ k → odef k y ) (sym *iso) xy )
   CS∋L : CS ∋ L
   CS∋L = ⟪ subst (λ k → k ⊆ L) (sym *iso) (λ x → x)  , subst (λ k → odef OS (& k)) (sym lem0) OS∋od∅  ⟫ where
        lem0 : L ＼ * (& L) ≡ od∅
        lem0 = subst (λ k → L ＼ k  ≡ od∅) (sym *iso) L＼L=0
--- we may add
--     OS∋L   :  OS ∋ L

open Topology

Cl : {L : HOD} → (top : Topology L) → (A : HOD) → A ⊆ L → HOD
Cl {L} top A A⊆L = record { od = record { def = λ x → odef L x ∧ ( (c : Ordinal) → odef (CS top) c → A ⊆ * c → odef (* c) x ) } 
  ; odmax = & L ; <odmax = odef∧< } 

ClL : {L : HOD} → (top : Topology L) → {f : L ⊆ L } → Cl top L f ≡ L
ClL {L} top {f} =  ==→o≡ ( record { eq→ = λ {x} ic 
        → subst (λ k → odef k x) *iso ((proj2 ic) (& L) (CS∋L top) (subst (λ k → L ⊆ k) (sym *iso) ( λ x → x)))
    ; eq← =  λ {x} lx → ⟪ lx , ( λ c cs l⊆c → l⊆c lx) ⟫ } )

-- Subbase P
--   A set of countable intersection of P will be a base (x ix an element of the base)

data Subbase (P : HOD) : Ordinal → Set n where
   gi : {x : Ordinal } → odef P x → Subbase P x
   g∩ : {x y : Ordinal } → Subbase P x → Subbase P y → Subbase P (& (* x ∩ * y))

--
--   if y is in a Subbase, some element of P contains it 

sbp :  (P : HOD) {x : Ordinal } → Subbase P x → Ordinal
sbp P {x} (gi {y} px) = x
sbp P {.(& (* _ ∩ * _))} (g∩ sb sb₁) = sbp P sb

is-sbp :  (P : HOD) {x y : Ordinal } → (px : Subbase P x) → odef (* x) y  → odef P (sbp P px ) ∧ odef (* (sbp P px)) y
is-sbp P {x} (gi px) xy = ⟪ px , xy ⟫
is-sbp P {.(& (* _ ∩ * _))} (g∩ {x} {y} px px₁) xy = is-sbp P px (proj1 (subst (λ k → odef k _ ) *iso  xy))

--  An open set generate from a base
--
--  OS = { U ⊂ L | ∀ x ∈ U → ∃ b ∈ P →  x ∈ b ⊂ U }

record Base (L P : HOD) (u x : Ordinal) : Set n where
   field
       b   : Ordinal 
       u⊂L : * u ⊆ L
       sb  : Subbase P b
       b⊆u : * b ⊆ * u
       bx  : odef (* b) x
   x⊆L : odef L x 
   x⊆L = u⊂L (b⊆u bx)

SO : (L P : HOD) → HOD
SO L P = record { od = record { def = λ u → {x : Ordinal } → odef (* u) x → Base L P u x } ; odmax = osuc (& L) ; <odmax = tp00 } where
    tp00 :  {y : Ordinal} → ({x : Ordinal} → odef (* y) x → Base L P y x) → y o< osuc (& L)
    tp00 {y} op = subst (λ k → k o≤ & L ) &iso ( ⊆→o≤ (λ {x} yx → Base.x⊆L (op yx) )) 

record IsSubBase (L P : HOD) : Set (suc n) where
   field
       P⊆PL   : P ⊆ Power L
--  we may need these if OS ∋ L is necessary
--     p    : {x : HOD} → L ∋ x → HOD
--     Pp : {x : HOD} → {lx : L ∋ x } → P ∋ p lx
--     px   : {x : HOD} → {lx : L ∋ x } → p lx ∋ x

GeneratedTopogy : (L P : HOD) → IsSubBase L P  → Topology L
GeneratedTopogy L P isb = record { OS = SO L P ; OS⊆PL = tp00
         ; o∪ = tp02 ; o∩ = tp01 ; OS∋od∅ = tp03 } where
    tp03 : {x : Ordinal } → odef (* (& od∅)) x → Base L P (& od∅) x
    tp03 {x} 0x = ⊥-elim ( empty (* x) ( subst₂ (λ j k → odef j k ) *iso (sym &iso) 0x )) 
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

-- Product Topology

open ZFProduct

-- Product Topology is not 
--     ZFP (OS TP) (OS TQ) (box)

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

pbase⊆PL : {P Q : HOD} → (TP : Topology P) → (TQ : Topology Q) → {x : Ordinal } → BaseP TP Q x ∨ BaseQ P TQ x → odef (Power (ZFP P Q)) x
pbase⊆PL {P} {Q} TP TQ {z} (case1 record { p = p ; q = q ; op = op ; prod = prod }) = subst (λ k → odef (Power (ZFP P Q)) k ) (sym prod) tp01  where
    tp01 : odef (Power (ZFP P Q)) (& (ZFP (* p) Q))
    tp01 w wz with subst (λ k → odef k w ) *iso wz
    ... | ab-pair {a} {b} pa qb = ZFP→ (subst (λ k → odef P k ) (sym &iso) tp03 ) (subst (λ k → odef Q k ) (sym &iso) qb ) where
        tp03 : odef P a
        tp03 =  os⊆L TP (subst (λ k → odef (OS TP) k) (sym &iso) op) pa
pbase⊆PL {P} {Q} TP TQ {z} (case2 record { p = p ; q = q ; oq = oq ; prod = prod }) = subst (λ k → odef (Power (ZFP P Q)) k ) (sym prod) tp01  where
    tp01 : odef (Power (ZFP P Q)) (& (ZFP P (* q) ))
    tp01 w wz with subst (λ k → odef k w ) *iso wz
    ... | ab-pair {a} {b} pa qb = ZFP→ (subst (λ k → odef P k ) (sym &iso) pa ) (subst (λ k → odef Q k ) (sym &iso) tp03 )  where
        tp03 : odef Q b
        tp03 =  os⊆L TQ (subst (λ k → odef (OS TQ) k) (sym &iso) oq) qb

pbase : {P Q : HOD} → Topology P → Topology Q → HOD
pbase {P} {Q} TP TQ = record { od = record { def = λ x → BaseP TP Q x ∨ BaseQ P TQ x } ; odmax = & (Power (ZFP P Q)) ; <odmax = tp00 } where
    tp00 : {y : Ordinal} → BaseP TP Q y ∨ BaseQ P TQ y → y o< & (Power (ZFP P Q))
    tp00 {y} bpq = odef< ( pbase⊆PL TP TQ bpq ) 

ProductTopology : {P Q : HOD} → Topology P → Topology Q → Topology (ZFP P Q)
ProductTopology {P} {Q} TP TQ =  GeneratedTopogy (ZFP P Q) (pbase TP TQ) record { P⊆PL = pbase⊆PL TP TQ }

-- covers

record _covers_ ( P q : HOD  ) : Set n where
   field
       cover   : {x : Ordinal } → odef q x → Ordinal
       P∋cover : {x : Ordinal } → {lt : odef q  x} → odef P (cover lt)
       isCover : {x : Ordinal } → {lt : odef q  x} → odef (* (cover lt))  x

open _covers_

-- Finite Intersection Property

record FIP {L : HOD} (top : Topology L) : Set n where
   field
       limit : {X : Ordinal } → * X ⊆ CS top → * X ∋ L
          →       ( { C : Ordinal  } { x : Ordinal } → * C ⊆ * X → Subbase (* C) x → o∅ o< x ) →  Ordinal
       is-limit : {X : Ordinal } → (CX : * X ⊆ CS top ) → (XL : * X ∋ L )
          → ( fip : { C : Ordinal  } { x : Ordinal } → * C ⊆ * X → Subbase (* C) x → o∅ o< x ) 
          →  {x : Ordinal } → odef (* X) x → odef (* x) (limit CX XL fip)
   L∋limit  : {X : Ordinal } → (CX : * X ⊆ CS top ) → (XL : * X ∋ L)
          → ( fip : { C : Ordinal  } { x : Ordinal } → * C ⊆ * X → Subbase (* C) x → o∅ o< x ) 
          →  odef L (limit CX XL fip)
   L∋limit {X} CX XL fip = cs⊆L top (subst (λ k → odef (CS top) k) (sym &iso) (CX XL)) (is-limit CX XL fip XL)

-- Compact

data Finite-∪ (S : HOD) : Ordinal → Set n where
   fin-e : {x : Ordinal } → odef S x → Finite-∪ S x
   fin-∪  : {x y : Ordinal } → Finite-∪ S x → Finite-∪ S y → Finite-∪ S (& (* x ∪ * y))

record Compact  {L : HOD} (top : Topology L)  : Set n where
   field
       finCover  : {X : Ordinal } → (* X) ⊆ OS top → (* X) covers L → Ordinal
       isCover   : {X : Ordinal } → (xo : (* X) ⊆ OS top) → (xcp : (* X) covers L ) → (* (finCover xo xcp )) covers L
       isFinite  : {X : Ordinal } → (xo : (* X) ⊆ OS top) → (xcp : (* X) covers L ) → Finite-∪ (* X) (finCover xo xcp ) 

-- FIP is Compact

FIP→Compact : {L : HOD} → (top : Topology L ) → FIP top  → Compact top
FIP→Compact {L} top fip = record { finCover = finCover ; isCover = isCover1 ; isFinite = isFinite } where
   -- set of coset of X
   CX : {X : Ordinal} → * X ⊆ OS top → Ordinal
   CX {X} ox = & ( Replace' (* X) (λ z xz → L ＼  z ))
   CCX : {X : Ordinal} → (os :  * X ⊆ OS top) → * (CX os) ⊆ CS top 
   CCX {X} ox = {!!}
   -- CX has finite intersection
   CXfip : {X : Ordinal } → * X ⊆ OS top → Set n
   CXfip {X} ox =  { x C : Ordinal } → * C ⊆ * (CX ox) → Subbase (* C) x → o∅ o< x 
   Cex : {X : Ordinal } → * X ⊆ OS top → HOD
   Cex {X} ox =  record { od = record { def = λ C → { x : Ordinal } → * C ⊆ * (CX ox) → Subbase (* C) o∅ } 
       ; odmax = osuc ( & (Power L)) ; <odmax = {!!} }
   -- a counter example of fip , some CX has no finite intersection
   cex : {X : Ordinal } → * X ⊆ OS top → * X covers L → Ordinal
   cex {X} ox oc = & ( ODC.minimal O (Cex ox) fip00)  where
      fip00 : ¬ ( Cex ox =h= od∅ ) 
      fip00 cex=0 = fip03 {!!} {!!} where 
          fip03 : {x z : Ordinal } → odef (* x) z →  (¬ odef (* x) z) → ⊥
          fip03 {x} {z} xz nxz = nxz xz
          fip02 : {C x : Ordinal} → * C ⊆ * (CX ox) → Subbase (* C) x → o∅ o< x
          fip02 = {!!}
          fip01 : Ordinal
          fip01 = FIP.limit fip (CCX ox) {!!} fip02
   ¬CXfip : {X : Ordinal } → (ox : * X ⊆ OS top) → (oc : * X covers L) → * (cex ox oc) ⊆ * (CX ox) → Subbase (* (cex ox oc)) o∅ 
   ¬CXfip {X} ox oc = {!!} where
      fip04 : odef (Cex ox) (cex ox oc)
      fip04 = {!!}
   -- this defines finite cover
   finCover :  {X : Ordinal} → * X ⊆ OS top → * X covers L → Ordinal
   finCover {X} ox oc = & ( Replace' (* (cex ox oc)) (λ z xz → L ＼  z ))
       -- create Finite-∪ from cex
   isFinite : {X : Ordinal} (xo : * X ⊆ OS top) (xcp : * X covers L) → Finite-∪ (* X) (finCover xo xcp)
   isFinite = {!!}
   -- is also a cover
   isCover1 : {X : Ordinal} (xo : * X ⊆ OS top) (xcp : * X covers L) → * (finCover xo xcp) covers L
   isCover1 = {!!}


Compact→FIP : {L : HOD} → (top : Topology L ) → Compact top  → FIP top
Compact→FIP = {!!}

-- existence of Ultra Filter

open Filter

-- Ultra Filter has limit point

record UFLP {P : HOD} (TP : Topology P) {L : HOD} (LP : L ⊆ Power P ) (F : Filter {L} {P} LP )  
       (FL : filter F ∋ P) (ultra : ultra-filter F ) : Set (suc (suc n)) where
   field
       limit : Ordinal
       P∋limit : odef P limit
       is-limit : {o : Ordinal} → odef (OS TP) o → odef (* o) limit → (* o) ⊆ filter F

-- FIP is UFL

UFLP→FIP : {P : HOD} (TP : Topology P) → {L : HOD} (LP : L ⊆ Power P ) → 
   ( (F : Filter {L} {P} LP ) (FP : filter F ∋ P) (UF : ultra-filter F ) → UFLP TP LP F FP UF ) → FIP TP
UFLP→FIP {P} TP {L} LP uflp = record { limit = uf00 ; is-limit = {!!} } where
     fip : {X : Ordinal} → * X ⊆ CS TP → * X ∋ P → Set n
     fip {X} CSX XP = {C x : Ordinal} → * C ⊆ * X → Subbase (* C) x → o∅ o< x
     F : {X : Ordinal} → (CSX : * X ⊆ CS TP) → (XP : * X ∋ P ) → fip {X} CSX XP → Filter {L} {P} LP
     F = ?
     uf00 : {X : Ordinal} → (CSX : * X ⊆ CS TP) → (XP : * X ∋ P ) → fip {X} CSX XP → Ordinal
     uf00 = ?

FIP→UFLP : {P : HOD} (TP : Topology P) →  FIP TP
   →  {L : HOD} (LP : L ⊆ Power P ) (F : Filter LP ) (FP : filter F ∋ P) (UF : ultra-filter F ) → UFLP {P} TP {L} LP F FP UF
FIP→UFLP {P} TP fip {L} LP F FP UF = ?

-- product topology of compact topology is compact

Tychonoff : {P Q : HOD } → (TP : Topology P) → (TQ : Topology Q)  → Compact TP → Compact TQ   → Compact (ProductTopology TP TQ)
Tychonoff {P} {Q} TP TQ CP CQ = FIP→Compact (ProductTopology TP TQ) (UFLP→FIP (ProductTopology TP TQ) LPQ uflp ) where 
    L = pbase TP TQ
    LPQ = pbase⊆PL TP TQ
    -- Product of UFL has limit point 
    uflp : (F : Filter {pbase TP TQ} LPQ) (LF : filter F ∋ ZFP P Q) (UF : ultra-filter F)
             → UFLP (ProductTopology TP TQ) LPQ F LF UF
    uflp F LF UF = record { limit = & < ? , {!!} >  ; P∋limit = {!!} ; is-limit = {!!} } 
