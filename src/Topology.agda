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
module Topology {n : Level } (O : Ordinals {n} ) (HODAxiom : HODBase.ODAxiom O)  (ho< : OD.ODAxiom-ho< O HODAxiom )
       (AC : OD.AxiomOfChoice O HODAxiom ) where


open import  Relation.Binary.PropositionalEquality hiding ( [_] )
open import Relation.Binary.Definitions

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

open AxiomOfChoice AC
open import ODC O HODAxiom AC as ODC

open import Level
open import Ordinals

import filter 

open import Relation.Nullary 
-- open import Relation.Binary hiding ( _⇔_ )
open import Data.Empty 
open import Relation.Binary.PropositionalEquality
open import Data.Nat renaming ( zero to Zero ; suc to Suc ;  ℕ to Nat ; _⊔_ to _n⊔_ ) 
import BAlgebra 

open import ZProduct O HODAxiom ho<
open import filter O HODAxiom ho< AC

import Relation.Binary.Reasoning.Setoid as EqHOD

LDec : (L : HOD) (P : HOD) → P ⊆ L → (x : HOD) → Dec (x ∈ P)
LDec L P _ x = ∋-p P x

record Topology  ( L : HOD ) : Set (suc n) where
   field
       OS    : HOD
       OS⊆PL :  OS ⊆ Power L
       o∩ : { p q : HOD } → OS ∋ p →  OS ∋ q      → OS ∋ (p ∩ q)
       o∪ : { P : HOD }  →  P ⊆ OS                → OS ∋ Union P
       OS∋od∅ : OS ∋ od∅ -- OS ∋ Union od∅ 
--- we may add
--     OS∋L   :  OS ∋ L
-- closed Set
   open BAlgebra O HODAxiom ho< L (LDec L)
   CS : HOD
   CS = record { od = record { def = λ x → (* x ⊆ L) ∧ odef OS (& ( L ＼ (* x ))) } ; odmax = osuc (& L) ; <odmax = tp02 } where
       tp02 : {y : Ordinal } → (* y ⊆ L) ∧ odef OS (& (L ＼ * y)) → y o< osuc (& L)
       tp02 {y} nop = subst (λ k → k o≤ & L ) &iso ( ⊆→o≤ (λ {x} yx → proj1 nop yx ))
   os⊆L :  {x : HOD} → OS ∋ x → x ⊆ L
   os⊆L {x} Ox {y} xy = ( OS⊆PL Ox ) _ (eq← *iso xy)
   cs⊆L :  {x : HOD} → CS ∋ x → x ⊆ L
   cs⊆L {x} Cx {y} xy = proj1 Cx (eq← *iso xy)
   CS∋L : CS ∋ L
   CS∋L = ⟪ (λ lt → eq→ *iso lt)  , subst (λ k → odef OS k) (sym lem0) OS∋od∅  ⟫ where
        lem0 : & (L ＼ * (& L)) ≡ & od∅
        lem0 = ==→o≡ ( ==-trans (＼-cong L L (* (& L)) L ==-refl *iso ) L＼L=0 )
   CS⊆PL :  CS ⊆ Power L
   CS⊆PL {x} Cx y xy = proj1 Cx xy
   P＼CS=OS : {cs : HOD} → CS ∋ cs →  OS ∋ ( L ＼ cs )
   P＼CS=OS {cs} ⟪ cs⊆L , olcs  ⟫ = subst (λ k → odef OS k) (==→o≡ (＼-cong L L (* (& cs)) cs ==-refl *iso))  olcs
   P＼OS=CS : {cs : HOD} → OS ∋ cs →  CS ∋ ( L ＼ cs )
   P＼OS=CS {os} oos = ⟪ (λ lt →  proj1 (eq→ *iso lt))
      , subst (λ k → odef OS k) (==→o≡ (==-sym (==-trans (
           ＼-cong L L (* ( & (L ＼ os))) (L ＼ os) ==-refl *iso ) (L＼Lx=x {os} (os⊆L oos)) ))) oos  ⟫


open Topology

-- Closure ( Intersection of Closed Set which include A )

Cl : {L : HOD} → (top : Topology L) → (A : HOD) → HOD
Cl {L} top A = record { od = record { def = λ x → odef L x ∧ ( (c : Ordinal) → odef (CS top) c → A ⊆ * c → odef (* c) x ) }
  ; odmax = & L ; <odmax = odef∧< }

ClL : {L : HOD} → (top : Topology L) → Cl top L  =h= L
ClL {L} top  =  record { eq→ = λ {x} ic
        → eq→ *iso ((proj2 ic) (& L) (CS∋L top) (λ lt → eq← *iso lt))
    ; eq← =  λ {x} lx → ⟪ lx , ( λ c cs l⊆c → l⊆c lx) ⟫ } 

-- Closure is Closed Set


CS∋Cl : {L : HOD} → (top : Topology L) → (A : HOD) → CS top ∋ Cl top A 
CS∋Cl {L} top A = subst (λ k → odef (CS top)  k) (==→o≡ cc00) (P＼OS=CS top UOCl-is-OS)  where
    open BAlgebra O HODAxiom ho< L (LDec L)
    OCl : HOD  -- set of open set which it not contains A 
    OCl = record { od = record { def = λ o → odef (OS top) o ∧ ( A ⊆ (L ＼ * o) ) } ; odmax = & (OS top) ; <odmax = odef∧< }
    OCl⊆OS  : OCl ⊆  OS top 
    OCl⊆OS ox  = proj1 ox
    UOCl-is-OS : OS top ∋ Union OCl
    UOCl-is-OS = o∪ top OCl⊆OS
    cc00 : (L ＼ Union OCl) =h= Cl top A
    cc00 = record { eq→ = cc01 ; eq← = cc03 } where
        cc01 : {x : Ordinal} → odef (L ＼ Union OCl) x → odef L x ∧ ((c : Ordinal) → odef (CS top) c → A ⊆ * c → odef (* c) x)
        cc01 {x} ⟪ Lx , nul ⟫ = ⟪ Lx , ( λ c cc ac → cc02 c cc ac nul ) ⟫ where 
           cc02 : (c : Ordinal) → odef (CS top) c → A ⊆ * c → ¬ odef (Union OCl) x  → odef (* c) x
           cc02 c cc ac nox with ODC.∋-p (* c) (* x)
           ... | yes y = subst (λ k → odef (* c) k) &iso y
           ... | no ncx = ⊥-elim ( nox record { owner = & ( L ＼ * c) ; ao = ⟪ proj2 cc , cc07 ⟫ ; ox = eq← *iso cc06  } ) where
                cc06 : odef (L ＼ * c) x 
                cc06 = ⟪ Lx , subst (λ k → ¬ odef (* c) k) &iso ncx ⟫
                cc08 : * c ⊆ L
                cc08 = cs⊆L top (subst (λ k → odef (CS top) k ) (sym &iso) cc )
                cc09 : (L ＼ * (& (L ＼ * c))) =h= (* c)
                cc09 = begin 
                    L ＼ * (& (L ＼ * c)) ≈⟨ ＼-cong L L (* (& (L ＼ * c))) (L ＼ * c) ==-refl *iso  ⟩
                    L ＼ (L ＼ * c) ≈⟨  L＼Lx=x {* c} cc08 ⟩
                    * c ∎
                       where open EqHOD ==-Setoid
                cc07 :  A ⊆ (L ＼ * (& (L ＼ * c)))
                cc07 {z} az = eq← cc09 ( ac az ) 
        cc03 : {x : Ordinal}  → odef L x ∧ ((c : Ordinal) → odef (CS top) c → A ⊆ * c → odef (* c) x) → odef (L ＼ Union OCl) x
        cc03 {x} ⟪ Lx , ccx ⟫ = ⟪ Lx , cc04 ⟫ where
           -- if x is in Cl A, it is in some c : CS, OCl says it is not , i.e. L ＼ o ∋ x, so it is in (L ＼ Union OCl) x
           cc04 : ¬ odef (Union OCl) x
           cc04 record { owner = o ; ao = ⟪ oo , A⊆L-o ⟫ ; ox = ox } = proj2 ( eq→ *iso cc05) ox  where
                cc05 : odef (* (& (L ＼ * o))) x
                cc05 = ccx (& (L ＼ * o)) (P＼OS=CS top (subst (λ k → odef (OS top) k) (sym &iso) oo)) (λ lt → eq← *iso (A⊆L-o lt)) 

CS∋x→Clx=x : {L x : HOD} → (top : Topology L) → CS top ∋ x → Cl top x =h= x 
CS∋x→Clx=x {L} {x} top cx = record { eq→ = cc10 ; eq← = cc11 } where
    cc10 : {y : Ordinal} → odef L y ∧ ((c : Ordinal) → odef (CS top) c → x ⊆ * c → odef (* c) y) → odef x y
    cc10 {y} ⟪ Ly , cc ⟫ = eq→ *iso ( cc (& x) cx (λ {z} xz → eq← *iso xz  ) )
    cc11 : {y : Ordinal} → odef x y → odef L y ∧ ((c : Ordinal) → odef (CS top) c → x ⊆ * c → odef (* c) y) 
    cc11 {y} xy = ⟪ cs⊆L top cx xy , (λ c oc x⊆c → x⊆c xy ) ⟫

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
is-sbp P {.(& (* _ ∩ * _))} (g∩ {x} {y} px px₁) xy = is-sbp P px (proj1 (eq→ *iso xy))

sb⊆ : {P Q : HOD} {x : Ordinal } → P ⊆ Q → Subbase P x → Subbase Q x
sb⊆ {P} {Q} P⊆Q (gi px) = gi (P⊆Q px)
sb⊆ {P} {Q} P⊆Q (g∩ px qx) = g∩ (sb⊆ P⊆Q px) (sb⊆ P⊆Q qx)

--  An open set generate from a base
--
--  OS = { U ⊆ L | ∀ x ∈ U → ∃ b ∈ P →  x ∈ b ⊆ U }

record Base (L P : HOD) (u x : Ordinal) : Set n where
   field
       b   : Ordinal
       u⊆L : * u ⊆ L
       sb  : Subbase P b
       b⊆u : * b ⊆ * u
       bx  : odef (* b) x
   x⊆L : odef L x
   x⊆L = u⊆L (b⊆u bx)

SO : (L P : HOD) → HOD
SO L P = record { od = record { def = λ u → {x : Ordinal } → odef (* u) x → Base L P u x } ; odmax = osuc (& L) ; <odmax = tp00 } where
    tp00 :  {y : Ordinal} → ({x : Ordinal} → odef (* y) x → Base L P y x) → y o< osuc (& L)
    tp00 {y} op = subst (λ k → k o≤ & L ) &iso ( ⊆→o≤ (λ {x} yx → Base.x⊆L (op yx) ))

record IsSubBase (L P : HOD) : Set (suc n) where
   field
       P⊆PL   : P ⊆ Power L
--  we may need these if OS ∋ L is necessary
--     p    : {x : HOD} → L ∋ x → HOD
--     Pp   : {x : HOD} → {lx : L ∋ x } → P ∋ p lx
--     px   : {x : HOD} → {lx : L ∋ x } → p lx ∋ x

InducedTopology : (L P : HOD) → IsSubBase L P  → Topology L
InducedTopology L P isb = record { OS = SO L P ; OS⊆PL = tp00
         ; o∪ = tp02 ; o∩ = tp01 ; OS∋od∅ = tp03 } where
    tp03 : {x : Ordinal } → odef (* (& od∅)) x → Base L P (& od∅) x
    tp03 {x} 0x = ⊥-elim ( empty (* x) (eq→ *iso ( subst (λ k → odef (* (& od∅)) k ) (sym &iso) 0x )))
    tp00 : SO L P ⊆ Power L
    tp00 {u} ou x ux  with ou ux
    ... | record { b = b ; u⊆L = u⊆L ; sb = sb ; b⊆u = b⊆u ; bx = bx } = u⊆L (b⊆u bx)
    tp01 :  {p q : HOD} → SO L P ∋ p → SO L P ∋ q → SO L P ∋ (p ∩ q)
    tp01 {p} {q} op oq {x} ux =  record { b = b ; u⊆L = λ lt → ul (eq→ *iso lt)
      ; sb = g∩ (Base.sb (op px)) (Base.sb (oq qx))   ; b⊆u = tp08 ; bx = tp14 } where
        px : odef (* (& p)) x
        px = eq← *iso ( proj1 (eq→ *iso ux) )
        qx : odef (* (& q)) x
        qx = eq← *iso ( proj2 (eq→ *iso ux) )
        b : Ordinal
        b = & (* (Base.b (op px)) ∩ * (Base.b (oq qx)))
        tp08 :  * b ⊆ * (& (p ∩ q) )
        tp08 = λ lt → ( eq← *iso ((⊆∩-dist {(* (Base.b (op px)) ∩ * (Base.b (oq qx)))} {p} {q} tp09 tp10 ) (eq→ *iso lt))) where
             tp11 : * (Base.b (op px))  ⊆ * (& p )
             tp11 = Base.b⊆u (op px)
             tp12 : * (Base.b (oq qx))  ⊆ * (& q )
             tp12 = Base.b⊆u (oq qx)
             tp09 : (* (Base.b (op px)) ∩ * (Base.b (oq qx))) ⊆ p
             tp09 = ⊆∩-incl-1 {* (Base.b (op px))} {* (Base.b (oq qx))} {p} (λ lt → eq→ *iso (tp11 lt))
             tp10 : (* (Base.b (op px)) ∩ * (Base.b (oq qx))) ⊆ q
             tp10 = ⊆∩-incl-2 {* (Base.b (oq qx))} {* (Base.b (op px))} {q} (λ lt → eq→ *iso (tp12 lt))
        tp14 : odef (* (& (* (Base.b (op px)) ∩ * (Base.b (oq qx))))) x
        tp14 = eq← *iso ⟪ Base.bx (op px) , Base.bx (oq qx) ⟫
        ul :  (p ∩ q) ⊆ L
        ul = λ pq →  (Base.u⊆L (op px)) (pz (eq← *iso pq)) where
            pz : {z : Ordinal } → odef (* (& (p ∩ q))) z → odef (* (& p)) z
            pz {z} pq = eq← *iso ( proj1 (eq→ *iso pq ) )
    tp02 : { q : HOD} → q ⊆ SO L P → SO L P ∋ Union q
    tp02 {q} q⊆O {x} ux with eq→ *iso ux
    ... | record { owner = y ; ao = qy ; ox = yx } with q⊆O qy yx
    ... | record { b = b ; u⊆L = u⊆L ; sb = sb ; b⊆u = b⊆u ; bx = bx } = record { b = b ; u⊆L = λ lt → tp04 (eq→ *iso lt)
         ; sb = sb ; b⊆u = λ lt → eq← *iso (tp06 lt)  ; bx = bx } where
      tp05 :  Union q ⊆ L
      tp05 {z} record { owner = y ; ao = qy ; ox = yx } with q⊆O qy yx
      ... | record { b = b ; u⊆L = u⊆L ; sb = sb ; b⊆u = b⊆u ; bx = bx }
         = IsSubBase.P⊆PL isb (proj1 (is-sbp P sb bx )) _ (proj2 (is-sbp P sb bx )) 
      tp04 :  Union q ⊆ L
      tp04 = tp05
      tp06 : * b ⊆ Union q
      tp06 {z} bz = record { owner = y ; ao = qy ; ox = b⊆u bz  }

-- Product Topology

open ZFProduct

-- Product Topology is not
--     ZFP (OS TP) (OS TQ) (box)

-- Rectangle subset (zπ1 ⁻¹ p)
record BaseP {P : HOD} (TP : Topology P ) (Q : HOD) (x : Ordinal) : Set n where
   field
       p : Ordinal
       op : odef (OS TP) p
       prod : x ≡ & (ZFP (* p) Q )

-- Rectangle subset (zπ12⁻¹ q )
record BaseQ (P : HOD) {Q : HOD} (TQ : Topology Q ) (x : Ordinal) : Set n where
   field
       q  : Ordinal
       oq : odef (OS TQ) q
       prod : x ≡ & (ZFP P (* q ))

pbase⊆PL : {P Q : HOD} → (TP : Topology P) → (TQ : Topology Q) → {x : Ordinal } → BaseP TP Q x ∨ BaseQ P TQ x → odef (Power (ZFP P Q)) x
pbase⊆PL {P} {Q} TP TQ {z} (case1 record { p = p ; op = op ; prod = prod }) = subst (λ k → odef (Power (ZFP P Q)) k ) (sym prod) tp01  where
    tp01 : odef (Power (ZFP P Q)) (& (ZFP (* p) Q))
    tp01 w wz with eq→ *iso wz
    ... | ab-pair {a} {b} pa qb = ZFP→ (subst (λ k → odef P k ) (sym &iso) tp03 ) (subst (λ k → odef Q k ) (sym &iso) qb ) where
        tp03 : odef P a
        tp03 =  os⊆L TP (subst (λ k → odef (OS TP) k) (sym &iso) op) pa
pbase⊆PL {P} {Q} TP TQ {z} (case2 record { q = q ; oq = oq ; prod = prod }) = subst (λ k → odef (Power (ZFP P Q)) k ) (sym prod) tp01  where
    tp01 : odef (Power (ZFP P Q)) (& (ZFP P (* q) ))
    tp01 w wz with eq→ *iso wz
    ... | ab-pair {a} {b} pa qb = ZFP→ (subst (λ k → odef P k ) (sym &iso) pa ) (subst (λ k → odef Q k ) (sym &iso) tp03 )  where
        tp03 : odef Q b
        tp03 =  os⊆L TQ (subst (λ k → odef (OS TQ) k) (sym &iso) oq) qb

pbase : {P Q : HOD} → Topology P → Topology Q → HOD
pbase {P} {Q} TP TQ = record { od = record { def = λ x → BaseP TP Q x ∨ BaseQ P TQ x } ; odmax = & (Power (ZFP P Q)) ; <odmax = tp00 } where
    tp00 : {y : Ordinal} → BaseP TP Q y ∨ BaseQ P TQ y → y o< & (Power (ZFP P Q))
    tp00 {y} bpq = odef< ( pbase⊆PL TP TQ bpq )

ProductTopology : {P Q : HOD} → Topology P → Topology Q → Topology (ZFP P Q)
ProductTopology {P} {Q} TP TQ =  InducedTopology (ZFP P Q) (pbase TP TQ) record { P⊆PL = pbase⊆PL TP TQ }

-- covers  ( q ⊆ Union P )

record _covers_ ( P q : HOD  ) : Set n where
   field
       cover   : {x : Ordinal } → odef q x → Ordinal
       P∋cover : {x : Ordinal } → (lt : odef q  x) → odef P (cover lt)
       isCover : {x : Ordinal } → (lt : odef q  x) → odef (* (cover lt))  x

open _covers_

cong-covers : (P Q R S : HOD) → P =h= Q →  R =h= S → P covers R → Q covers S
cong-covers P Q R S P=Q R=S record { cover = cover ; P∋cover = P∋cover ; isCover = isCover } 
     = record { cover = λ {x} px → cover (eq← R=S px) ; P∋cover = λ {x} px → eq→ P=Q (P∋cover (eq← R=S px)) 
       ; isCover = λ {x} px → isCover (eq← R=S px) }


-- Finite Intersection Property

record FIP {L : HOD} (top : Topology L) : Set n where
   field
       limit : {X : Ordinal } → * X ⊆ CS top
          →       ( { x : Ordinal } → Subbase (* X) x → o∅ o< x ) →  Ordinal
       is-limit : {X : Ordinal } → (CX : * X ⊆ CS top )
          → ( fip :  { x : Ordinal } → Subbase (* X) x → o∅ o< x )
          →  {x : Ordinal } → odef (* X) x → odef (* x) (limit CX fip)
   L∋limit  : {X : Ordinal } → (CX : * X ⊆ CS top )
          → ( fip : { x : Ordinal } → Subbase (* X) x → o∅ o< x )
          →  {x : Ordinal } → odef (* X) x
          →  odef L (limit CX fip)
   L∋limit {X} CX fip {x} xx = cs⊆L top (subst (λ k → odef (CS top) k) (sym &iso) (CX xx)) (is-limit CX fip xx)

-- Compact

data Finite-∪ (S : HOD) : Ordinal → Set n where
   fin-e : Finite-∪ S o∅
   fin-i : {x : Ordinal } → odef S x  → Finite-∪ S (& ( * x , * x ))   -- an element of S
   fin-∪ : {x y : Ordinal } → Finite-∪ S x → Finite-∪ S y → Finite-∪ S (& (* x ∪ * y))
   --  Finite-∪ S y → Union y ⊆ S

record Compact  {L : HOD} (top : Topology L)  : Set n where
   field
       finCover  : {X : Ordinal } → (* X) ⊆ OS top → (* X) covers L → Ordinal
       isCover   : {X : Ordinal } → (xo : (* X) ⊆ OS top) → (xcp : (* X) covers L ) → (* (finCover xo xcp )) covers L
       isFinite  : {X : Ordinal } → (xo : (* X) ⊆ OS top) → (xcp : (* X) covers L ) → Finite-∪ (* X) (finCover xo xcp )

-- FIP is Compact

FIP→Compact : {L : HOD} → (top : Topology L ) → FIP top  → Compact top
FIP→Compact {L} top fip with trio< (& L) o∅
... | tri< a ¬b ¬c = ⊥-elim ( ¬x<0 a )
... | tri≈ ¬a b ¬c = record { finCover = λ _ _ → o∅ ; isCover = λ {X} _ xcp → fip01 xcp ; isFinite = fip00 }  where
   -- L is empty
   fip02 : {x : Ordinal } → ¬ odef L x
   fip02 {x} Lx = ⊥-elim ( o<¬≡ (sym b) (∈∅< Lx) )
   fip01 : {X : Ordinal } → (xcp : * X covers L) → (* o∅) covers L
   fip01 xcp = record { cover = λ Lx → ⊥-elim (fip02 Lx)  ; P∋cover = λ Lx → ⊥-elim (fip02 Lx)  ; isCover =  λ Lx → ⊥-elim (fip02 Lx) }
   fip00 : {X : Ordinal} (xo : * X ⊆ OS top) (xcp : * X covers L) → Finite-∪ (* X) o∅
   fip00 {X} xo xcp = fin-e 
... | tri> ¬a ¬b 0<L = record { finCover = finCover ; isCover = isCover1 ; isFinite = isFinite } where
   -- set of coset of X
   open BAlgebra O HODAxiom ho< L  (LDec L)
   CX : {X : Ordinal} → * X ⊆ OS top → Ordinal
   CX {X} ox = & ( Replace (* X) (λ z → L ＼  z ) RC＼ )
   CCX : {X : Ordinal} → (os :  * X ⊆ OS top) → * (CX os) ⊆ CS top
   CCX {X} os {x} ox with eq→ *iso ox
   ... | record { z = z ; az = az ; x=ψz = x=ψz } = ⟪ fip05 , fip06  ⟫ where --  x ≡ & (L ＼ * z)
      fip07 : z ≡ & (L ＼ * x)
      fip07 = subst₂ (λ j k → j ≡ k) &iso (cong (λ k → & ( L ＼ k )) (cong (*) (sym x=ψz))) ( ==→o≡ record { eq→ = fip09 ; eq← = fip08 } ) where
          fip08 : {x : Ordinal} → odef L x ∧ (¬ odef (* (& (L ＼ * z))) x) → odef (* z) x
          fip08 {x} ⟪ Lx , not ⟫ = double-neg-elim ( λ nz → not (eq← *iso  ⟪ Lx , nz ⟫) )   -- ( odef L x ∧ odef (* z) x → ⊥) → ⊥
          fip09 : {x : Ordinal} → odef (* z) x → odef L x ∧ (¬ odef (* (& (L ＼ * z))) x)
          fip09 {w} zw = ⟪ os⊆L top (os (subst (λ k → odef (* X) k) (sym &iso) az)) zw  , (λ lt → fip10 (eq→ *iso lt))  ⟫ where
             fip10 : ¬ (odef (L ＼ * z) w)
             fip10 ⟪ Lw , nzw ⟫ = nzw zw
      fip06 : odef (OS top) (& (L ＼ * x))
      fip06 = os ( subst (λ k → odef (* X) k ) fip07 az )
      fip05 : * x ⊆ L
      fip05 {w} xw = proj1 ( eq→ (begin
          * x ≈⟨ o≡→== x=ψz  ⟩
          * (& (  L ＼ * z )) ≈⟨ *iso ⟩
          L ＼ * z ∎ ) xw ) where
             open EqHOD ==-Setoid
   --
   --   X covres L means Intersection of (CX X) contains nothing
   --     then some finite Intersection of (CX X) contains nothing ( contraposition of FIP .i.e. CFIP)
   --     it means there is a finite cover
   --
   finCoverBase : {X : Ordinal } → * X ⊆ OS top → * X covers L →  Subbase (Replace (* X) (λ z → L ＼ z) RC＼ ) o∅
   finCoverBase {X} ox oc with p∨¬p (Subbase (Replace (* X) (λ z → L ＼ z) RC＼ ) o∅)
   ... | case1 sb = sb
   ... | case2 ¬sb = ⊥-elim (¬¬cover fip25 fip20) where
       ¬¬cover : {z : Ordinal } →  odef L z → ¬ ( {y : Ordinal } → (Xy : odef (* X) y)  → ¬ ( odef (* y) z ))
       ¬¬cover {z} Lz nc  =  nc ( P∋cover oc Lz  ) (isCover oc _ )
       -- ¬sb → we have finite intersection
       fip02 : {x : Ordinal} → Subbase (* (CX ox)) x → o∅ o< x
       fip02 {x} sc with trio< x o∅
       ... | tri< a ¬b ¬c = ⊥-elim ( ¬x<0 a )
       ... | tri> ¬a ¬b c = c
       ... | tri≈ ¬a b ¬c  = ⊥-elim (¬sb (sb⊆ (eq→ *iso)  (subst (λ k → Subbase (* (CX ox)) k ) b sc ))) 
       -- we have some intersection because L is not empty (if we have an element of L, we don't need choice)
       fip26 : odef (* (CX ox))    (& (L ＼  * ( cover oc ( x∋minimal L (0<P→ne 0<L) ) )))
       fip26 = eq← *iso record { z = cover oc (x∋minimal L (0<P→ne 0<L)) ; az = P∋cover oc (x∋minimal L (0<P→ne 0<L))  ; x=ψz = refl }
       fip25 : odef L( FIP.limit fip (CCX ox) fip02 )
       fip25 = FIP.L∋limit fip (CCX ox) fip02 fip26
       fip20 : {y : Ordinal } → (Xy : odef (* X) y)  → ¬ ( odef (* y) ( FIP.limit fip (CCX ox) fip02 ))
       fip20 {y} Xy yl = proj2 fip21 yl where
           fip22 : odef (* (CX ox)) (& ( L ＼ * y ))
           fip22 = eq← *iso record { z = y ; az = Xy ; x=ψz = refl }
           fip21 : odef (L ＼ * y) ( FIP.limit fip (CCX ox) fip02 )
           fip21 = eq→ *iso ( FIP.is-limit fip (CCX ox) fip02 fip22 )
   -- create HOD from Subbase ( finite intersection )
   finCoverSet : {X : Ordinal } → (x : Ordinal) →  Subbase (Replace (* X) (λ z → L ＼ z) RC＼ ) x → HOD
   finCoverSet {X} x (gi rx) =  ( L ＼ * x ) , ( L ＼ * x  )
   finCoverSet {X} x∩y (g∩ {x} {y} sx sy) = finCoverSet {X} x sx ∪ finCoverSet {X} y sy 
   --
   -- this defines finite cover
   finCover :  {X : Ordinal} → * X ⊆ OS top → * X covers L → Ordinal
   finCover {X} ox oc = & ( finCoverSet o∅ (finCoverBase ox oc))
   -- create Finite-∪ from finCoverSet
   isFinite : {X : Ordinal} (xo : * X ⊆ OS top) (xcp : * X covers L) → Finite-∪ (* X) (finCover xo xcp)
   isFinite {X} xo xcp = fip60 o∅ (finCoverBase xo xcp) where
        fip60 : (x : Ordinal) → (sb : Subbase (Replace (* X) (λ z → L ＼ z) RC＼ ) x ) → Finite-∪ (* X) (& (finCoverSet {X} x sb))
        fip60 x (gi rx) = subst (λ k → Finite-∪ (* X) k) fip62 (fin-i (fip61 rx)) where
           fip62 : & (* (& (L ＼ * x)) , * (& (L ＼ * x))) ≡ & ((L ＼ * x) , (L ＼ * x))
           fip62 = ==→o≡ (pair-subst2 *iso *iso )
           fip61 : odef (Replace (* X) (_＼_ L) RC＼ ) x → odef (* X) ( & ((L ＼ * x ) ))
           fip61 record { z = z1 ; az = az1 ; x=ψz = x=ψz1 } = subst (λ k → odef (* X) k) fip33 az1 where
               fip34 : * z1 ⊆ L
               fip34 {w} wz1 = os⊆L top (subst (λ k → odef (OS top) k) (sym &iso) (xo az1)) wz1
               fip33 : z1 ≡ & (L ＼ * x)
               fip33 = begin
                 z1 ≡⟨ sym &iso ⟩
                 & (* z1) ≡⟨ sym ( ==→o≡ (L＼Lx=x {* z1} fip34))  ⟩
                 & (L ＼ ( L ＼ * z1)) ≡⟨ ==→o≡ ( ＼-cong L L ( L ＼ * z1) (* (& ( L ＼ * z1))) ==-refl  (==-sym *iso) ) ⟩
                 & (L ＼ * (& ( L ＼ * z1))) ≡⟨ cong (λ k → & ( L ＼ * k )) (sym x=ψz1) ⟩
                 & (L ＼ * x ) ∎ where open ≡-Reasoning
        fip60 x∩y (g∩ {x} {y} sx sy) = subst (λ k → Finite-∪ (* X) k) fip62 ( fin-∪ (fip60 x sx)  (fip60 y sy)  ) where
               fip62 : & (* (& (finCoverSet x sx)) ∪ * (& (finCoverSet y sy))) ≡ & (finCoverSet x sx ∪ finCoverSet y sy)
               fip62 = ==→o≡ (begin
                  (* (& (finCoverSet x sx)) ∪ * (& (finCoverSet y sy))) 
                      ≈⟨ ∪-cong {* (& (finCoverSet x sx))} {finCoverSet x sx} {* (& (finCoverSet y sy))} {finCoverSet y sy} *iso *iso ⟩
                  finCoverSet x sx ∪ finCoverSet y sy ∎ ) 
                     where open EqHOD ==-Setoid
   -- is also a cover
   isCover1 : {X : Ordinal} (xo : * X ⊆ OS top) (xcp : * X covers L) → * (finCover xo xcp) covers L
   isCover1 {X} xo xcp = cong-covers _ _ _ _ (==-sym *iso) (==-trans (＼-cong L L (* o∅) od∅ ==-refl o∅==od∅)  L＼0=L)
            -- subst₂ (λ j k → j covers k ) ? (subst (λ k → L ＼ k ≡ L) ? ? ) -- L＼0=L) 
     (fip70 o∅ (finCoverBase xo xcp)) where
        fip70 : (x : Ordinal) → (sb : Subbase (Replace (* X) (λ z → L ＼ z) RC＼ ) x ) → (finCoverSet {X} x sb) covers (L ＼ * x)
        fip70 x (gi rx) = fip73 where
            fip73 : ((L ＼ * x) , (L ＼ * x)) covers (L ＼ * x)   -- obvious
            fip73 = record { cover = λ _ → & (L ＼ * x) ; P∋cover = λ _ → case1 refl 
                ; isCover = λ {x} lt → eq← *iso lt }
        fip70 x∩y (g∩ {x} {y} sx sy) = cong-covers _ _ _ _ ==-refl (＼-cong L L (* x ∩ * y) (* (& (* x ∩ * y))) ==-refl (==-sym *iso)) 
               ( fip43 {_} {L} {* x} {* y} (fip71 (fip70 x sx)) (fip72 (fip70 y sy)) ) where
            fip71 : {a b c : HOD} → a covers c →  (a ∪ b) covers c
            fip71 {a} {b} {c} cov = record { cover = cover cov ; P∋cover = λ lt → case1 (P∋cover cov lt) 
               ; isCover = isCover cov } 
            fip72 : {a b c : HOD} → a covers c →  (b ∪ a) covers c
            fip72 {a} {b} {c} cov = record { cover = cover cov ; P∋cover = λ lt → case2 (P∋cover cov lt) 
               ; isCover = isCover cov } 
            fip45 : {L a b : HOD} → (L ＼ (a ∩ b)) ⊆ ( (L ＼ a) ∪  (L ＼ b))
            fip45 {L} {a} {b} {x} Lab with ∋-p  b (* x)
            ... | yes bx = case1 ⟪ proj1 Lab , (λ ax → proj2 Lab ⟪ ax , subst (λ k → odef b k) &iso bx ⟫ )  ⟫
            ... | no ¬bx = case2 ⟪ proj1 Lab , subst (λ k → ¬ ( odef b k)) &iso ¬bx  ⟫
            fip43 : {A L a b : HOD } → A covers (L ＼ a) → A covers (L ＼ b ) → A covers ( L ＼ ( a ∩ b ) )
            fip43 {A} {L} {a} {b} ca cb = record { cover = fip44 ; P∋cover = fip46 ; isCover = fip47 } where
                fip44 :  {x : Ordinal} → odef (L ＼ (a ∩ b)) x → Ordinal
                fip44 {x} Lab with fip45 {L} {a} {b} Lab
                ... | case1 La = cover ca La
                ... | case2 Lb = cover cb Lb
                fip46 : {x : Ordinal} (lt : odef (L ＼ (a ∩ b)) x) → odef A (fip44 lt)
                fip46 {x} Lab with  fip45 {L} {a} {b} Lab
                ... | case1 La = P∋cover ca La
                ... | case2 Lb = P∋cover cb Lb
                fip47 : {x : Ordinal} (lt : odef (L ＼ (a ∩ b)) x) → odef (* (fip44 lt)) x
                fip47 {x} Lab with  fip45 {L} {a} {b} Lab
                ... | case1 La = isCover ca La
                ... | case2 Lb = isCover cb Lb



Compact→FIP : {L : HOD} → (top : Topology L ) → Compact top  → FIP top
Compact→FIP {L} top compact with trio< (& L) o∅
... | tri< a ¬b ¬c = ⊥-elim ( ¬x<0 a )
... | tri≈ ¬a L=0 ¬c = record { limit = λ {X} CX fip → o∅ ; is-limit = λ {X} CX fip xx → ⊥-elim (fip000 CX fip xx)  }  where
   -- empty L case
   --   if 0 < X then 0 < x ∧ L ∋ xfrom fip
   --   if 0 ≡ X then ¬ odef X x
   fip000 : {X x : Ordinal} (CX : * X ⊆ CS top) → ({y : Ordinal} → Subbase (* X) y → o∅ o< y) → ¬ odef (* X) x
   fip000 {X} {x} CX fip xx with trio< o∅ X
   ... | tri< 0<X ¬b ¬c = ¬∅∋ (eq→ (begin
       L ≈⟨ ==-sym *iso ⟩
       * (& L) ≈⟨ o≡→== L=0 ⟩
       * o∅   ≈⟨ o∅==od∅ ⟩
       od∅ ∎ ) (subst (λ k → odef L k ) (sym &iso) 
        ( cs⊆L top (subst (λ k → odef (CS top) k ) (sym &iso) (CX xx))  Xe ))) where
      open EqHOD ==-Setoid
      0<x : o∅ o< x
      0<x = fip (gi xx )
      e : HOD  -- we have an element of x
      e = minimal (* x) (0<P→ne (subst (λ k → o∅ o< k) (sym &iso) 0<x) )
      Xe : odef (* x) (& e)
      Xe = x∋minimal (* x) (0<P→ne (subst (λ k → o∅ o< k) (sym &iso) 0<x) )
   ... | tri≈ ¬a 0=X ¬c = ⊥-elim ( ¬∅∋ (eq→  ( begin 
           * X ≈⟨  o≡→== (sym 0=X) ⟩ 
           * o∅ ≈⟨  o∅==od∅ ⟩ 
           od∅ ∎ ) (subst (λ k → odef (* X) k ) (sym &iso) xx ) )) where open EqHOD ==-Setoid
   ... | tri> ¬a ¬b c = ⊥-elim ( ¬x<0 c )
... | tri> ¬a ¬b 0<L = record { limit = limit ; is-limit = fip00 } where
   -- set of coset of X
   open BAlgebra O HODAxiom ho< L (LDec L)
   OX : {X : Ordinal} → * X ⊆ CS top → Ordinal
   OX {X} ox = & ( Replace (* X) (λ z → L ＼  z ) RC＼)
   OOX : {X : Ordinal} → (cs :  * X ⊆ CS top) → * (OX cs) ⊆ OS top
   OOX {X} cs {x} ox with eq→ *iso ox
   ... | record { z = z ; az = az ; x=ψz = x=ψz } =  subst (λ k → odef (OS top) k) (sym x=ψz) ( P＼CS=OS top (cs comp01))  where
       comp01 : odef (* X) (& (* z))
       comp01 = subst (λ k → odef (* X) k) (sym &iso) az
   --  if all finite intersection of X contains something, 
   --  there is no finite cover. From Compactness, (OX X) is not a cover of L ( contraposition of Compact)
   --    it means there is a limit
   record NC {X : Ordinal} (CX : * X ⊆ CS top) (fip : {x : Ordinal} → Subbase (* X) x → o∅ o< x) (0<X : o∅ o< X) : Set n where
      field         -- find an element x, which is not covered (which is a limit point)
          x : Ordinal
          yx : {y : Ordinal} (Xy : odef (* X) y) →  odef (* y) x 
   has-intersection : {X : Ordinal} (CX : * X ⊆ CS top) (fip : {x : Ordinal} → Subbase (* X) x → o∅ o< x) 
      → (0<X : o∅ o< X ) →  NC CX fip 0<X
   has-intersection {X} CX fip 0<X =  intersection where
      e : HOD  -- we have an element of X
      e = minimal  (* X) (0<P→ne (subst (λ k → o∅ o< k) (sym &iso) 0<X) )
      Xe : odef (* X) (& e)
      Xe = x∋minimal (* X) (0<P→ne (subst (λ k → o∅ o< k) (sym &iso) 0<X) )
      no-cover : ¬ ( (* (OX CX)) covers L ) 
      no-cover cov = ⊥-elim (no-finite-cover (Compact.isCover compact (OOX CX) cov)) where
          -- construct Subase from Finite-∪
          fp01 : Ordinal
          fp01 = Compact.finCover compact (OOX CX) cov
          record SB (t : Ordinal) : Set n where
            field
               i : Ordinal 
               sb : Subbase (* X) (& (L ＼ * i))
               t⊆i : (L ＼ * i) ⊆  (L ＼ Union ( * t ) )
          fp02 : (t : Ordinal) → Finite-∪ (* (OX CX)) t → SB t
          fp02 t fin-e = record { i = & ( L  ＼ e) ; sb = gi (subst (λ k → odef (* X) k) fp21 Xe) ; t⊆i = fp23  } where  
              --  t ≡ o∅, no cover. Any subst of L is ok and we have e ⊆ L 
              fp22 : e ⊆ L
              fp22 {x} lt =  cs⊆L top (CX Xe) lt 
              fp21 : & e ≡ & (L ＼ * (& (L ＼ e)))
              fp21 = ==→o≡ ( ==-trans (==-sym (L＼Lx=x {e} fp22 )) (＼-cong L L (L ＼ e) (* (& (L ＼ e)))  ==-refl (==-sym *iso )))
              fp23 : (L ＼ * (& (L ＼ e))) ⊆ (L ＼ Union (* o∅))
              fp23 {x} ⟪ Lx , _ ⟫ = ⟪ Lx , ( λ lt → ⊥-elim ( ¬∅∋ (eq→ (begin
                  (* o∅) ≈⟨  o∅==od∅ ⟩
                  od∅ ∎ ) (subst (λ k → odef (* o∅) k ) (sym &iso) (Own.ao lt ))))) ⟫ 
                     where open EqHOD ==-Setoid
          fp02 t (fin-i {x} tx ) = record { i = x ; sb = gi fp03  ; t⊆i = fp24 } where
              -- we have a single cover x, L ＼ * x is single finite intersection
              fp24 : (L ＼ * x) ⊆ (L ＼ Union (* (& (* x , * x))))
              fp24 {y} ⟪ Lx , not ⟫  = ⟪ Lx , fp26  ⟫ where
                   fp26 : ¬ odef (Union (* (& (* x , * x)))) y
                   fp26 record { owner = owner ; ao = ao ; ox = ox } with eq→ *iso ao
                   ... | case1 refl = not (eq→ *iso ox )
                   ... | case2 refl = not (eq→ *iso ox )
              fp03 :  odef (* X) (& (L ＼ * x))  -- becase x is an element of  Replace (* X) (λ z → L ＼  z )
              fp03 with eq→ *iso tx
              ... | record { z = z1 ; az = az1 ; x=ψz = x=ψz1 } = subst (λ k → odef (* X) k) fip33 az1 where
                   fip34 : * z1 ⊆ L
                   fip34 {w} wz1 = cs⊆L top (subst (λ k → odef (CS top) k) (sym &iso) (CX az1) ) wz1
                   fip33 : z1 ≡ & (L ＼ * x)
                   fip33 = trans (sym &iso ) (==→o≡ ( begin
                     (* z1) ≈⟨ ==-sym  (L＼Lx=x {* z1} fip34 ) ⟩
                     (L ＼ ( L ＼ * z1)) ≈⟨ ＼-cong L L ( L ＼ * z1) (* x) ==-refl (==-trans (==-sym *iso) (o≡→== (sym x=ψz1)) ) ⟩ 
                     (L ＼ * x ) ∎ ) ) where open EqHOD ==-Setoid
          fp02 t (fin-∪ {tx} {ty} ux uy ) =  record { i = & (* (SB.i (fp02 tx ux)) ∪ * (SB.i (fp02 ty uy))) ; sb = fp11  ; t⊆i = fp35 } where
              fp35 : (L ＼ * (& (* (SB.i (fp02 tx ux)) ∪ * (SB.i (fp02 ty uy))))) ⊆ (L ＼ Union (* (& (* tx ∪ * ty))))
              fp35 = λ lt → eq← fp42 ( fp36 (eq→  ( ＼-cong L L (* (& (* (SB.i (fp02 tx ux)) ∪ * (SB.i (fp02 ty uy))))) 
                                                                (* (SB.i (fp02 tx ux)) ∪ * (SB.i (fp02 ty uy))) ==-refl *iso ) lt ) ) where
                  fp43 : (P : HOD ) → Union (* (& P)) =h= Union P
                  eq← (fp43 P) record { owner = owner ; ao = ao ; ox = ox } = record { owner = owner ; ao = eq← *iso ao ; ox = ox }
                  eq→ (fp43 P) record { owner = owner ; ao = ao ; ox = ox } = record { owner = owner ; ao = eq→ *iso ao ; ox = ox }
                  fp42 : ( L ＼ Union (* (& (* tx ∪ * ty)))) =h=  (L ＼ Union (* tx ∪ * ty))
                  eq→ fp42 {x} ⟪ lx , nux ⟫ = ⟪ lx , (λ lt → nux (eq← (fp43 _) lt) ) ⟫
                  eq← fp42 {x} ⟪ lx , nux ⟫ = ⟪ lx , (λ lt → nux (eq→ (fp43 _) lt) ) ⟫
                  fp40 : {z tz : Ordinal } → Finite-∪ (* (OX CX)) tz → odef (Union (* tz )) z → odef L z 
                  fp40 {z} {.(Ordinals.o∅ O)} fin-e record { owner = owner ; ao = ao ; ox = ox } 
                      = ⊥-elim ( ¬∅∋ (eq→ o∅==od∅ (subst (λ k → odef (* o∅) k ) (sym &iso) ao )))
                  fp40 {z} {.(& (* _ , * _))} (fin-i {w} x) uz = fp41 x (eq→ (fp43 _) uz)  where
                       fp41 : (x : odef (* (OX CX)) w) → (uz : odef (Union (* w , * w)) z ) → odef L z
                       fp41 x record { owner = .(& (* w)) ; ao = (case1 refl) ; ox = ox } = 
                           os⊆L top (OOX CX (subst (λ k → odef (* (OX CX)) k) (sym &iso) x )) (eq→ *iso ox )
                       fp41 x record { owner = .(& (* w)) ; ao = (case2 refl) ; ox = ox } = 
                           os⊆L top (OOX CX (subst (λ k → odef (* (OX CX)) k) (sym &iso) x )) (eq→ *iso ox )
                  fp40 {z} {.(& (* _ ∪ * _))} (fin-∪ {x1} {y1} ftx fty) uz with eq→ (fp43 _ ) uz
                  ... | record { owner = o ; ao = case1 x1o ; ox = oz } = fp40 ftx record { owner = o ; ao = x1o ; ox = oz } 
                  ... | record { owner = o ; ao = case2 y1o ; ox = oz } = fp40 fty record { owner = o ; ao = y1o ; ox = oz } 
                  fp36 : (L ＼  (* (SB.i (fp02 tx ux)) ∪ * (SB.i (fp02 ty uy)))) ⊆ (L ＼ Union (* tx ∪ * ty))
                  fp36 {z} ⟪ Lz , not ⟫ = ⟪ Lz , fp37 ⟫ where
                      fp37 : ¬ odef (Union (* tx ∪ * ty)) z 
                      fp37 record { owner = owner ; ao = (case1 ax) ; ox = ox } = not (case1 (fp39 record { owner = _ ; ao = ax ; ox = ox }) ) where
                          fp38 : (L ＼  (* (SB.i (fp02 tx ux)))) ⊆ (L ＼ Union (* tx))
                          fp38 = SB.t⊆i (fp02 tx ux) 
                          fp39 : Union (* tx) ⊆  (* (SB.i (fp02 tx ux)))
                          fp39 {w} txw with ∨L＼X {* (SB.i (fp02 tx ux))} (fp40 ux txw)
                          ... | case1 sb = sb
                          ... | case2 lsb = ⊥-elim ( proj2 (fp38 lsb) txw )
                      fp37 record { owner = owner ; ao = (case2 ax) ; ox = ox } = not (case2 (fp39 record { owner = _ ; ao = ax ; ox = ox }) ) where
                          fp38 : (L ＼  (* (SB.i (fp02 ty uy)))) ⊆ (L ＼ Union (* ty))
                          fp38 = SB.t⊆i (fp02 ty uy) 
                          fp39 : Union (* ty) ⊆  (* (SB.i (fp02 ty uy)))
                          fp39 {w} tyw with ∨L＼X {* (SB.i (fp02 ty uy))} (fp40 uy tyw)
                          ... | case1 sb = sb
                          ... | case2 lsb = ⊥-elim ( proj2 (fp38 lsb) tyw )
              fp04 :  {tx ty : Ordinal} → & (* (& (L ＼ * tx)) ∩ * (& (L ＼ * ty))) ≡ & (L ＼ * (& (* tx ∪ * ty)))
              fp04 {tx} {ty} = ==→o≡ record { eq→ = fp05 ; eq← = fp09 }  where
                  fp05 : {x : Ordinal} → odef (* (& (L ＼ * tx)) ∩ * (& (L ＼ * ty))) x → odef (L ＼ * (& (* tx ∪ * ty))) x
                  fp05 {x} lt with eq← *iso∩ lt
                  ... | ⟪ ⟪ Lx , ¬tx ⟫ , ⟪ Ly , ¬ty ⟫ ⟫ = eq→  (＼-cong L L (* tx ∪ * ty) (* (& (* tx ∪ * ty))) ==-refl (==-sym *iso) ) ⟪ Lx , fp06 ⟫  where
                        fp06 : ¬ odef (* tx ∪ * ty) x 
                        fp06 (case1 tx) = ¬tx tx
                        fp06 (case2 ty) = ¬ty ty
                  fp09 : {x : Ordinal} → odef (L ＼ * (& (* tx ∪ * ty))) x → odef (* (& (L ＼ * tx)) ∩ * (& (L ＼ * ty))) x
                  fp09 {x} lt with eq→ (＼-cong L L (* (& (* tx ∪ * ty))) (* tx ∪ * ty) ==-refl *iso )  lt
                  ... | ⟪ Lx , ¬tx∨ty ⟫ = eq→ *iso∩ 
                         ⟪ ⟪ Lx , ( λ tx → ¬tx∨ty (case1 tx)) ⟫ , ⟪ Lx , ( λ ty → ¬tx∨ty (case2 ty))  ⟫ ⟫ 
              fp11 : Subbase (* X) (& (L ＼ * (& ((* (SB.i (fp02 tx ux)) ∪ * (SB.i (fp02 ty uy)))))))
              fp11 = subst (λ k → Subbase (* X) k ) fp04 ( g∩ (SB.sb (fp02 tx ux)) (SB.sb (fp02 ty uy )) ) 
          -- 
          -- becase of fip, finite cover cannot be a cover
          --
          fcov : Finite-∪ (* (OX CX)) (Compact.finCover compact (OOX CX) cov)
          fcov = Compact.isFinite compact (OOX CX) cov
          0<sb : {i : Ordinal } → (sb : Subbase (* X) (& (L ＼ * i))) → o∅ o< & (L ＼ * i)
          0<sb {i} sb = fip sb
          sb : SB (Compact.finCover compact (OOX CX) cov)
          sb = fp02 fp01 (Compact.isFinite compact (OOX CX) cov)
          no-finite-cover : ¬ ( (* (Compact.finCover compact (OOX CX) cov)) covers L ) 
          no-finite-cover fcovers = ⊥-elim ( o<¬≡ (sym (==→o≡ f22)) f25 ) where  
               f23 : (L ＼ * (SB.i sb)) ⊆ ( L ＼  Union (* (Compact.finCover compact (OOX CX) cov)))
               f23 = SB.t⊆i sb
               f22 : (L ＼  Union (* (Compact.finCover compact (OOX CX) cov))) =h= od∅
               f22 = record { eq→ = λ lt → ⊥-elim ( f24 lt)  ; eq← = λ lt → ⊥-elim (¬x<0 lt) } where
                    f24 : {x : Ordinal } → ¬ ( odef (L ＼ Union (* (Compact.finCover compact (OOX CX) cov))) x )
                    f24 {x} ⟪ Lx , not ⟫ = not record { owner = cover fcovers Lx  ; ao = P∋cover fcovers Lx ; ox = isCover fcovers Lx }
               f25 : & od∅ o< (& (L ＼  Union (* (Compact.finCover compact (OOX CX) cov))) )
               f25 = ordtrans<-≤ (subst (λ k → k o< & (L ＼ * (SB.i sb))) (sym ord-od∅) (0<sb (SB.sb sb) ) )  ( begin
                  & (L ＼ * (SB.i sb))  ≤⟨ ⊆→o≤ f23 ⟩ 
                  & (L ＼  Union (* (Compact.finCover compact (OOX CX) cov)))  ∎  ) where open o≤-Reasoning O
      -- if we have no cover, we can consruct NC
      intersection : NC CX fip 0<X
      intersection with p∨¬p (NC CX fip 0<X)
      ... | case1 nc = nc 
      ... | case2 ¬nc = ⊥-elim ( no-cover record { cover = λ Lx → & (L ＼ coverf Lx) ; P∋cover = fp22 ; isCover = fp23 } ) where
          coverSet : {x : Ordinal} → odef L x → HOD
          coverSet {x} Lx = record { od = record { def = λ y → odef (* X) y ∧ odef (L ＼ * y) x } ; odmax = X 
             ; <odmax = λ {x} lt → subst (λ k → x o< k) &iso ( odef< (proj1 lt)) }
          fp17 : {x : Ordinal} → (Lx : odef L x ) → ¬ ( coverSet Lx =h= od∅ )
          fp17 {x} Lx eq = ⊥-elim (¬nc record { x = x ; yx = fp19 } ) where
             fp19 : {y : Ordinal} → odef (* X) y → odef (* y) x
             fp19 {y} Xy with ∨L＼X {* y} {x} Lx
             ... | case1 yx = yx
             ... | case2 lyx = ⊥-elim ( ¬x<0 {y} ( eq→ eq fp20 )) where
                fp20 : odef (* X) y ∧ odef (L ＼ * y) x
                fp20 = ⟪ Xy , lyx ⟫
          coverf : {x : Ordinal} → (Lx : odef L x ) → HOD
          coverf Lx =  minimal (coverSet Lx) (fp17 Lx)
          fp22 :  {x : Ordinal} (lt : odef L x) → odef (* (OX CX)) (& (L ＼ coverf lt))
          fp22 {x} Lx = eq← *iso record { z = _ ; az = fp25 ; x=ψz = fp24   } where
             fp24 : & (L ＼ coverf Lx) ≡ & (L ＼ * (& (coverf Lx)))
             fp24 = ==→o≡ (＼-cong L L (coverf Lx) (* (& (coverf Lx))) ==-refl (==-sym *iso) )
             fp25 : odef (* X) (& (coverf Lx))
             fp25 = proj1 ( x∋minimal (coverSet Lx) (fp17 Lx) )
          fp23 :  {x : Ordinal} (lt : odef L x) → odef (* (& (L ＼ coverf lt))) x
          fp23 {x} Lx = eq← *iso ⟪ Lx , fp26 ⟫  where
             fp26 : ¬ odef (coverf Lx) x
             fp26 llx = proj2 (proj2 ( x∋minimal (coverSet Lx) (fp17 Lx) )) (eq← *iso llx) 
   limit : {X : Ordinal} (CX : * X ⊆ CS top) (fip : {x : Ordinal} → Subbase (* X) x → o∅ o< x) → Ordinal
   limit {X} CX fip with trio< X o∅ 
   ... | tri< a ¬b ¬c = ⊥-elim ( ¬x<0 a )
   ... | tri≈ ¬a b ¬c = o∅
   ... | tri> ¬a ¬b c = NC.x ( has-intersection CX fip c)
   fip00 : {X : Ordinal} (CX : * X ⊆ CS top)
            (fip : {x : Ordinal} → Subbase (* X) x → o∅ o< x)
            {x : Ordinal} → odef (* X) x → odef (* x) (limit CX fip )
   fip00 {X} CX fip {x} Xx with trio< X o∅
   ... | tri< a ¬b ¬c = ⊥-elim ( ¬x<0 a )
   ... | tri≈ ¬a b ¬c = ⊥-elim (  o<¬≡ (sym b) (subst (λ k → o∅ o< k) &iso (∈∅< Xx) ) )
   ... | tri> ¬a ¬b c = NC.yx ( has-intersection CX fip c ) Xx

open Filter

--
-- {v | Neighbor lim v}  set of u ⊆ v ⊆ P where u is an open set u ∋ x
--
record Neighbor {P : HOD} (TP : Topology P) (x v : Ordinal) : Set n where
   field
       u : Ordinal
       ou : odef (OS TP) u
       ux : odef (* u) x
       v⊆P : * v ⊆ P
       u⊆v : * u ⊆ * v

--
-- Neighbor on x is a Filter (on Power P)
--
NeighborF : {P : HOD} (TP : Topology P)  (x : Ordinal ) → Filter {Power P} {P} (λ x → x)
NeighborF {P} TP x = record { filter = NF ; f⊆L = NF⊆PP ; filter1 = f1 ; filter2 = f2 } where
    nf00 : {v : Ordinal } → Neighbor TP x v → odef (Power P) v
    nf00 {v} nei y vy = Neighbor.v⊆P nei vy
    NF : HOD
    NF = record { od = record { def = λ v → Neighbor TP x v } ; odmax = & (Power P) ; <odmax = λ lt → odef< (nf00 lt) }
    NF⊆PP : NF ⊆ Power P
    NF⊆PP = nf00 
    f1 : {p q : HOD} → Power P ∋ q → NF ∋ p → p ⊆ q → NF ∋ q
    f1 {p} {q} Pq Np p⊆q = record { u = Neighbor.u Np ; ou = Neighbor.ou Np ; ux = Neighbor.ux Np ; v⊆P = Pq _ ; u⊆v = f11 } where
        f11 :  * (Neighbor.u Np) ⊆ * (& q)
        f11 {x} ux = eq← *iso ( p⊆q (eq→ *iso  (Neighbor.u⊆v Np ux)) )
    f2 : {p q : HOD} → NF ∋ p → NF ∋ q → Power P ∋ (p ∩ q) → NF ∋ (p ∩ q)
    f2 {p} {q} Np Nq Ppq = record { u = upq ; ou = ou ; ux = ux ; v⊆P = Ppq _ ; u⊆v = f20 } where
         upq : Ordinal
         upq = & ( * (Neighbor.u Np) ∩ * (Neighbor.u Nq) )
         ou : odef (OS TP) upq
         ou = o∩ TP (subst (λ k → odef (OS TP) k) (sym &iso) (Neighbor.ou Np)) (subst (λ k → odef (OS TP) k) (sym &iso) (Neighbor.ou Nq))
         ux :  odef (* upq) x
         ux = eq← *iso ⟪ Neighbor.ux Np , Neighbor.ux Nq ⟫
         f20 : * upq ⊆ * (& (p ∩ q))
         f20 {x} lt = eq← *iso ⟪ eq→  *iso  (Neighbor.u⊆v Np (proj1 pq))  , eq→ *iso (Neighbor.u⊆v Nq (proj2 pq)) ⟫  where
             pq :  odef (* (Neighbor.u Np) ∩ * (Neighbor.u Nq)) x
             pq = eq→ *iso lt

CAP : (P : HOD) {p q : HOD } → Power P ∋ p → Power P ∋ q → Power P ∋ (p ∩ q)
CAP P {p} {q} Pp Pq x pqx with eq→ *iso pqx
... | ⟪ px , qx ⟫ = Pp _ (eq← *iso px )

NEG : (P : HOD) {p : HOD } → Power P ∋ p → Power P ∋ (P ＼ p )
NEG P {p} Pp x vx with eq→ *iso vx
... | ⟪ Px , npx ⟫ = Px



