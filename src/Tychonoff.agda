{-# OPTIONS --allow-unsolved-metas #-}
open import Level
open import Ordinals
module Tychonoff {n : Level } (O : Ordinals {n})   where

open import zf
open import logic
open _∧_
open _∨_
open Bool

import OD
open import Relation.Nullary
open import Data.Empty
open import Relation.Binary.Core
open import Relation.Binary.Definitions
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
open import Topology O
open import maximum-filter O

open Filter  
open Topology 

-- FIP is UFL

-- filter Base
record FBase (P : HOD )(X : Ordinal ) (u : Ordinal) : Set n where
   field
       b x : Ordinal
       b⊆X : * b ⊆ * X
       sb  : Subbase (* b) x
       u⊆P : * u ⊆ P
       x⊆u : * x ⊆ * u

record UFLP {P : HOD} (TP : Topology P)  (F : Filter {Power P} {P} (λ x → x) )
       (ultra : ultra-filter F ) : Set (suc (suc n)) where
   field
       limit : Ordinal
       P∋limit : odef P limit
       is-limit : {v : Ordinal} → Neighbor TP limit v → (* v) ⊆ filter F

UFLP→FIP : {P : HOD} (TP : Topology P) →
   ((F : Filter {Power P} {P} (λ x → x) ) (UF : ultra-filter F ) → UFLP TP F UF ) → FIP TP
UFLP→FIP {P} TP uflp with trio< (& P) o∅
... | tri< a ¬b ¬c = ⊥-elim ( ¬x<0 a )
... | tri≈ ¬a b ¬c = record { limit = ? ; is-limit = {!!} } where
   -- P is empty
   fip02 : {x : Ordinal } → ¬ odef P x
   fip02 {x} Px = ⊥-elim ( o<¬≡ (sym b) (∈∅< Px) )
... | tri> ¬a ¬b 0<P = record { limit = ? ; is-limit = uf01 } where
     fip : {X : Ordinal} → * X ⊆ CS TP → Set n
     fip {X} CSX = {x : Ordinal} → Subbase (* X) x → o∅ o< x
     N : {X : Ordinal} → (CSX : * X ⊆ CS TP) → fip CSX → HOD
     N {X} CSX fp = record { od = record { def = λ u → FBase P X u } ; odmax = osuc (& P)
        ; <odmax = λ {x} lt → subst₂ (λ j k → j o< osuc k) &iso refl (⊆→o≤ (FBase.u⊆P lt))  }
     N⊆PP : {X : Ordinal } → (CSX : * X ⊆ CS TP) → (fp : fip CSX) → N CSX fp ⊆ Power P
     N⊆PP CSX fp nx b xb  = FBase.u⊆P nx xb
     nc : {X : Ordinal} → (CSX : * X ⊆ CS TP) → (fp : fip CSX) → HOD
     nc = ?
     N∋nc :{X : Ordinal} → (CSX : * X ⊆ CS TP) → (fp : fip CSX) → odef (N CSX fp) (& (nc CSX fp) )
     N∋nc = ?
     0<PP : o∅ o< & (Power P)
     0<PP = ?
     --
     -- FIP defines a filter
     --
     F : {X : Ordinal} → (CSX : * X ⊆ CS TP) → (fp : fip CSX) → Filter {Power P} {P} (λ x → x)
     F {X} CSX fp = record { filter = N CSX fp ; f⊆L = N⊆PP CSX fp ; filter1 = f1 ; filter2 = f2 } where
         f1 :  {p q : HOD} → Power P ∋ q → N CSX fp ∋ p → p ⊆ q → N CSX fp ∋ q
         f1 {p} {q} Xq record { b = b ; x = x ; b⊆X = b⊆X ; sb = sb ; u⊆P = Xp ; x⊆u = x⊆p } p⊆q =
                       record { b = b ; x = x ; b⊆X = b⊆X ; sb = sb ; u⊆P = subst (λ k → k ⊆ P) (sym *iso) f10 ; x⊆u = λ {z} xp →
                            subst (λ k → odef k z) (sym *iso) (p⊆q (subst (λ k → odef k z) *iso (x⊆p xp)))  } where
              f10 : q ⊆ P
              f10 {x} qx = subst (λ k → odef P k) &iso (power→ P _ Xq (subst (λ k → odef q k) (sym &iso) qx  ))
         f2 : {p q : HOD} → N CSX fp ∋ p → N CSX fp ∋ q → Power P ∋ (p ∩ q) → N CSX fp ∋ (p ∩ q)
         f2 {p} {q} Np Nq Xpq = record { b = & Np+Nq ; x = & xp∧xq ; b⊆X = f20 ; sb = sbpq ; u⊆P = p∩q⊆p ; x⊆u = f22 } where
              p∩q⊆p : * (& (p ∩ q)) ⊆ P
              p∩q⊆p {x} pqx = subst (λ k → odef P k) &iso (power→ P _ Xpq (subst₂ (λ j k → odef j k ) *iso (sym &iso) pqx ))
              Np+Nq = * (FBase.b Np) ∪ * (FBase.b Nq)
              xp∧xq = * (FBase.x Np) ∩ * (FBase.x Nq)
              sbpq : Subbase (* (& Np+Nq)) (& xp∧xq)
              sbpq = subst₂ (λ j k → Subbase j k ) (sym *iso) refl (  g∩ (sb⊆ case1 (FBase.sb Np)) (sb⊆ case2 (FBase.sb Nq)))
              f20 : * (& Np+Nq) ⊆ * X
              f20 {x} npq with subst (λ k → odef k x) *iso npq
              ... | case1 np = FBase.b⊆X Np np
              ... | case2 nq = FBase.b⊆X Nq nq
              f22 : * (& xp∧xq) ⊆ * (& (p ∩ q))
              f22 = subst₂ ( λ j k → j ⊆ k ) (sym *iso) (sym *iso) (λ {w} xpq
                 → ⟪ subst (λ k → odef k w) *iso ( FBase.x⊆u Np (proj1 xpq)) ,  subst (λ k → odef k w) *iso ( FBase.x⊆u Nq (proj2 xpq)) ⟫ )
     --
     -- it contains no empty sets
     -- 
     proper : {X : Ordinal} → (CSX : * X ⊆ CS TP) → (fp : fip {X} CSX) → ¬ (N CSX fp ∋ od∅)
     proper = ?
     --
     -- then we have maximum ultra filter 
     --
     maxf : {X : Ordinal} → (CSX : * X ⊆ CS TP) → (fp : fip {X} CSX) → MaximumFilter (λ x → x) (F CSX fp)
     maxf {X} CSX fp = F→Maximum {Power P} {P} (λ x → x) (CAP P)  (F CSX fp) 0<PP (N∋nc CSX fp) (proper CSX fp)
     mf : {X : Ordinal} → (CSX : * X ⊆ CS TP) → (fp : fip {X} CSX) → Filter {Power P} {P} (λ x → x)
     mf {X} CSX fp =  MaximumFilter.mf (maxf CSX fp) 
     ultraf : {X : Ordinal} → (CSX : * X ⊆ CS TP) → (fp : fip {X} CSX) → ultra-filter ( mf CSX fp)
     ultraf {X} CSX fp = F→ultra {Power P} {P} (λ x → x) (CAP P) (F CSX fp)  0<PP (N∋nc CSX fp) (proper CSX fp)
     --
     -- so i has a limit as a limit of UIP
     --
     limit : {X : Ordinal} → (CSX : * X ⊆ CS TP) → fip {X} CSX → Ordinal
     limit {X} CSX fp = UFLP.limit ( uflp ( mf CSX fp ) (ultraf CSX fp))
     uf02 : {X v  : Ordinal} → (CSX : * X ⊆ CS TP) → (fp : fip {X} CSX) 
        → Neighbor TP (limit CSX fp) v → * v ⊆  filter ( mf CSX fp )  
     uf02 {X} {v} CSX fp nei {x} vx = UFLP.is-limit ( uflp  ( mf CSX fp ) (ultraf CSX fp)) nei vx
     --
     -- the limit is an element of entire elements of X
     --
     uf01 :  {X : Ordinal} (CSX : * X ⊆ CS TP) (fp : fip {X} CSX) {x : Ordinal} → odef (* X) x → odef (* x) (limit CSX fp)
     uf01 {X} CSX fp {x} xx with ODC.∋-p O (* x) (* (limit CSX fp))
     ... | yes y = subst (λ k → odef (* x) k) &iso y
     ... | no nxl = ⊥-elim ( MaximumFilter.proper (maxf CSX fp) uf08 )  where
         uf03 : OS TP ∋  ( P ＼ (* x))
         uf03 = ?
         uf05 : odef ( P ＼ (* x)) (limit CSX fp)
         uf05 = ⟪  ? , subst (λ k → ¬ odef (* x) k) ?  nxl ⟫
         uf04 : Neighbor TP (limit CSX fp) (& ( P ＼ (* (limit CSX fp))))
         uf04 = record { u = & ( P ＼ (* x)) ; ou = ? ; ux = ? ; v⊆P = ? ; u⊆v = ? }
         uf07 : odef (filter (mf CSX fp)) x
         uf07 = ?
         uf06 : odef (filter (mf CSX fp)) (& ( P ＼ (* x)) )
         uf06 = ?
         uf08 : (filter (mf CSX fp)) ∋ od∅
         uf08 = ?
            

FIP→UFLP : {P : HOD} (TP : Topology P) →  FIP TP
   →  (F : Filter {Power P} {P} (λ x → x)) (UF : ultra-filter F ) → UFLP {P} TP F UF
FIP→UFLP {P} TP fip F UF = record { limit = FIP.limit fip (subst (λ k → k ⊆ CS TP) (sym *iso) CF⊆CS) ufl01 ; P∋limit = ? ; is-limit = ufl00 } where
     --
     -- take closure of given filter elements
     --
     CF : HOD
     CF = Replace (filter F) (λ x → Cl TP x  )
     CF⊆CS : CF ⊆ CS TP
     CF⊆CS {x} record { z = z ; az = az ; x=ψz = x=ψz } = subst (λ k → odef (CS TP) k) (sym x=ψz) (CS∋Cl TP (* z)) 
     --
     -- it is set of closed set and has FIP ( F is proper )
     --
     ufl01 : {x : Ordinal} → Subbase (* (& CF)) x → o∅ o< x
     ufl01 = ?
     --
     -- so we have a limit
     --
     limit : Ordinal
     limit = FIP.limit fip (subst (λ k → k ⊆ CS TP) (sym *iso) CF⊆CS) ufl01  
     ufl02 : {y : Ordinal } → odef (* (& CF)) y → odef (* y) limit
     ufl02 = FIP.is-limit fip (subst (λ k → k ⊆ CS TP) (sym *iso) CF⊆CS) ufl01  
     --
     -- Neigbor of limit ⊆ Filter
     --
     ufl03 : {f v : Ordinal } → odef (filter F) f → Neighbor TP limit v → ¬ ( * f ∩ * v ) =h= od∅  -- because limit is in CF which is a closure
     ufl03 {f} {v} ff nei fv=0 = ?
     pp :  {v x : Ordinal} → Neighbor TP limit v → odef (* v) x → Power P ∋ (* x)
     pp {v} {x} nei vx z pz = ?
     ufl00 :  {v : Ordinal} → Neighbor TP limit v → * v ⊆ filter F 
     ufl00 {v} nei {x} fx with ultra-filter.ultra UF (pp nei fx) (NEG P (pp nei fx))
     ... | case1 fv = subst (λ k → odef (filter F) k) &iso fv
     ... | case2 nfv = ? -- will contradicts ufl03

-- product topology of compact topology is compact

Tychonoff : {P Q : HOD } → (TP : Topology P) → (TQ : Topology Q)  → Compact TP → Compact TQ   → Compact (ProductTopology TP TQ)
Tychonoff {P} {Q} TP TQ CP CQ = FIP→Compact (ProductTopology TP TQ) (UFLP→FIP (ProductTopology TP TQ) uflPQ ) where
     uflP : (F : Filter {Power P} {P} (λ x → x))  (UF : ultra-filter F)
             → UFLP TP F UF
     uflP F UF = FIP→UFLP TP (Compact→FIP TP CP) F UF
     uflQ : (F : Filter {Power Q} {Q} (λ x → x))  (UF : ultra-filter F)
             → UFLP TQ F UF
     uflQ F UF = FIP→UFLP TQ (Compact→FIP TQ CQ) F UF
     -- Product of UFL has limit point
     uflPQ :  (F : Filter {Power (ZFP P Q)} {ZFP P Q} (λ x → x))  (UF : ultra-filter F)
             → UFLP (ProductTopology TP TQ) F UF
     uflPQ F UF = record { limit = & < * ( UFLP.limit uflp ) , * ( UFLP.limit uflq ) >  ; P∋limit = Pf ; is-limit = isL } where
         FP : Filter {Power P} {P} (λ x → x)
         FP = record { filter = Proj1 (filter F) (Power P) (Power Q) ; f⊆L = ty00 ; filter1 = ? ; filter2 = ? } where
             ty00 :  Proj1 (filter F) (Power P) (Power Q) ⊆ Power P
             ty00 {x} ⟪ PPx , ppf ⟫ = PPx
         UFP : ultra-filter FP
         UFP = record { proper = ? ; ultra = ? }
         uflp : UFLP TP FP UFP
         uflp = FIP→UFLP TP (Compact→FIP TP CP) FP UFP

         FQ : Filter {Power Q} {Q} (λ x → x)
         FQ = record { filter = Proj2 (filter F) (Power P) (Power Q) ; f⊆L = ty00 ; filter1 = ? ; filter2 = ? } where
             ty00 :  Proj2 (filter F) (Power P) (Power Q) ⊆ Power Q
             ty00 {x} ⟪ QPx , ppf ⟫ = QPx
         UFQ : ultra-filter FQ
         UFQ = record { proper = ? ; ultra = ? }
         uflq : UFLP TQ FQ UFQ
         uflq = FIP→UFLP TQ (Compact→FIP TQ CQ) FQ UFQ

         Pf : odef (ZFP P Q) (& < * (UFLP.limit uflp) , * (UFLP.limit uflq) >)
         Pf = ?
         pq⊆F : {p q : HOD} → Neighbor TP (& p) (UFLP.limit uflp) → Neighbor TP (& q) (UFLP.limit uflq) → ? ⊆ filter F 
         pq⊆F = ?
         isL : {v : Ordinal} → Neighbor (ProductTopology TP TQ) (& < * (UFLP.limit uflp) , * (UFLP.limit uflq) >) v → * v ⊆ filter F 
         isL {v} npq {x} fx = ? where 
             bpq : Base (ZFP P Q) (pbase TP TQ) (Neighbor.u npq) (& < * (UFLP.limit uflp) , * (UFLP.limit uflq) >)
             bpq = Neighbor.ou npq (Neighbor.ux npq)
             pqb : Subbase (pbase TP TQ) (Base.b bpq )
             pqb = Base.sb bpq 
             pqb⊆opq : * (Base.b bpq) ⊆ * ( Neighbor.u npq )
             pqb⊆opq = Base.b⊆u bpq
             base⊆F : {b : Ordinal } →  Subbase (pbase TP TQ) b → * b ⊆  * (Neighbor.u npq) → * b ⊆ filter F
             base⊆F (gi (case1 px)) b⊆u {z} bz = fz  where
                 -- F contains no od∅, because it projection contains no od∅
                 --    x is an element of BaseP, which is a subset of Neighbor npq
                 --    x is also an elment of Proj1 F because Proj1 F has UFLP (uflp)
                 --    BaseP ∩ F is not empty
                 --    (Base P ∩ F) ⊆ F , (Base P ) ⊆ F , 
                 il1 : odef (Power P) z ∧ ZProj1 (filter F) z
                 il1 = UFLP.is-limit uflp ? bz 
                 nei1 : HOD
                 nei1 = Proj1 (* (Neighbor.u npq)) (Power P) (Power Q)
                 plimit : Ordinal
                 plimit = UFLP.limit uflp 
                 nproper : {b : Ordinal } →  * b ⊆ nei1 → o∅ o< b
                 nproper = ?
                 b∋z : odef nei1 z
                 b∋z = ?
                 bp : BaseP {P} TP Q z
                 bp = record { p = ? ; op = ? ; prod = ? }
                 neip : {p : Ordinal } → ( bp : BaseP TP Q p ) → * p ⊆ filter F 
                 neip = ?
                 il2 : * z ⊆ ZFP (Power P) (Power Q)
                 il2 = ?
                 il3 : filter F ∋ ? 
                 il3 = ?
                 fz : odef (filter F) z
                 fz = subst (λ k → odef (filter F) k) &iso (filter1 F ? ? ?)
             base⊆F (gi (case2 qx)) b⊆u {z} bz = ?
             base⊆F (g∩ b1 b2) b⊆u {z} bz = ?






