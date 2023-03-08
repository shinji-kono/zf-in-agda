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
open import ZProduct O
open import Topology O
open import maximum-filter O

open Filter
open Topology

-- FIP is UFL

-- filter Base
record FBase (P : HOD ) (X : Ordinal ) (u : Ordinal) : Set n where
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
       is-limit : {v : Ordinal} → Neighbor TP limit v → filter F ∋ (* v)

UFLP→FIP : {P : HOD} (TP : Topology P) →
   ((F : Filter {Power P} {P} (λ x → x) ) (UF : ultra-filter F ) → UFLP TP F UF ) → FIP TP
UFLP→FIP {P} TP uflp with trio< (& P) o∅
... | tri< a ¬b ¬c = ⊥-elim ( ¬x<0 a )
... | tri≈ ¬a P=0 ¬c = record { limit = λ CX fip → o∅ ; is-limit = fip03 } where
   -- P is empty
   fip02 : {x : Ordinal } → ¬ odef P x
   fip02 {x} Px = ⊥-elim ( o<¬≡ (sym P=0) (∈∅< Px) )
   fip03 : {X : Ordinal} (CX : * X ⊆ CS TP) (fip : {x : Ordinal} → Subbase (* X) x → o∅ o< x) {x : Ordinal} →
            odef (* X) x → odef (* x) o∅
   -- empty P case
   --   if 0 < X then 0 < x ∧ P ∋ xfrom fip
   --   if 0 ≡ X then ¬ odef X x
   fip03 {X} CX fip {x} xx with trio< o∅ X
   ... | tri< 0<X ¬b ¬c = ⊥-elim ( ¬∅∋ (subst₂ (λ j k → odef j k ) (trans (trans (sym *iso) (cong (*) P=0)) o∅≡od∅ ) (sym &iso)
        ( cs⊆L TP (subst (λ k → odef (CS TP) k ) (sym &iso) (CX xx))  xe ))) where
      0<x : o∅ o< x
      0<x = fip (gi xx )
      e : HOD  -- we have an element of x
      e = ODC.minimal O (* x) (0<P→ne (subst (λ k → o∅ o< k) (sym &iso) 0<x) )
      xe : odef (* x) (& e)
      xe = ODC.x∋minimal O (* x) (0<P→ne (subst (λ k → o∅ o< k) (sym &iso) 0<x) )
   ... | tri≈ ¬a 0=X ¬c = ⊥-elim ( ¬∅∋ (subst₂ (λ j k → odef j k ) ( begin
           * X ≡⟨ cong (*) (sym 0=X) ⟩
           * o∅ ≡⟨  o∅≡od∅ ⟩
           od∅ ∎ ) (sym &iso) xx ) ) where open ≡-Reasoning
   ... | tri> ¬a ¬b c = ⊥-elim ( ¬x<0 c )
... | tri> ¬a ¬b 0<P = record { limit = λ CSX fip → limit CSX fip ; is-limit =  uf01 } where
     fip : {X : Ordinal} → * X ⊆ CS TP → Set n
     fip {X} CSX = {x : Ordinal} → Subbase (* X) x → o∅ o< x
     N : {X : Ordinal} → (CSX : * X ⊆ CS TP) → fip CSX → HOD
     N {X} CSX fp = record { od = record { def = λ u → FBase P X u } ; odmax = osuc (& P)
        ; <odmax = λ {x} lt → subst₂ (λ j k → j o< osuc k) &iso refl (⊆→o≤ (FBase.u⊆P lt))  }
     N⊆PP : {X : Ordinal } → (CSX : * X ⊆ CS TP) → (fp : fip CSX) → N CSX fp ⊆ Power P
     N⊆PP CSX fp nx b xb  = FBase.u⊆P nx xb
     -- filter base is not empty necessary for generating ultra filter
     nc : {X : Ordinal} → o∅ o< X → (CSX : * X ⊆ CS TP) → (fip : fip CSX) → HOD
     nc {X} 0<X CSX fip = ODC.minimal O (* X) (0<P→ne (subst (λ k → o∅ o< k) (sym &iso) 0<X) ) -- an element of X
     N∋nc :{X : Ordinal} → (0<X : o∅ o< X) → (CSX : * X ⊆ CS TP)
        → (fip : fip CSX) → odef (N CSX fip) (& (nc 0<X CSX fip) )
     N∋nc {X} 0<X CSX fip = record { b = X ; x =  & e ;  b⊆X = λ x → x ; sb = gi Xe ; u⊆P = nn02 ; x⊆u = λ x → x } where
          e : HOD  -- we have an element of X
          e = ODC.minimal O (* X) (0<P→ne (subst (λ k → o∅ o< k) (sym &iso) 0<X) )
          Xe : odef (* X) (& e)
          Xe = ODC.x∋minimal O (* X) (0<P→ne (subst (λ k → o∅ o< k) (sym &iso) 0<X) )
          nn01 = ODC.minimal O (* (& e)) (0<P→ne (subst (λ k → o∅ o< k) (sym &iso) (fip (gi Xe))) )
          nn02 : * (& (nc 0<X CSX fip)) ⊆ P
          nn02 = subst (λ k → k ⊆ P ) (sym *iso) (cs⊆L TP (CSX Xe ) )

     0<PP : o∅ o< & (Power P)
     0<PP = subst (λ k → k o< & (Power P)) &iso ( c<→o< (subst (λ k → odef (Power P) k) (sym &iso) nn00 )) where
          nn00 : odef (Power P) o∅
          nn00 x lt with subst (λ k → odef k x) o∅≡od∅ lt
          ... | x<0 = ⊥-elim ( ¬x<0 x<0)
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
     -- it contains no empty sets becase it is a finite intersection ( Subbase (* X) x )
     --
     proper : {X : Ordinal} → (CSX : * X ⊆ CS TP) → (fip : fip {X} CSX) → ¬ (N CSX fip ∋ od∅)
     proper {X} CSX fip record { b = b ; x = x ; b⊆X = b⊆X ; sb = sb ; u⊆P = u⊆P ; x⊆u = x⊆u } = o≤> x≤0 (fip (fp00 _ _ b⊆X sb)) where
          x≤0 : x o< osuc  o∅
          x≤0 = subst₂ (λ j k → j o< osuc k) &iso (trans (cong (&) *iso) ord-od∅ ) (⊆→o≤ (x⊆u))
          fp00 : (b x : Ordinal) → * b ⊆ * X → Subbase (* b) x → Subbase (* X) x
          fp00 b y b<X (gi by ) = gi ( b<X by )
          fp00 b _ b<X (g∩ {y} {z} sy sz ) = g∩ (fp00 _ _ b<X sy) (fp00 _ _ b<X sz)
     --
     -- then we have maximum ultra filter
     --
     maxf : {X : Ordinal} → o∅ o< X → (CSX : * X ⊆ CS TP) → (fp : fip {X} CSX) → MaximumFilter (λ x → x) (F CSX fp)
     maxf {X} 0<X CSX fp = F→Maximum {Power P} {P} (λ x → x) (CAP P)  (F CSX fp) 0<PP (N∋nc 0<X CSX fp) (proper CSX fp)
     mf : {X : Ordinal} → o∅ o< X → (CSX : * X ⊆ CS TP) → (fp : fip {X} CSX) → Filter {Power P} {P} (λ x → x)
     mf {X} 0<X CSX fp =  MaximumFilter.mf (maxf 0<X CSX fp)
     ultraf : {X : Ordinal} → (0<X : o∅ o< X ) → (CSX : * X ⊆ CS TP) → (fp : fip {X} CSX) → ultra-filter ( mf 0<X CSX fp)
     ultraf {X} 0<X CSX fp = F→ultra {Power P} {P} (λ x → x) (CAP P) (F CSX fp)  0<PP (N∋nc 0<X CSX fp) (proper CSX fp)
     --
     -- so i has a limit as a limit of UIP
     --
     limit : {X : Ordinal} → (CSX : * X ⊆ CS TP) → fip {X} CSX → Ordinal
     limit {X} CSX fp with trio< o∅ X
     ... | tri< 0<X ¬b ¬c = UFLP.limit ( uflp ( mf 0<X CSX fp ) (ultraf 0<X CSX fp))
     ... | tri≈ ¬a 0=X ¬c = o∅
     ... | tri> ¬a ¬b c = ⊥-elim ( ¬x<0 c )
     --
     -- the limit is an limit of entire elements of X
     --
     uf01 :  {X : Ordinal} (CSX : * X ⊆ CS TP) (fp : fip {X} CSX) {x : Ordinal} → odef (* X) x → odef (* x) (limit CSX fp)
     uf01 {X} CSX fp {x} xx with trio< o∅ X
     ... | tri> ¬a ¬b c = ⊥-elim ( ¬x<0 c )
     ... | tri≈ ¬a 0=X ¬c = ⊥-elim ( ¬a (subst (λ k → o∅ o< k) &iso ( ∈∅< xx )))
     ... | tri< 0<X ¬b ¬c with ∨L＼X {P} {* x} {UFLP.limit ( uflp  ( mf 0<X CSX fp ) (ultraf 0<X CSX fp))}
         (UFLP.P∋limit ( uflp  ( mf 0<X CSX fp ) (ultraf 0<X CSX fp)))
     ... | case1 lt = lt -- odef (* x) y
     ... | case2 nlxy = ⊥-elim (MaximumFilter.proper (maxf 0<X CSX fp) uf11 ) where
        y = UFLP.limit ( uflp  ( mf 0<X CSX fp ) (ultraf 0<X CSX fp))
        x⊆P : * x ⊆ P
        x⊆P = cs⊆L TP (CSX (subst (λ k → odef (* X) k) (sym &iso) xx))
        uf10 : odef (P ＼ * x ) y
        uf10 = nlxy
        uf03 : Neighbor TP y (& (P ＼ * x ))
        uf03 = record { u = _ ; ou = P＼CS=OS TP (CSX (subst (λ k → odef (* X) k ) (sym &iso) xx))
           ; ux = subst (λ k → odef k y) (sym *iso) uf10
           ; v⊆P = λ {z} xz → proj1 (subst(λ k → odef k z) *iso xz )
           ; u⊆v = λ x → x  }
        uf07 : * (& (* x , * x)) ⊆ * X
        uf07 {y} lt with subst (λ k → odef k y) *iso lt
        ... | case1 refl = subst (λ k → odef (* X) k ) (sym &iso) xx
        ... | case2 refl = subst (λ k → odef (* X) k ) (sym &iso) xx
        uf05 : odef (filter (MaximumFilter.mf (maxf 0<X CSX fp))) x
        uf05 = MaximumFilter.F⊆mf (maxf 0<X CSX fp) record { b = & (* x , * x) ; b⊆X = uf07
           ; sb = gi (subst (λ k → odef k x) (sym *iso) (case1 (sym &iso)) )  ; u⊆P = x⊆P ; x⊆u = λ x → x  }
        uf061 : odef (filter (MaximumFilter.mf (maxf 0<X CSX fp))) (& (* (& (P ＼ * x ))))
        uf061 = UFLP.is-limit ( uflp (mf 0<X CSX fp) (ultraf 0<X CSX fp)) {& (P ＼ * x)} uf03
        -- uf06 (same as uf061) have yellow if zorn lemma is not imported
        uf06 : odef (filter (MaximumFilter.mf (maxf 0<X CSX fp))) (& (P ＼ * x ))
        uf06 = subst (λ k → odef (filter (MaximumFilter.mf (maxf 0<X CSX fp))) k) &iso (UFLP.is-limit ( uflp (mf 0<X CSX fp) (ultraf 0<X CSX fp)) {& (P ＼ * x)} uf03  )
        uf13 : & ((* x) ∩ (P ＼ * x )) ≡ o∅
        uf13 = subst₂ (λ j k → j ≡ k ) refl ord-od∅ (cong (&) ( ==→o≡ record { eq→ = uf14 ; eq← = λ {x} lt → ⊥-elim (¬x<0 lt) }  ) ) where
           uf14 : {y : Ordinal} → odef (* x ∩ (P ＼ * x)) y → odef od∅ y
           uf14 {y} ⟪ xy , ⟪ Px , ¬xy ⟫ ⟫ = ⊥-elim ( ¬xy xy )
        uf12 : odef (Power P) (& ((* x) ∩ (P ＼ * x )))
        uf12 z pz with subst (λ k → odef k z) *iso pz
        ... | ⟪ xz , ⟪ Pz , ¬xz ⟫ ⟫ = Pz
        uf11 : filter (MaximumFilter.mf (maxf 0<X CSX fp)) ∋ od∅
        uf11 = subst (λ k → odef (filter (MaximumFilter.mf (maxf 0<X CSX fp))) k ) (trans uf13 (sym ord-od∅))
           ( filter2 (MaximumFilter.mf (maxf 0<X CSX fp)) (subst (λ k → odef (filter (MaximumFilter.mf (maxf 0<X CSX fp))) k) (sym &iso) uf05) uf06 uf12  )

x⊆Clx : {P : HOD} (TP : Topology P) →  {x : HOD} → x ⊆ P   → x ⊆ Cl TP x
x⊆Clx {P} TP {x}  x<p {y} xy  = ⟪ x<p xy , (λ c csc x<c → x<c xy )  ⟫
P⊆Clx : {P : HOD} (TP : Topology P) →  {x : HOD} → x ⊆ P   → Cl TP x ⊆ P
P⊆Clx {P} TP {x}  x<p {y} xy  = proj1 xy

FIP→UFLP : {P : HOD} (TP : Topology P) →  FIP TP
   →  (F : Filter {Power P} {P} (λ x → x)) (UF : ultra-filter F ) → UFLP {P} TP F UF
FIP→UFLP {P} TP fip F UF = record { limit = FIP.limit fip (subst (λ k → k ⊆ CS TP) (sym *iso) CF⊆CS) ufl01
   ; P∋limit = ufl10 ; is-limit = ufl00 } where
     F∋P : odef (filter F) (& P)
     F∋P with ultra-filter.ultra UF {od∅} (λ z az → ⊥-elim (¬x<0 (subst (λ k → odef k z) *iso az)) )  (λ z az → proj1 (subst (λ k → odef k z) *iso az ) )
     ... | case1 fp = ⊥-elim ( ultra-filter.proper UF fp )
     ... | case2 flp = subst (λ k → odef (filter F) k) (cong (&) (==→o≡ fl20))  flp where
         fl20 :  (P ＼ Ord o∅) =h=  P
         fl20 = record { eq→ = λ {x} lt → proj1 lt ; eq← = λ {x} lt → ⟪ lt , (λ lt → ⊥-elim (¬x<0 lt) )  ⟫  }
     0<P : o∅ o< & P
     0<P with trio< o∅ (& P)
     ... | tri< a ¬b ¬c = a
     ... | tri≈ ¬a b ¬c = ⊥-elim (ultra-filter.proper UF (subst (λ k → odef (filter F) k) (trans (sym b) (sym ord-od∅)) F∋P) )
     ... | tri> ¬a ¬b c = ⊥-elim (¬x<0 c)
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
     ufl08  : {z : Ordinal} → odef (Power P) (& (Cl TP (* z)))
     ufl08 {z} w zw with subst (λ k → odef k w ) *iso zw
     ... | t = proj1 t
     fx→px : {x : Ordinal} → odef (filter F) x → Power P ∋ * x
     fx→px {x} fx z xz = f⊆L F fx _ (subst (λ k → odef k z) *iso xz )
     F∋sb : {x : Ordinal} → Subbase CF x → odef (filter F) x
     F∋sb {x} (gi record { z = z ; az = az ; x=ψz = x=ψz }) = ufl07 where
        ufl09 : * z ⊆ P
        ufl09 {y} zy = f⊆L F az _ zy
        ufl07 : odef (filter F) x
        ufl07 = subst (λ k → odef (filter F) k) &iso ( filter1 F (subst (λ k → odef (Power P) k) (trans (sym x=ψz) (sym &iso))  ufl08  )
            (subst (λ k → odef (filter F) k) (sym &iso) az)
            (subst (λ k → * z ⊆ k ) (trans (sym *iso) (sym (cong (*) x=ψz)) ) (x⊆Clx TP {* z} ufl09 ) ))
     F∋sb  (g∩ {x} {y} sx sy) = filter2 F (subst (λ k → odef (filter F) k) (sym &iso) (F∋sb sx))
        (subst (λ k → odef (filter F) k) (sym &iso) (F∋sb sy))
            (λ z xz → fx→px (F∋sb sx) _ (subst (λ k → odef k _) (sym *iso) (proj1 (subst (λ k → odef k z) *iso xz) )))
     ufl01 : {x : Ordinal} → Subbase (* (& CF)) x → o∅ o< x
     ufl01 {x} sb = ufl04  where
        ufl04 : o∅ o< x
        ufl04 with trio< o∅ x
        ... | tri< a ¬b ¬c = a
        ... | tri≈ ¬a b ¬c = ⊥-elim ( ultra-filter.proper UF (subst (λ k → odef (filter F) k) (
           begin
           x  ≡⟨ sym b ⟩
           o∅ ≡⟨ sym ord-od∅ ⟩
           & od∅  ∎ ) (F∋sb (subst (λ k → Subbase k x) *iso sb )) ))  where open ≡-Reasoning
        ... | tri> ¬a ¬b c = ⊥-elim (¬x<0 c)
     ufl10 : odef P (FIP.limit fip (subst (λ k → k ⊆ CS TP) (sym *iso) CF⊆CS) ufl01)
     ufl10 = FIP.L∋limit fip (subst (λ k → k ⊆ CS TP) (sym *iso) CF⊆CS) ufl01 {& P} ufl11  where
         ufl11 : odef (* (& CF)) (& P)
         ufl11 = subst (λ k → odef k (& P)) (sym *iso) record { z = _ ; az  = F∋P ; x=ψz = sym (cong (&) (trans (cong (Cl TP) *iso) (ClL TP)))   }
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
     -- if odef (* X) x, Cl TP x contains limit (ufl02)
     -- in (nei : Neighbor TP limit v) , there is an open Set u which contains the limit
     -- F contains u or P ＼ u because F is ultra
     --   if F ∋ u, then F ∋ v from u ⊆ v which is a propetery of Neighbor
     --   if F ∋ P ＼ u, it is a closed set (Cl (P ＼ u) ≡ P ＼ u) and it does not contains the limit
     --      this contradicts ufl02
     pp :  {v : Ordinal} → (nei : Neighbor TP limit v ) → Power P ∋ (* (Neighbor.u nei))
     pp {v} record { u = u ; ou = ou ; ux = ux ; v⊆P = v⊆P ; u⊆v = u⊆v } z pz
        = os⊆L TP (subst (λ k → odef (OS TP) k) (sym &iso) ou ) (subst (λ k → odef k z) *iso pz )
     ufl00 :  {v : Ordinal} → Neighbor TP limit v → filter F ∋ * v
     ufl00 {v} nei with ultra-filter.ultra UF (pp nei ) (NEG P (pp nei ))
     ... | case1 fu = subst (λ k → odef (filter F) k) &iso
       ( filter1 F (subst (λ k → odef (Power P) k ) (sym &iso) px)  fu (subst (λ k → u ⊆ k ) (sym *iso) (Neighbor.u⊆v nei))) where
         u = * (Neighbor.u nei)
         px : Power P ∋ * v
         px z vz = Neighbor.v⊆P nei (subst (λ k → odef k z) *iso vz )
     ... | case2 nfu = ⊥-elim ( ¬P\u∋limit P\u∋limit ) where
         u = * (Neighbor.u nei)
         P\u : HOD
         P\u = P ＼ u
         P\u∋limit : odef P\u limit
         P\u∋limit = subst (λ k → odef k limit) *iso ( ufl02 (subst (λ k → odef k (& P\u)) (sym *iso) ufl03 )) where
             ufl04 : & P\u ≡ & (Cl TP (* (& P\u)))
             ufl04 = cong (&) (sym (trans (cong (Cl TP) *iso)
                (CS∋x→Clx=x TP (P＼OS=CS TP (subst (λ k → odef (OS TP) k) (sym &iso) (Neighbor.ou nei) )))))
             ufl03 : odef CF (& P\u )
             ufl03 = record { z = _ ; az = nfu ; x=ψz = ufl04 }
         ¬P\u∋limit : ¬ odef P\u limit
         ¬P\u∋limit ⟪ Pl , nul ⟫ = nul ( Neighbor.ux nei )

-- product topology of compact topology is compact

import Axiom.Extensionality.Propositional
postulate f-extensionality : { n m : Level}  → Axiom.Extensionality.Propositional.Extensionality n m
open import Relation.Binary.HeterogeneousEquality as HE using (_≅_ )


Tychonoff : {P Q : HOD } → (TP : Topology P) → (TQ : Topology Q)  → Compact TP → Compact TQ   → Compact (ProductTopology TP TQ)
Tychonoff {P} {Q} TP TQ CP CQ = FIP→Compact (ProductTopology TP TQ) (UFLP→FIP (ProductTopology TP TQ) uflPQ ) where
     uflP : (F : Filter {Power P} {P} (λ x → x))  (UF : ultra-filter F)
             → UFLP TP F UF
     uflP F UF = FIP→UFLP TP (Compact→FIP TP CP) F UF
     uflQ : (F : Filter {Power Q} {Q} (λ x → x))  (UF : ultra-filter F)
             → UFLP TQ F UF
     uflQ F UF = FIP→UFLP TQ (Compact→FIP TQ CQ) F UF
     -- Product of UFL has a limit point
     uflPQ :  (F : Filter {Power (ZFP P Q)} {ZFP P Q} (λ x → x))  (UF : ultra-filter F)
             → UFLP (ProductTopology TP TQ) F UF
     uflPQ F UF = record { limit = & < * ( UFLP.limit uflp ) , * ( UFLP.limit uflq ) >  ; P∋limit = Pf ; is-limit = isL } where
         F∋PQ : odef (filter F) (& (ZFP P Q))
         F∋PQ with ultra-filter.ultra UF {od∅} (λ z az → ⊥-elim (¬x<0 (subst (λ k → odef k z) *iso az)) )  (λ z az → proj1 (subst (λ k → odef k z) *iso az ) )
         ... | case1 fp = ⊥-elim ( ultra-filter.proper UF fp )
         ... | case2 flp = subst (λ k → odef (filter F) k) (cong (&) (==→o≡ fl20))  flp where
             fl20 :  (ZFP P Q ＼ Ord o∅) =h=  ZFP P Q
             fl20 = record { eq→ = λ {x} lt → proj1 lt ; eq← = λ {x} lt → ⟪ lt , (λ lt → ⊥-elim (¬x<0 lt) )  ⟫  }
         0<PQ : o∅ o< & (ZFP P Q)
         0<PQ with trio< o∅ (& (ZFP P Q))
         ... | tri< a ¬b ¬c = a
         ... | tri≈ ¬a b ¬c = ⊥-elim (ultra-filter.proper UF (subst (λ k → odef (filter F) k) (trans (sym b) (sym ord-od∅)) F∋PQ) )
         ... | tri> ¬a ¬b c = ⊥-elim (¬x<0 c)
         apq : HOD
         apq = ODC.minimal O (ZFP P Q) (0<P→ne 0<PQ)
         is-apq : ZFP P Q ∋ apq
         is-apq = ODC.x∋minimal O (ZFP P Q) (0<P→ne 0<PQ)
         ap : odef P ( zπ1 is-apq  )
         ap = zp1 is-apq
         aq : odef Q ( zπ2 is-apq  )
         aq = zp2 is-apq
         F⊆pxq : {x : HOD } → filter F ∋ x →  x ⊆ ZFP P Q
         F⊆pxq {x} fx {y} xy = f⊆L F fx y (subst (λ k → odef k y) (sym *iso) xy)

         ---
         --- FP is a P-projection of F, which is a ultra filter
         ---
         isP→PxQ : {x : HOD} → (x⊆P : x ⊆ P ) → ZFP x Q ⊆ ZFP P Q
         isP→PxQ {x} x⊆P (ab-pair p q) = ab-pair (x⊆P p) q
         fx→px : {x : HOD } → filter F ∋ x → HOD
         fx→px {x} fx = Replace' x ( λ y xy → * (zπ1 (F⊆pxq fx xy) ))
         fx→px1 : {p : HOD } {q : Ordinal } → odef Q q → (fp : filter F ∋  ZFP p Q ) → fx→px fp ≡ p
         fx→px1 {p} {q} qq fp = ==→o≡ record { eq→ = ty20 ; eq← = ty22 } where
             ty21 : {a b : Ordinal } → (pz : odef p a) → (qz : odef Q b) → ZFProduct P Q (& (* (& < * a , * b >)))
             ty21 pz qz = F⊆pxq fp (subst (odef (ZFP p Q)) (sym &iso) (ab-pair pz qz ))
             ty32 : {a b : Ordinal } → (pz : odef p a) → (qz : odef Q b) → zπ1 (ty21 pz qz) ≡ a
             ty32 {a} {b} pz qz  = ty33 (ty21 pz qz) (cong (&) *iso) where
                 ty33 : {a b x : Ordinal } ( p : ZFProduct P Q x ) → x ≡ & < * a , * b > → zπ1 p ≡ a
                 ty33 {a} {b} (ab-pair {c} {d} zp zq) eq with prod-≡ (subst₂ (λ j k → j ≡ k) *iso *iso (cong (*) eq))
                 ... | ⟪ a=c , b=d ⟫ = subst₂ (λ j k → j ≡ k) &iso &iso (cong (&) a=c)
             ty20 : {x : Ordinal} → odef (fx→px fp) x → odef p x
             ty20 {x} record { z = _ ; az = ab-pair {a} {b} pz qz ; x=ψz = x=ψz } = subst (λ k → odef p k) a=x pz  where
                 ty24 : * x  ≡ * a
                 ty24 = begin
                    * x ≡⟨ cong (*) x=ψz ⟩
                    _ ≡⟨ *iso  ⟩
                    * (zπ1 (F⊆pxq fp (subst (odef (ZFP p Q)) (sym &iso) (ab-pair pz qz)))) ≡⟨ cong (*) (ty32 pz qz) ⟩
                    * a ∎ where open ≡-Reasoning
                 a=x : a  ≡ x
                 a=x = subst₂ (λ j k → j ≡ k ) &iso &iso (cong (&) (sym ty24))
             ty22 : {x : Ordinal} → odef p x → odef (fx→px fp) x
             ty22 {x} px = record { z = _ ; az = ab-pair px qq ; x=ψz = subst₂ (λ j k → j ≡ k) &iso refl (cong (&) ty12 ) }  where
                 ty12 : * x ≡ * (zπ1 (F⊆pxq fp (subst (odef (ZFP p Q)) (sym &iso) (ab-pair px qq ))))
                 ty12 = begin
                    * x ≡⟨ sym (cong (*) (ty32 px qq )) ⟩
                    * (zπ1 (F⊆pxq fp (subst (odef (ZFP p Q)) (sym &iso) (ab-pair px qq )))) ∎ where open ≡-Reasoning

         --  Projection of F
         FPSet : HOD
         FPSet = Replace' (filter F) (λ x fx → Replace' x ( λ y xy → * (zπ1 (F⊆pxq fx xy) )))

         --  Projection ⁻¹  F (which is in F) is in FPSet
         FPSet∋zpq : {q : HOD} → q ⊆ P → filter F ∋  ZFP q Q → FPSet ∋ q
         FPSet∋zpq {q} q⊆P fq = record { z = _ ; az = fq ; x=ψz = sym (cong (&) ty10) } where
              -- brain damaged one
              ty11 : {y : HOD} {xy : (* (& (ZFP q Q))) ∋ y } →
                 * (zπ1 ( (F⊆pxq (subst (odef (filter F)) (sym &iso) fq) xy))) ≡ * (zπ1 ( (F⊆pxq fq (subst (λ k → odef k (& y)) *iso xy)  )))
              ty11 {y} {xy}  = cong (λ k → * (zπ1 k)) ( HE.≅-to-≡ (∋-irr {ZFP P Q} a b )) where
                 a = F⊆pxq (subst (odef (filter F)) (sym &iso) fq) xy
                 b = F⊆pxq fq (subst (λ k → odef k (& y)) *iso xy)
              ty10 : Replace' (* (& (ZFP q Q))) (λ y xy → * (zπ1 (F⊆pxq (subst (odef (filter F)) (sym &iso) fq) xy))) ≡ q
              ty10 = begin
                  Replace' (* (& (ZFP q Q))) (λ y xy → * (zπ1 (F⊆pxq (subst (odef (filter F)) (sym &iso) fq) xy)))
                     ≡⟨
                  cong (λ k → Replace' (* (& (ZFP q Q))) k ) (f-extensionality (λ y → (f-extensionality (λ xy → ty11 {y} {xy}))))
                      ⟩
                  Replace' (* (& (ZFP q Q))) (λ y xy → * (zπ1 (F⊆pxq fq (subst (λ k → odef k (& y)) *iso xy)  )))
                     ≡⟨ Replace'-iso _  ( λ y xy → * (zπ1 (F⊆pxq fq xy) )) ⟩
                  Replace' (ZFP q Q) ( λ y xy → * (zπ1 (F⊆pxq fq xy) )) ≡⟨ refl ⟩
                  fx→px fq ≡⟨ fx→px1 aq fq  ⟩
                  q ∎ where open ≡-Reasoning
         FPSet⊆PP :  FPSet  ⊆ Power P
         FPSet⊆PP {x} record { z = z ; az = fz ; x=ψz = x=ψz } w xw with subst (λ k → odef k w) (trans (cong (*) x=ψz) *iso) xw
         ... | record { z = z1 ; az = az1 ; x=ψz = x=ψz1 }
            = subst (λ k → odef P k) (sym (trans x=ψz1 &iso))
               (zp1 (F⊆pxq (subst (λ k → odef (filter F) k) (sym &iso) fz) (subst (λ k → odef (* z) k) (sym &iso) az1))  )
         X=F1 : (x : Ordinal) (p : HOD) (fx : odef (filter F) x) → Set n
         X=F1 x p fx = & p ≡ & (Replace' (* x) (λ y xy →
           * (zπ1 (f⊆L F
             (subst (odef (filter F)) (sym &iso) fx)
             (& y) (subst (λ k → OD.def (HOD.od k) (& y)) (sym *iso) xy)))))
         x⊆pxq : {x : Ordinal} {p : HOD} (fx : odef (filter F) x) → X=F1 x p fx → * x ⊆ ZFP p Q
         x⊆pxq {x} {p} fx x=ψz {w} xw with F⊆pxq (subst (λ k → odef (filter F) k) (sym &iso) fx) xw
         ... | ab-pair {a} {b} pw qw = ab-pair ty08 qw where
              ty21 : ZFProduct P Q (& (* (& < * a , * b >)))
              ty21 = subst (λ k → ZFProduct P Q k) (cong & (sym *iso)) (ab-pair pw qw)
              ty32 : ZFProduct P Q (& (* (& < * a , * b >)))
              ty32 = f⊆L F (subst (odef (filter F)) (sym &iso) fx)
                    (& (* (& < * a , * b >))) (subst (λ k → odef k
                    (& (* (& < * a , * b >)))) (sym *iso) (subst (odef (* x)) (sym &iso) xw))
              ty07 : odef (* x) (& < * a , * b >)
              ty07 = xw
              ty08 : odef p a
              ty08 = subst (λ k → odef k a ) (subst₂ (λ j k → j ≡ k) *iso *iso (sym (cong (*) x=ψz)))
                   record { z = _ ; az = xw ;  x=ψz = sym (trans &iso (ty33 ty32 (cong (&) *iso ))) } where
                 ty33 : {a b x : Ordinal } ( p : ZFProduct P Q x ) → x ≡ & < * a , * b > → zπ1 p ≡ a
                 ty33 {a} {b} (ab-pair {c} {d} zp zq) eq with prod-≡ (subst₂ (λ j k → j ≡ k) *iso *iso (cong (*) eq))
                 ... | ⟪ a=c , b=d ⟫ = subst₂ (λ j k → j ≡ k) &iso &iso (cong (&) a=c)
         p⊆P : {x : Ordinal} {p : HOD} (fx : odef (filter F) x) → X=F1 x p fx → p ⊆ P
         p⊆P {x} {p} fx x=ψz {w} pw with subst (λ k → odef k w) (subst₂ (λ j k → j ≡ k ) *iso *iso (cong (*) x=ψz))  pw
         ... | record { z = z1 ; az = az1 ; x=ψz = x=ψz1 } = subst (λ k → odef P k) (sym (trans x=ψz1 &iso))
               (zp1 (F⊆pxq (subst (λ k → odef (filter F) k) (sym &iso) fx) (subst (λ k → odef (* x) k) (sym &iso) az1 ))  )
         FP : Filter {Power P} {P} (λ x → x)
         FP = record { filter = FPSet ; f⊆L = FPSet⊆PP ; filter1 = ty01 ; filter2 = ty02 } where
             ty01 : {p q : HOD} → Power P ∋ q → FPSet ∋ p → p ⊆ q → FPSet ∋ q
             ty01 {p} {q} Pq record { z = x ; az = fx ; x=ψz = x=ψz } p⊆q = FPSet∋zpq q⊆P (ty10 ty05 ty06 )
                where
                  --  p ≡ (Replace' (* x) (λ y xy → (zπ1 (F⊆pxq (subst (odef (filter F)) (sym &iso) fx) xy))
                  --  x = ( px , qx )  , px ⊆ q
                  ty03 : Power (ZFP P Q) ∋ ZFP q Q
                  ty03 z zpq = isP→PxQ {* (& q)} (Pq _) ( subst (λ k → odef k z ) (trans *iso (cong (λ k → ZFP k Q) (sym *iso))) zpq )
                  q⊆P : q ⊆ P
                  q⊆P {w} qw = Pq _ (subst (λ k → odef k w ) (sym *iso) qw )
                  ty05 : filter F ∋  ZFP p Q
                  ty05 = filter1 F (λ z wz → isP→PxQ (p⊆P fx x=ψz) (subst (λ k → odef k z) *iso wz)) (subst (λ k → odef (filter F) k) (sym &iso) fx) (x⊆pxq fx x=ψz)
                  ty06 : ZFP p Q ⊆ ZFP q Q
                  ty06 (ab-pair wp wq ) = ab-pair (p⊆q wp) wq
                  ty10 : filter F ∋ ZFP p Q → ZFP p Q ⊆ ZFP q Q → filter F ∋  ZFP q Q
                  ty10 fzp zp⊆zq = filter1 F ty03 fzp zp⊆zq
             ty02 : {p q : HOD} → FPSet ∋ p → FPSet ∋ q → Power P ∋ (p ∩ q) → FPSet ∋ (p ∩ q)
             ty02 {p} {q} record { z = zp ; az = fzp ; x=ψz = x=ψzp }
                          record { z = zq ; az = fzq ; x=ψz = x=ψzq } Ppq
                = FPSet∋zpq (λ {z} xz → Ppq z (subst (λ k → odef k z) (sym *iso) xz )) ty50 where
                  ty54 : Power (ZFP P Q) ∋ (ZFP p Q ∩ ZFP q Q)
                  ty54 z xz = subst (λ k → ZFProduct P Q k ) (zp-iso pqz) (ab-pair pqz1 pqz2 ) where
                     pqz :  odef (ZFP (p ∩ q) Q)  z
                     pqz = subst (λ k → odef k z ) (trans *iso (sym (proj1 ZFP∩) ))  xz
                     pqz1 : odef P (zπ1 pqz)
                     pqz1 = p⊆P fzp x=ψzp (proj1 (zp1 pqz))
                     pqz2 : odef Q (zπ2 pqz)
                     pqz2 = zp2 pqz
                  ty53 : filter F ∋ ZFP p Q
                  ty53 = filter1 F (λ z wz → isP→PxQ (p⊆P fzp x=ψzp)
                     (subst (λ k → odef k z) *iso wz))
                     (subst (λ k → odef (filter F) k) (sym &iso) fzp ) (x⊆pxq fzp x=ψzp)
                  ty52 : filter F ∋ ZFP q Q
                  ty52 = filter1 F (λ z wz → isP→PxQ (p⊆P fzq x=ψzq)
                     (subst (λ k → odef k z) *iso wz))
                     (subst (λ k → odef (filter F) k) (sym &iso) fzq ) (x⊆pxq fzq x=ψzq)
                  ty51 : filter F ∋ ( ZFP p Q ∩ ZFP q Q )
                  ty51 = filter2 F ty53 ty52 ty54
                  ty50 : filter F ∋ ZFP (p ∩ q) Q
                  ty50 = subst (λ k → filter F ∋ k ) (sym (proj1 ZFP∩)) ty51
         UFP : ultra-filter FP
         UFP = record { proper = ty61 ; ultra = ty60 } where
            ty61 : ¬ (FPSet ∋ od∅)
            ty61 record { z = z ; az = az ; x=ψz = x=ψz } = ultra-filter.proper UF ty62 where
               ty63 : {x : Ordinal} → ¬ odef (* z) x
               ty63 {x} zx with x⊆pxq az x=ψz zx
               ... | ab-pair xp xq = ¬x<0 xp
               ty62 : odef (filter F) (& od∅)
               ty62 = subst (λ k → odef (filter F) k ) (trans (sym &iso) (cong (&) (¬x∋y→x≡od∅ ty63)) ) az
            ty60 : {p : HOD} → Power P ∋ p → Power P ∋ (P ＼ p) → (FPSet ∋ p) ∨ (FPSet ∋ (P ＼ p))
            ty60 {p} Pp Pnp with ultra-filter.ultra UF {ZFP p Q}
                (λ z xz → isP→PxQ (λ {x} lt → Pp _ (subst (λ k → odef k x) (sym *iso) lt)) (subst (λ k → odef k z) *iso xz))
                (λ z xz → proj1 (subst (λ k → odef k z) *iso xz ))
            ... | case1 fp  = case1 (FPSet∋zpq (λ {z} xz → Pp z (subst (λ k → odef k z) (sym *iso) xz )) fp )
            ... | case2 fnp = case2 (FPSet∋zpq (λ pp → proj1 pp)  (subst (λ k → odef (filter F) k) (cong (&) (proj1 ZFP\Q)) fnp ))
         uflp : UFLP TP FP UFP
         uflp = FIP→UFLP TP (Compact→FIP TP CP) FP UFP

         --  FPSet is in Projection ⁻¹  F
         FPSet⊆F : {x : Ordinal } → odef FPSet x →  odef (filter F) (& (ZFP (* x) Q))
         FPSet⊆F {x} record { z = z ; az = az ; x=ψz = x=ψz } = filter1 F ty80 (subst (λ k → odef (filter F) k) (sym &iso) az) ty71 where
             Rx : HOD
             Rx = Replace' (* z) (λ y xy → * (zπ1 (F⊆pxq (subst (odef (filter F)) (sym &iso) az) xy)))
             RxQ∋z : * z ⊆ ZFP Rx Q 
             RxQ∋z {w} zw = subst (λ k → ZFProduct Rx Q k ) ty70 ( ab-pair record { z = w ; az = zw ; x=ψz = refl  } (zp2 b )) where
                 a = F⊆pxq (subst (odef (filter F)) (sym &iso) az) (subst (odef (* z)) (sym &iso) zw) 
                 b = subst (λ k → odef (ZFP P Q) k ) (sym &iso) ( f⊆L F az w zw )
                 ty73 : & (* (zπ1 a)) ≡ zπ1 b 
                 ty73 = begin
                     & (* (zπ1 a)) ≡⟨ &iso ⟩ 
                     zπ1 a ≡⟨ cong zπ1 (HE.≅-to-≡ (∋-irr {ZFP _ _ } a b)) ⟩ 
                     zπ1 b ∎  where open ≡-Reasoning
                 ty70 : & < * (& (* (zπ1 a))) , * (zπ2 b) > ≡ w
                 ty70 with zp-iso (subst (λ k → odef (ZFP P Q) k) (sym &iso) (f⊆L F az _ zw )) 
                 ... | eq = trans (cong₂ (λ j k → & < * j , k > ) ty73  refl ) (trans eq &iso ) 
             ty71 : * z ⊆ ZFP (* x) Q
             ty71 = subst (λ k → * z ⊆ ZFP k Q) ty72 RxQ∋z where
                 ty72 : Rx ≡ * x 
                 ty72 = begin
                    Rx ≡⟨ sym *iso ⟩
                    * (& Rx)  ≡⟨ cong (*) (sym x=ψz ) ⟩
                    * x ∎ where open ≡-Reasoning
             ty80 : Power (ZFP P Q) ∋ ZFP (* x) Q
             ty80 y yx = isP→PxQ ty81 (subst (λ k → odef k y ) *iso yx ) where
                 ty81 : * x ⊆ P 
                 ty81 {w} xw with subst (λ k → odef k w) (trans (cong (*) x=ψz ) *iso ) xw
                 ... | record { z = z1 ; az = az1 ; x=ψz = x=ψz1 } = subst (λ k → odef P k) (sym ty84) ty87 where
                      a =  f⊆L F (subst (odef (filter F)) (sym &iso) az) (& (* z1)) 
                                 (subst (λ k → odef k (& (* z1))) (sym *iso) (subst (odef (* z)) (sym &iso) az1))
                      b = subst (λ k → odef (ZFP P Q) k ) (sym &iso) (f⊆L F az _ az1 )
                      ty87 : odef P (zπ1 b)
                      ty87 = zp1 b
                      ty84 : w ≡ (zπ1 b)
                      ty84 = begin
                       w ≡⟨ trans x=ψz1 &iso ⟩
                       zπ1 a ≡⟨ cong zπ1 (HE.≅-to-≡ (∋-irr {ZFP _ _ } a b )) ⟩
                       zπ1 b  ∎ where open ≡-Reasoning

         --  copy and pasted, sorry
         --
         isQ→PxQ : {x : HOD} → (x⊆Q : x ⊆ Q ) → ZFP P x  ⊆ ZFP P Q
         isQ→PxQ {x} x⊆Q (ab-pair p q) = ab-pair p (x⊆Q q)
         fx→qx : {x : HOD } → filter F ∋ x → HOD
         fx→qx {x} fx = Replace' x ( λ y xy → * (zπ2 (F⊆pxq fx xy) ))
         fx→qx1 : {q : HOD } {p : Ordinal } → odef P p → (fq : filter F ∋  ZFP P q ) → fx→qx fq ≡ q
         fx→qx1 {q} {p} qq fq = ==→o≡ record { eq→ = ty20 ; eq← = ty22 } where
             ty21 : {a b : Ordinal } → (qz : odef q b) → (pz : odef P a) → ZFProduct P Q (& (* (& < * a , * b >)))
             ty21 qz pz = F⊆pxq fq (subst (odef (ZFP P q)) (sym &iso) (ab-pair pz qz ))
             ty32 : {a b : Ordinal } → (qz : odef q b) → (pz : odef P a) → zπ2 (ty21 qz pz) ≡ b
             ty32 {a} {b} pz qz  = ty33 (ty21 pz qz) (cong (&) *iso) where
                 ty33 : {a b x : Ordinal } ( q : ZFProduct P Q x ) → x ≡ & < * a , * b > → zπ2 q ≡ b
                 ty33 {a} {b} (ab-pair {c} {d} zp zq) eq with prod-≡ (subst₂ (λ j k → j ≡ k) *iso *iso (cong (*) eq))
                 ... | ⟪ a=c , b=d ⟫ = subst₂ (λ j k → j ≡ k) &iso &iso (cong (&) b=d)
             ty20 : {x : Ordinal} → odef (fx→qx fq) x → odef q x
             ty20 {x} record { z = _ ; az = ab-pair {a} {b} pz qz ; x=ψz = x=ψz } = subst (λ k → odef q k) b=x qz  where
                 ty24 : * x  ≡ * b
                 ty24 = begin
                    * x ≡⟨ cong (*) x=ψz ⟩
                    _ ≡⟨ *iso  ⟩
                    * (zπ2 (F⊆pxq fq (subst (odef (ZFP P q)) (sym &iso) (ab-pair pz qz)))) ≡⟨ cong (*) (ty32 qz pz) ⟩
                    * b ∎ where open ≡-Reasoning
                 b=x : b  ≡ x
                 b=x = subst₂ (λ j k → j ≡ k ) &iso &iso (cong (&) (sym ty24))
             ty22 : {x : Ordinal} → odef q x → odef (fx→qx fq) x
             ty22 {x} qx = record { z = _ ; az = ab-pair qq qx ; x=ψz = subst₂ (λ j k → j ≡ k) &iso refl (cong (&) ty12 ) }  where
                 ty12 : * x ≡ * (zπ2 (F⊆pxq fq (subst (odef (ZFP P q)) (sym &iso) (ab-pair qq qx ))))
                 ty12 = begin
                    * x ≡⟨ sym (cong (*) (ty32 qx qq )) ⟩
                    * (zπ2 (F⊆pxq fq (subst (odef (ZFP P q)) (sym &iso) (ab-pair qq qx )))) ∎ where open ≡-Reasoning
         FQSet : HOD
         FQSet = Replace' (filter F) (λ x fx → Replace' x ( λ y xy → * (zπ2 (F⊆pxq fx xy) )))
         FQSet∋zpq : {q : HOD} → q ⊆ Q → filter F ∋  ZFP P q → FQSet ∋ q
         FQSet∋zpq {q} q⊆P fq = record { z = _ ; az = fq ; x=ψz = sym (cong (&) ty10) } where
              -- brain damaged one
              ty11 : {y : HOD} {xy : (* (& (ZFP P q ))) ∋ y } →
                 * (zπ2 ( (F⊆pxq (subst (odef (filter F)) (sym &iso) fq) xy))) ≡ * (zπ2 ( (F⊆pxq fq (subst (λ k → odef k (& y)) *iso xy)  )))
              ty11 {y} {xy}  = cong (λ k → * (zπ2 k)) ( HE.≅-to-≡ (∋-irr {ZFP P Q} a b )) where
                 a = F⊆pxq (subst (odef (filter F)) (sym &iso) fq) xy
                 b = F⊆pxq fq (subst (λ k → odef k (& y)) *iso xy)
              ty10 : Replace' (* (& (ZFP P q ))) (λ y xy → * (zπ2 (F⊆pxq (subst (odef (filter F)) (sym &iso) fq) xy))) ≡ q
              ty10 = begin
                  Replace' (* (& (ZFP P q))) (λ y xy → * (zπ2 (F⊆pxq (subst (odef (filter F)) (sym &iso) fq) xy)))
                     ≡⟨
                  cong (λ k → Replace' (* (& (ZFP P q ))) k ) (f-extensionality (λ y → (f-extensionality (λ xy → ty11 {y} {xy}))))
                      ⟩
                  Replace' (* (& (ZFP P q))) (λ y xy → * (zπ2 (F⊆pxq fq (subst (λ k → odef k (& y)) *iso xy)  )))
                     ≡⟨ Replace'-iso _  ( λ y xy → * (zπ2 (F⊆pxq fq xy) )) ⟩
                  Replace' (ZFP P q ) ( λ y xy → * (zπ2 (F⊆pxq fq xy) )) ≡⟨ refl ⟩
                  fx→qx fq ≡⟨ fx→qx1 ap fq  ⟩
                  q ∎ where open ≡-Reasoning
         FQSet⊆PP :  FQSet  ⊆ Power Q
         FQSet⊆PP {x} record { z = z ; az = fz ; x=ψz = x=ψz } w xw with subst (λ k → odef k w) (trans (cong (*) x=ψz) *iso) xw
         ... | record { z = z1 ; az = az1 ; x=ψz = x=ψz1 }
            = subst (λ k → odef Q k) (sym (trans x=ψz1 &iso))
               (zp2 (F⊆pxq (subst (λ k → odef (filter F) k) (sym &iso) fz) (subst (λ k → odef (* z) k) (sym &iso) az1))  )
         X=F2 : (x : Ordinal) (q : HOD) (fx : odef (filter F) x) → Set n
         X=F2 x q fx = & q ≡ & (Replace' (* x) (λ y xy →
           * (zπ2 (f⊆L F
             (subst (odef (filter F)) (sym &iso) fx)
             (& y) (subst (λ k → OD.def (HOD.od k) (& y)) (sym *iso) xy)))))
         x⊆qxq : {x : Ordinal} {q : HOD} (fx : odef (filter F) x) → X=F2 x q fx → * x ⊆ ZFP P q
         x⊆qxq {x} {p} fx x=ψz {w} xw with F⊆pxq (subst (λ k → odef (filter F) k) (sym &iso) fx) xw
         ... | ab-pair {a} {b} pw qw = ab-pair pw ty08 where
              ty21 : ZFProduct P Q (& (* (& < * a , * b >)))
              ty21 = subst (λ k → ZFProduct P Q k) (cong & (sym *iso)) (ab-pair pw qw)
              ty32 : ZFProduct P Q (& (* (& < * a , * b >)))
              ty32 = f⊆L F (subst (odef (filter F)) (sym &iso) fx)
                    (& (* (& < * a , * b >))) (subst (λ k → odef k
                    (& (* (& < * a , * b >)))) (sym *iso) (subst (odef (* x)) (sym &iso) xw))
              ty07 : odef (* x) (& < * a , * b >)
              ty07 = xw
              ty08 : odef p b
              ty08 = subst (λ k → odef k b ) (subst₂ (λ j k → j ≡ k) *iso *iso (sym (cong (*) x=ψz)))
                   record { z = _ ; az = xw ;  x=ψz = sym (trans &iso (ty33 ty32 (cong (&) *iso ))) } where
                 ty33 : {a b x : Ordinal } ( p : ZFProduct P Q x ) → x ≡ & < * a , * b > → zπ2 p ≡ b
                 ty33 {a} {b} (ab-pair {c} {d} zp zq) eq with prod-≡ (subst₂ (λ j k → j ≡ k) *iso *iso (cong (*) eq))
                 ... | ⟪ a=c , b=d ⟫ = subst₂ (λ j k → j ≡ k) &iso &iso (cong (&) b=d)
         q⊆Q : {x : Ordinal} {p : HOD} (fx : odef (filter F) x) → X=F2 x p fx → p ⊆ Q
         q⊆Q {x} {p} fx x=ψz {w} pw with subst (λ k → odef k w) (subst₂ (λ j k → j ≡ k ) *iso *iso (cong (*) x=ψz))  pw
         ... | record { z = z1 ; az = az1 ; x=ψz = x=ψz1 } = subst (λ k → odef Q k) (sym (trans x=ψz1 &iso))
               (zp2 (F⊆pxq (subst (λ k → odef (filter F) k) (sym &iso) fx) (subst (λ k → odef (* x) k) (sym &iso) az1 ))  )
         FQ : Filter {Power Q} {Q} (λ x → x)
         FQ = record { filter = FQSet ; f⊆L = FQSet⊆PP ; filter1 = ty01 ; filter2 = ty02 } where
             ty01 : {p q : HOD} → Power Q ∋ q → FQSet ∋ p → p ⊆ q → FQSet ∋ q
             ty01 {p} {q} Pq record { z = x ; az = fx ; x=ψz = x=ψz } p⊆q = FQSet∋zpq q⊆P (ty10 ty05 ty06 )
                where
                  --  p ≡ (Replace' (* x) (λ y xy → (zπ2 (F⊆qxq (subst (odef (filter F)) (sym &iso) fx) xy))
                  --  x = ( px , qx )  , qx ⊆ q
                  ty03 : Power (ZFP P Q) ∋ ZFP P q
                  ty03 z zpq = isQ→PxQ {* (& q)} (Pq _) ( subst (λ k → odef k z ) (trans *iso (cong (λ k → ZFP P k ) (sym *iso))) zpq )
                  q⊆P : q ⊆ Q
                  q⊆P {w} qw = Pq _ (subst (λ k → odef k w ) (sym *iso) qw )
                  ty05 : filter F ∋  ZFP P p
                  ty05 = filter1 F (λ z wz → isQ→PxQ (q⊆Q fx x=ψz) (subst (λ k → odef k z) *iso wz)) (subst (λ k → odef (filter F) k) (sym &iso) fx) (x⊆qxq fx x=ψz)
                  ty06 : ZFP P p ⊆ ZFP P q
                  ty06 (ab-pair wp wq ) = ab-pair wp (p⊆q wq)
                  ty10 : filter F ∋ ZFP P p → ZFP P p ⊆ ZFP P q → filter F ∋  ZFP P q
                  ty10 fzp zp⊆zq = filter1 F ty03 fzp zp⊆zq
             ty02 : {p q : HOD} → FQSet ∋ p → FQSet ∋ q → Power Q ∋ (p ∩ q) → FQSet ∋ (p ∩ q)
             ty02 {p} {q} record { z = zp ; az = fzp ; x=ψz = x=ψzp }
                          record { z = zq ; az = fzq ; x=ψz = x=ψzq } Ppq
                = FQSet∋zpq (λ {z} xz → Ppq z (subst (λ k → odef k z) (sym *iso) xz )) ty50 where
                  ty54 : Power (ZFP P Q) ∋ (ZFP P p ∩ ZFP P q )
                  ty54 z xz = subst (λ k → ZFProduct P Q k ) (zp-iso pqz) (ab-pair pqz1 pqz2 ) where
                     pqz :  odef (ZFP P (p ∩ q) )  z
                     pqz = subst (λ k → odef k z ) (trans *iso (sym (proj2 ZFP∩) ))  xz
                     pqz1 : odef P (zπ1 pqz)
                     pqz1 = zp1 pqz
                     pqz2 : odef Q (zπ2 pqz)
                     pqz2 = q⊆Q fzp x=ψzp (proj1 (zp2 pqz))
                  ty53 : filter F ∋ ZFP P p
                  ty53 = filter1 F (λ z wz → isQ→PxQ (q⊆Q fzp x=ψzp)
                     (subst (λ k → odef k z) *iso wz))
                     (subst (λ k → odef (filter F) k) (sym &iso) fzp ) (x⊆qxq fzp x=ψzp)
                  ty52 : filter F ∋ ZFP P q
                  ty52 = filter1 F (λ z wz → isQ→PxQ (q⊆Q fzq x=ψzq)
                     (subst (λ k → odef k z) *iso wz))
                     (subst (λ k → odef (filter F) k) (sym &iso) fzq ) (x⊆qxq fzq x=ψzq)
                  ty51 : filter F ∋ ( ZFP P p ∩ ZFP P q )
                  ty51 = filter2 F ty53 ty52 ty54
                  ty50 : filter F ∋ ZFP P (p ∩ q)
                  ty50 = subst (λ k → filter F ∋ k ) (sym (proj2 ZFP∩)) ty51
         UFQ : ultra-filter FQ
         UFQ = record { proper = ty61 ; ultra = ty60 } where
            ty61 : ¬ (FQSet ∋ od∅)
            ty61 record { z = z ; az = az ; x=ψz = x=ψz } = ultra-filter.proper UF ty62 where
               ty63 : {x : Ordinal} → ¬ odef (* z) x
               ty63 {x} zx with x⊆qxq az x=ψz zx
               ... | ab-pair xp xq = ¬x<0 xq
               ty62 : odef (filter F) (& od∅)
               ty62 = subst (λ k → odef (filter F) k ) (trans (sym &iso) (cong (&) (¬x∋y→x≡od∅ ty63)) ) az
            ty60 : {p : HOD} → Power Q ∋ p → Power Q ∋ (Q ＼ p) → (FQSet ∋ p) ∨ (FQSet ∋ (Q ＼ p))
            ty60 {q} Pp Pnp with ultra-filter.ultra UF {ZFP P q}
                (λ z xz → isQ→PxQ (λ {x} lt → Pp _ (subst (λ k → odef k x) (sym *iso) lt)) (subst (λ k → odef k z) *iso xz))
                (λ z xz → proj1 (subst (λ k → odef k z) *iso xz ))
            ... | case1 fq  = case1 (FQSet∋zpq (λ {z} xz → Pp z (subst (λ k → odef k z) (sym *iso) xz )) fq )
            ... | case2 fnp = case2 (FQSet∋zpq (λ pp → proj1 pp)  (subst (λ k → odef (filter F) k) (cong (&) (proj2 ZFP\Q)) fnp ))


         --  FQSet is in Projection ⁻¹  F
         FQSet⊆F : {x : Ordinal } → odef FQSet x →  odef (filter F) (& (ZFP P (* x) ))
         FQSet⊆F {x} record { z = z ; az = az ; x=ψz = x=ψz } = filter1 F ty80 (subst (λ k → odef (filter F) k) (sym &iso) az) ty71 where
             Rx : HOD
             Rx = Replace' (* z) (λ y xy → * (zπ2 (F⊆pxq (subst (odef (filter F)) (sym &iso) az) xy)))
             PxRx∋z : * z ⊆ ZFP P Rx  
             PxRx∋z {w} zw = subst (λ k → ZFProduct P Rx k ) ty70 ( ab-pair (zp1 b) record { z = w ; az = zw ; x=ψz = refl } ) where
                 a = F⊆pxq (subst (odef (filter F)) (sym &iso) az) (subst (odef (* z)) (sym &iso) zw) 
                 b = subst (λ k → odef (ZFP P Q) k ) (sym &iso) ( f⊆L F az w zw )
                 ty73 : & (* (zπ2 a)) ≡ zπ2 b 
                 ty73 = begin
                     & (* (zπ2 a)) ≡⟨ &iso ⟩ 
                     zπ2 a ≡⟨ cong zπ2 (HE.≅-to-≡ (∋-irr {ZFP _ _ } a b)) ⟩ 
                     zπ2 b ∎  where open ≡-Reasoning
                 ty70 : & < * (zπ1 b) , * (& (* (zπ2 a)))  > ≡ w
                 ty70 with zp-iso (subst (λ k → odef (ZFP P Q) k) (sym &iso) (f⊆L F az _ zw )) 
                 ... | eq = trans (cong₂ (λ j k → & < j , * k > ) refl ty73 ) (trans eq &iso ) 
             ty71 : * z ⊆ ZFP P (* x) 
             ty71 = subst (λ k → * z ⊆ ZFP P k ) ty72 PxRx∋z where
                 ty72 : Rx ≡ * x 
                 ty72 = begin
                    Rx ≡⟨ sym *iso ⟩
                    * (& Rx)  ≡⟨ cong (*) (sym x=ψz ) ⟩
                    * x ∎ where open ≡-Reasoning
             ty80 : Power (ZFP P Q) ∋ ZFP P (* x) 
             ty80 y yx = isQ→PxQ ty81 (subst (λ k → odef k y ) *iso yx ) where
                 ty81 : * x ⊆ Q 
                 ty81 {w} xw with subst (λ k → odef k w) (trans (cong (*) x=ψz ) *iso ) xw
                 ... | record { z = z1 ; az = az1 ; x=ψz = x=ψz1 } = subst (λ k → odef Q k) (sym ty84) ty87 where
                      a =  f⊆L F (subst (odef (filter F)) (sym &iso) az) (& (* z1)) 
                                 (subst (λ k → odef k (& (* z1))) (sym *iso) (subst (odef (* z)) (sym &iso) az1))
                      b = subst (λ k → odef (ZFP P Q) k ) (sym &iso) (f⊆L F az _ az1 )
                      ty87 : odef Q (zπ2 b)
                      ty87 = zp2 b
                      ty84 : w ≡ (zπ2 b)
                      ty84 = begin
                       w ≡⟨ trans x=ψz1 &iso ⟩
                       zπ2 a ≡⟨ cong zπ2 (HE.≅-to-≡ (∋-irr {ZFP _ _ } a b )) ⟩
                       zπ2 b  ∎ where open ≡-Reasoning


         uflq : UFLP TQ FQ UFQ
         uflq = FIP→UFLP TQ (Compact→FIP TQ CQ) FQ UFQ

         Pf : odef (ZFP P Q) (& < * (UFLP.limit uflp) , * (UFLP.limit uflq) >)
         Pf = ab-pair (UFLP.P∋limit uflp) (UFLP.P∋limit uflq)

         isL : {v : Ordinal} → Neighbor (ProductTopology TP TQ) (& < * (UFLP.limit uflp) , * (UFLP.limit uflq) >) v → filter F ∋ * v
         isL {v} nei = filter1 F (λ z xz → Neighbor.v⊆P nei (subst (λ k → odef k z) *iso xz))
                (subst (λ k → odef (filter F) k) (sym &iso) (F∋base pqb b∋l )) bpq⊆v where
             --
             -- Product Topolgy's open set contains a subbase which is an element of ZPF p Q or ZPF P q
             --   Neighbor of limit contains an open set which conatins a limit
             --   every point of an open set is covered by a subbase
             --   so there is a subbase which contains a limit, the subbase is an element of projection of a filter (P or Q)
             TPQ = ProductTopology TP TQ
             lim = & < * (UFLP.limit uflp) , * (UFLP.limit uflq) >
             bpq : Base (ZFP P Q) (pbase TP TQ) (Neighbor.u nei) (& < * (UFLP.limit uflp) , * (UFLP.limit uflq) >)
             bpq = Neighbor.ou nei (Neighbor.ux nei)
             b∋l : odef (* (Base.b bpq)) lim
             b∋l = Base.bx bpq 
             pqb : Subbase (pbase TP TQ) (Base.b bpq )
             pqb = Base.sb bpq
             pqb⊆opq : * (Base.b bpq) ⊆ * ( Neighbor.u nei )
             bpq⊆v : * (Base.b bpq) ⊆ * v
             bpq⊆v {x} bx = Neighbor.u⊆v nei (pqb⊆opq bx)
             pqb⊆opq = Base.b⊆u bpq
             F∋base : {b : Ordinal } →  Subbase (pbase TP TQ) b → odef (* b) lim → odef (filter F) b
             F∋base {b} (gi (case1 px)) bl  = subst (λ k → odef (filter F) k) (sym (BaseP.prod px)) f∋b where
                 -- 
                 --  subbase of product topology which includes lim is in FP, so in F
                 --
                 isl00 : odef (ZFP (* (BaseP.p px)) Q) lim
                 isl00 = subst (λ k → odef k lim ) (trans (cong (*) (BaseP.prod px)) *iso )  bl
                 px∋limit : odef (* (BaseP.p px)) (UFLP.limit uflp)
                 px∋limit = isl01 isl00 refl where
                    isl01 : {x : Ordinal } → odef (ZFP (* (BaseP.p px)) Q) x → x ≡ lim →  odef (* (BaseP.p px)) (UFLP.limit uflp)
                    isl01 (ab-pair {a} {b} bx qx) ab=lim = subst (λ k → odef (* (BaseP.p px)) k) a=lim bx where
                       a=lim : a ≡ UFLP.limit uflp
                       a=lim = subst₂ (λ j k → j ≡ k ) &iso &iso (cong (&) (proj1 ( prod-≡ (subst₂ (λ j k → j ≡ k ) *iso *iso (cong (*) ab=lim) ) )))
                 fp∋b : filter FP ∋ * (BaseP.p px)
                 fp∋b = UFLP.is-limit uflp record { u = _ ; ou = BaseP.op px ; ux = px∋limit
                     ; v⊆P = λ {x} lt → os⊆L TP (subst (λ k → odef (OS TP) k) (sym &iso) (BaseP.op px)) lt ; u⊆v = λ x → x }
                 f∋b : odef (filter F) (& (ZFP (* (BaseP.p px)) Q))
                 f∋b = FPSet⊆F  (subst (λ k → odef (filter FP) k ) &iso fp∋b )
             F∋base {b} (gi (case2 qx)) bl  = subst (λ k → odef (filter F) k) (sym (BaseQ.prod qx)) f∋b where
                 isl00 : odef (ZFP P (* (BaseQ.q qx))) lim
                 isl00 = subst (λ k → odef k lim ) (trans (cong (*) (BaseQ.prod qx)) *iso )  bl
                 qx∋limit : odef (* (BaseQ.q qx)) (UFLP.limit uflq)
                 qx∋limit = isl01 isl00 refl where
                    isl01 : {x : Ordinal } → odef (ZFP P (* (BaseQ.q qx)) ) x → x ≡ lim →  odef (* (BaseQ.q qx)) (UFLP.limit uflq)
                    isl01 (ab-pair {a} {b} px bx) ab=lim = subst (λ k → odef (* (BaseQ.q qx)) k) b=lim bx where
                       b=lim : b ≡ UFLP.limit uflq
                       b=lim = subst₂ (λ j k → j ≡ k ) &iso &iso (cong (&) (proj2 ( prod-≡ (subst₂ (λ j k → j ≡ k ) *iso *iso (cong (*) ab=lim) ) )))
                 fp∋b : filter FQ ∋ * (BaseQ.q qx)
                 fp∋b = UFLP.is-limit uflq record { u = _ ; ou = BaseQ.oq qx ; ux = qx∋limit
                     ; v⊆P = λ {x} lt → os⊆L TQ (subst (λ k → odef (OS TQ) k) (sym &iso) (BaseQ.oq qx)) lt ; u⊆v = λ x → x }
                 f∋b : odef (filter F) (& (ZFP P (* (BaseQ.q qx)) ))
                 f∋b = FQSet⊆F  (subst (λ k → odef (filter FQ) k ) &iso fp∋b )
             F∋base (g∩ {x} {y} b1 b2) bl = F∋x∩y where
                 -- filter contains finite intersection
                 fb01 :  odef (filter F) x
                 fb01 = F∋base b1 (proj1 (subst (λ k → odef k lim) *iso bl))
                 fb02 :  odef (filter F) y
                 fb02 = F∋base b2 (proj2 (subst (λ k → odef k lim) *iso bl))
                 F∋x∩y : odef (filter F) (& (* x ∩ * y))
                 F∋x∩y = filter2 F (subst (λ k → odef (filter F) k) (sym &iso) fb01) (subst (λ k → odef (filter F) k) (sym &iso) fb02)
                    (CAP (ZFP P Q) (subst (λ k → odef (Power (ZFP P Q)) k) (sym &iso) (f⊆L F fb01))
                                   (subst (λ k → odef (Power (ZFP P Q)) k) (sym &iso) (f⊆L F fb02)))






