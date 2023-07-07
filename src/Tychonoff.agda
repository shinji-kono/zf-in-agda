{-# OPTIONS --allow-unsolved-metas #-}
open import Level
open import Ordinals
module Tychonoff {n : Level } (O : Ordinals {n})   where

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
-- open Ordinals.IsNext isNext
open OrdUtil O
open ODUtil O

import ODC
open ODC O

open import filter O
open import filter-util O
open import ZProduct O
open import Topology O
open import maximum-filter O

open Filter
open Topology

--
-- Tychonoff : {P Q : HOD } → (TP : Topology P) → (TQ : Topology Q)  
--      → Compact TP → Compact TQ   → Compact (ProductTopology TP TQ)
--
-- ULFP : Compact <=> Every ultra filter F have a limit i.e. open sets which contains the limit (Neighbor limit)  is in F
--
-- Tychonoff {P} {Q} TP TQ CP CQ = FIP→Compact (ProductTopology TP TQ) (UFLP→FIP (ProductTopology TP TQ) uflPQ ) where
--
--     FP FQ : create projections of a filter F, so it is ULFP
--
--         Pf : odef (ZFP P Q) (& < * (UFLP.limit uflp) , * (UFLP.limit uflq) >)
--    
--     the product of each limits must be a limit of ultra filter F
--
--     its neighbor is in F, because we can decompose Neighbors nei into subbase of Product Topology which is a open set of P ∋ p or Q ∋ q
--     so (P x q) ∋ limit ∨ (q x P) ∋ limit. P x q ⊆ nei , so nei ∋ limit
--
--     uflPQ :  (F : Filter {Power (ZFP P Q)} {ZFP P Q} (λ x → x))  (UF : ultra-filter F)
--             → UFLP (ProductTopology TP TQ) F UF
--
--     QED.

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

-- If any ultrafilter has a limit such that all its neighbors
-- are within the filter, it possesses the finite intersection
-- property (FIP). 

-- The finite intersection property defines a filter, and through Zorn's lemma, 
-- we can maximize it to obtain an ultrafilter. 
-- If the limit of the filter is not contained within a closed
-- set 'p' in the FIP, then it must be in the complement of 'p'
-- (P \ p). Since this complement is open and contains the limit,
-- it is included in the ultrafilter. However, this implies that
-- both 'p' and its complement (P \ p) are present in the filter,
-- which contradicts the proper characteristic of the ultrafilter,
-- meaning that the filter contains no empty set. 

--
UFLP→FIP : {P : HOD} (TP : Topology P) →
   ((F : Filter {Power P} {P} (λ x → x) ) (UF : ultra-filter F ) → UFLP TP F UF ) → FIP TP
UFLP→FIP {P} TP uflp with trio< (& P) o∅
... | tri< a ¬b ¬c = ⊥-elim ( ¬x<0 a )
... | tri≈ ¬a P=0 ¬c = record { limit = λ CX fip → o∅ ; is-limit = fip03 } where
   -- P is empty ( this case cannot happen because ulfp → 0 < P )
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
     -- filter base is not empty,  it is necessary to maximize fip filter 
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

     0<PP : o∅ o< & (Power P)     -- Power P contaisn od∅, so it is not empty
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
     -- then we have maximum ultra filter ( Zorn lemma )
     --    to debug this file, commet out the maximum filter and open import
     --    otherwise the check requires a minute
     --
     maxf : {X : Ordinal} → o∅ o< X → (CSX : * X ⊆ CS TP) → (fp : fip {X} CSX) → MaximumFilter (λ x → x) (F CSX fp)
     maxf {X} 0<X CSX fp = F→Maximum {Power P} {P} (λ x → x) (CAP P)  (F CSX fp) 0<PP (N∋nc 0<X CSX fp) (proper CSX fp)
     mf : {X : Ordinal} → o∅ o< X → (CSX : * X ⊆ CS TP) → (fp : fip {X} CSX) → Filter {Power P} {P} (λ x → x)
     mf {X} 0<X CSX fp =  ? -- MaximumFilter.mf (maxf 0<X CSX fp)
     ultraf : {X : Ordinal} → (0<X : o∅ o< X ) → (CSX : * X ⊆ CS TP) → (fp : fip {X} CSX) → ultra-filter ( mf 0<X CSX fp)
     ultraf {X} 0<X CSX fp = F→ultra {Power P} {P} (λ x → x) (CAP P) (F CSX fp)  0<PP (N∋nc 0<X CSX fp) (proper CSX fp)
     --
     -- so it has a limit as a limit of FIP
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
     --  0<X  limit is in * x or P ＼ * x
     ... | tri< 0<X ¬b ¬c with ∨L＼X {P} {* x} {UFLP.limit ( uflp  ( mf 0<X CSX fp ) (ultraf 0<X CSX fp))}
         (UFLP.P∋limit ( uflp  ( mf 0<X CSX fp ) (ultraf 0<X CSX fp)))
     ... | case1 lt = lt -- odef (* x) y
     ... | case2 nlxy = ⊥-elim (MaximumFilter.proper (maxf 0<X CSX fp) uf11 ) where
        --
        -- if (* x) do not conatins a limit, P ＼ * x contains it, (P ＼ * x) is open so it is the maxf ( UFLP.is-limit )
        --    UFLP contains (* x) and P ＼ * x, it contains od∅, contradicts the proper
        --
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

--
-- Finite intersection property implies that any ultra filter have a limit, that is, neighbors of the limit is in the filter.
--
-- An ultra filter F is given. Take a closure of a filter. It is closed and it has finite intersection property, because F is porper.
-- So it has a limit as a FIP. If a neighbor p which contains the limit, p or P \ p is in the ultra filter.
-- If it is in P \ p, it cannot contains the limit, contradiction.
--
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
     CF = Replace (filter F) (λ x → Cl TP x  ) {P} record { ≤COD = λ {z} {y} lt → proj1 lt  } 
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

--    FilterQP : {P Q : HOD } → (F : Filter {Power (ZFP P Q)} {ZFP P Q} (λ x → x))  
--         → Filter {Power (ZFP Q P)} {ZFP Q P} (λ x → x) 
--    FilterQP {P} {Q} F = record { filter = ? ; f⊆L = ? ; filter1 = ? ; filter2 = ? } 
-- 
--    projection-of-filter : {P Q : HOD } → (F : Filter {Power (ZFP P Q)} {ZFP P Q} (λ x → x))  
--         → Filter {Power P} {P} (λ x → x) 
--    projection-of-filter = ?
-- 
--    projection-of-ultra-filter : {P Q : HOD } → (F : Filter {Power (ZFP P Q)} {ZFP P Q} (λ x → x))  (UF : ultra-filter F) 
--         → ultra-filter (projection-of-filter F)
--    projection-of-ultra-filter = ?

--
-- We have UFLP both in P and Q. Given an ultra filter F on P x Q. It has limits on P and Q because a projection of ultra filter
-- is a ultra filter. Show the product of the limits is a limit of P x Q. A neighbor of P x Q contains subbase of P x Q,
-- which is either inverse projection x of P or Q. The x in in projection of F, because of UFLP. So it is in F, because of the
-- property of the filter.
--
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
         FP : Filter {Power P} {P} (λ x → x)
         FP = Filter-Proj1 {P} {Q} is-apq F
         UFP : ultra-filter FP
         UFP = Filter-Proj1-UF {P} {Q} is-apq F UF
         uflp : UFLP TP FP UFP
         uflp = FIP→UFLP TP (Compact→FIP TP CP) FP UFP

         --  FPSet is in Projection ⁻¹  F
         FPSet⊆F1 : {x : Ordinal } → odef (filter FP) x →  odef (filter F) (& (ZFP (* x) Q))
         FPSet⊆F1 {x} fpx = FPSet⊆F  is-apq F fpx  

         FQ : Filter {Power Q} {Q} (λ x → x)
         FQ = Filter-Proj2 {P} {Q} is-apq F
         UFQ : ultra-filter FQ
         UFQ = Filter-Proj2-UF {P} {Q} is-apq F UF 

         --  FQSet is in Projection ⁻¹  F
         FQSet⊆F1 : {x : Ordinal } → odef (filter FQ) x →  odef (filter F) (& (ZFP P (* x) ))
         FQSet⊆F1 {x} fpx = FQSet⊆F  is-apq F fpx  

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
                 f∋b = FPSet⊆F1 (subst (λ k → odef (filter FP) k ) &iso fp∋b )
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
                 f∋b = FQSet⊆F1 (subst (λ k → odef (filter FQ) k ) &iso fp∋b )
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






