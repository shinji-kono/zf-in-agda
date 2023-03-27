{-# OPTIONS --allow-unsolved-metas #-}
import Level
open import Ordinals
module generic-filter {n : Level.Level } (O : Ordinals {n})   where

-- import filter
open import zf
open import logic
-- open import partfunc {n} O
import OD

open import Relation.Nullary
open import Relation.Binary
open import Data.Empty
open import Relation.Binary
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality
open import Data.Nat
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

-- open filter O

open _∧_
open _∨_
open Bool


open HOD

-------
--    the set of finite partial functions from ω to 2
--
--

open import Data.List hiding (filter)
open import Data.Maybe

open import ZProduct O

record CountableModel : Set (Level.suc (Level.suc n)) where
   field
       ctl-M : HOD
       ctl→ : ℕ → Ordinal
       ctl<M : (x : ℕ) → odef (ctl-M) (ctl→ x)
       ctl← : (x : Ordinal )→  odef (ctl-M ) x → ℕ
       ctl-iso→ : { x : Ordinal } → (lt : odef (ctl-M) x )  → ctl→ (ctl← x lt ) ≡ x
       TC : {x y : Ordinal} → odef ctl-M x → odef (* x) y → odef ctl-M y
       is-model : (x : HOD) → & x o< & ctl-M → ctl-M ∋ (x ∩ ctl-M)
       -- we have no otherway round
       -- ctl-iso← : { x : ℕ }  →  ctl← (ctl→ x ) (ctl<M x)  ≡ x
--
-- almmost universe
-- find-p contains ∃ x : Ordinal → x o< & M → ∀ r ∈ M → ∈ Ord x
--

-- we expect  P ∈ * ctl-M ∧ G  ⊆ L ⊆ Power P  , ¬ G ∈ * ctl-M,

open CountableModel

----
--   a(n) ∈ M
--   ∃ q ∈ L ⊆ Power P → q ∈ a(n) ∧ p(n) ⊆ q
--
PGHOD :  (i : ℕ) (L : HOD) (C : CountableModel ) → (p : Ordinal) → HOD
PGHOD i L C p = record { od = record { def = λ x  →
       odef L x ∧ odef (* (ctl→ C i)) x  ∧  ( (y : Ordinal ) → odef (* p) y →  odef (* x) y ) }
   ; odmax = odmax L  ; <odmax = λ {y} lt → <odmax L (proj1 lt) }

---
--   p(n+1) = if ({q | q ∈ a(n) ∧ p(n) ⊆ q)} != ∅ then q otherwise p(n)
--
find-p :  (L : HOD ) (C : CountableModel )  (i : ℕ) → (x : Ordinal) → Ordinal
find-p L C zero x = x
find-p L C (suc i) x with is-o∅ ( & ( PGHOD i L C (find-p L C i x)) )
... | yes y  = find-p L C i x
... | no not  = & (ODC.minimal O ( PGHOD i L C (find-p L C i x)) (λ eq → not (=od∅→≡o∅ eq)))  -- axiom of choice

---
-- G = { r ∈ L ⊆ Power P | ∃ n → r ⊆ p(n) }
--
record PDN  (L p : HOD ) (C : CountableModel )  (x : Ordinal) : Set n where
   field
       gr : ℕ
       pn<gr : (y : Ordinal) → odef (* x) y → odef (* (find-p L C gr (& p))) y
       x∈PP  : odef L x

open PDN

---
-- G as a HOD
--
PDHOD :  (L p : HOD ) (C : CountableModel  ) → HOD
PDHOD L p C  = record { od = record { def = λ x →  PDN L p C x }
    ; odmax = odmax L ; <odmax = λ {y} lt → <odmax L {y} (PDN.x∈PP lt)  }

open PDN

P∅ : {P : HOD} → odef (Power P) o∅
P∅ {P} =  subst (λ k → odef (Power P) k ) ord-od∅ (lemma o∅  o∅≡od∅) where
    lemma : (x : Ordinal ) → * x ≡ od∅ → odef (Power P) (& od∅)
    lemma x eq = power← P od∅  (λ {x} lt → ⊥-elim (¬x<0 lt ))
x<y→∋ : {x y : Ordinal} → odef (* x) y → * x ∋ * y
x<y→∋ {x} {y} lt = subst (λ k → odef (* x) k ) (sym &iso) lt

gf05 : {a b : HOD} {x : Ordinal } → (odef (a ∪ b) x ) → ¬ odef a x → ¬ odef b x → ⊥
gf05 {a} {b} {x} (case1 ax) nax nbx = nax ax
gf05 {a} {b} {x} (case2 bx) nax nbx = nbx bx

open import Data.Nat.Properties
open import nat hiding ( exp )

p-monotonic1 :  (L p : HOD ) (C : CountableModel  ) → {n : ℕ} → (* (find-p L C n (& p))) ⊆ (* (find-p L C (suc n) (& p)))
p-monotonic1 L p C {n} {x} with is-o∅ (& (PGHOD n L C (find-p L C n (& p))))
... | yes y =  refl-⊆ {* (find-p L C n (& p))}
... | no not = λ  lt →   proj2 (proj2 fmin∈PGHOD) _ lt   where
    fmin : HOD
    fmin = ODC.minimal O (PGHOD n L C (find-p L C n (& p))) (λ eq → not (=od∅→≡o∅ eq))
    fmin∈PGHOD : PGHOD n L C (find-p L C n (& p)) ∋ fmin
    fmin∈PGHOD = ODC.x∋minimal O (PGHOD n L C (find-p L C n (& p))) (λ eq → not (=od∅→≡o∅ eq))

p-monotonic :  (L p : HOD ) (C : CountableModel  ) → {n m : ℕ} → n ≤ m → (* (find-p L C n (& p))) ⊆ (* (find-p L C m (& p)))
p-monotonic L p C {zero} {zero} n≤m = refl-⊆ {* (find-p L C zero (& p))}
p-monotonic L p C {zero} {suc m} z≤n lt = p-monotonic1 L p C {m} (p-monotonic L p C {zero} {m} z≤n lt )
p-monotonic L p C {suc n} {suc m} (s≤s n≤m) with <-cmp n m
... | tri< a ¬b ¬c = λ lt → p-monotonic1 L p C {m} (p-monotonic L p C {suc n} {m} a lt)
... | tri≈ ¬a refl ¬c = λ x → x
... | tri> ¬a ¬b c = ⊥-elim ( nat-≤> n≤m c )

record Expansion  (p : HOD) (dense : HOD)  : Set (Level.suc n) where
   field
       exp : HOD
       D∋exp : dense ∋ exp
       p⊆exp : p ⊆ exp

record Dense  (L : HOD ) : Set (Level.suc n) where
   field
       dense : HOD
       d⊆P :  dense ⊆ L
       has-exp : {p : HOD} → (Lp : L ∋ p) → Expansion p dense

record Exp2 (I : HOD)  ( p q : HOD ) : Set (Level.suc n) where
   field
       exp : HOD
       I∋exp : I ∋ exp
       p⊆exp : p ⊆ exp
       q⊆exp : q ⊆ exp

record ⊆-Ideal {L P : HOD } (LP : L ⊆ Power P) : Set (Level.suc n) where
   field
       ideal : HOD
       i⊆L :  ideal ⊆ L
       ideal1 : { p q : HOD } →  L ∋ q  → ideal ∋ p →  q ⊆ p  → ideal ∋ q
       exp : { p q : HOD } → ideal ∋ p → ideal ∋ q → Exp2 ideal p q

record GenericFilter {L P : HOD} (LP : L ⊆ Power P) (M : HOD) : Set (Level.suc n) where
    field
       genf : ⊆-Ideal {L} {P} LP
       generic : (D : Dense L ) → M ∋ Dense.dense D → ¬ ( (Dense.dense D ∩ ⊆-Ideal.ideal genf ) ≡ od∅ )

----
--  Generic Filter on L ⊆ Power P from HOD's Countable Ordinal (G ⊆ Power P ≡ G i.e. ℕ → P → Set )
--
--  p 0 ≡ p0
--  p (suc n) = if ∃ q ∈ M ∧ p n ⊆ q → q  (by axiom of choice) ( q =  * ( ctl→ n ) )
---             else p n

P-GenericFilter : (P L p0 : HOD ) → (LP : L ⊆ Power P) → L ∋ p0
      → (C : CountableModel ) → GenericFilter {L} {P} LP ( ctl-M C )
P-GenericFilter P L p0 L⊆PP Lp0 C = record {
      genf = record { ideal = PDHOD L p0 C ; i⊆L = x∈PP ; ideal1 = ideal1 ; exp = λ ip iq → exp1 ip iq }
    ; generic = fdense
   } where
       ideal1 : {p q : HOD} → L ∋ q → PDHOD L p0 C ∋ p → q ⊆ p → PDHOD L p0 C ∋ q
       ideal1 {p} {q} Lq record { gr = gr ; pn<gr = pn<gr ; x∈PP = x∈PP } q⊆p =
                 record { gr = gr ; pn<gr = λ y qy → pn<gr y (gf00 qy) ; x∈PP = Lq }  where
            gf00 : {y : Ordinal } →  odef (* (& q)) y → odef (* (& p)) y
            gf00 {y} qy = subst (λ k → odef k y ) (sym *iso) (q⊆p (subst (λ k → odef k y) *iso qy ))
       Lan : (i : ℕ ) →  odef L (find-p L C i (& p0))
       Lan zero = Lp0
       Lan (suc i) with is-o∅ ( & ( PGHOD i L C (find-p L C i (& p0))) )
       ... | yes y  = Lan i
       ... | no not  = proj1 ( ODC.x∋minimal O ( PGHOD i L C (find-p L C i (& p0))) (λ eq → not (=od∅→≡o∅ eq)))
       exp1 : {p q : HOD} → (ip : PDHOD L p0 C ∋ p) → (ip : PDHOD L p0 C ∋ q) → Exp2 (PDHOD L p0 C) p q
       exp1 {p} {q} record { gr = pgr ; pn<gr = ppn ; x∈PP = PPp }
                      record { gr = qgr ; pn<gr = qpn ; x∈PP = PPq } = gf01 where
            Pp = record { gr = pgr ; pn<gr = ppn ; x∈PP = PPp }
            Pq = record { gr = qgr ; pn<gr = qpn ; x∈PP = PPq }
            gf17 : {q : HOD} → (Pq : PDHOD L p0 C ∋ q ) → PDHOD L p0 C ∋ * (find-p L C (gr Pq) (& p0))
            gf17 {q} Pq = record { gr = PDN.gr Pq  ; pn<gr = λ y qq → subst (λ k → odef (* k) y) &iso qq
                 ; x∈PP = subst (λ k → odef L k ) (sym &iso) (Lan (PDN.gr Pq))  }
            gf01 : Exp2 (PDHOD L p0 C) p q
            gf01 with <-cmp pgr qgr
            ... | tri< a ¬b ¬c = record { exp = * (find-p L C (gr Pq) (& p0))  ; I∋exp = gf17 Pq ; p⊆exp = λ px → gf15 _ px
                    ; q⊆exp = λ {x} qx → qpn _ (subst (λ k → odef k x) (sym *iso) qx)  } where
                 gf16 : gr Pp ≤ gr Pq
                 gf16 = <to≤ a
                 gf15 :  (y : Ordinal) → odef p y → odef (* (find-p L C (gr Pq) (& p0))) y
                 gf15 y xpy = p-monotonic L p0 C gf16 (PDN.pn<gr Pp y (subst (λ k → odef k y) (sym *iso) xpy) )
            ... | tri≈ ¬a refl ¬c = record { exp = * (find-p L C (gr Pq) (& p0))  ; I∋exp = gf17 Pq
                    ; p⊆exp = λ {x} px → ppn _ (subst (λ k → odef k x) (sym *iso) px)
                    ; q⊆exp = λ {x} qx → qpn _ (subst (λ k → odef k x) (sym *iso) qx)  }
            ... | tri> ¬a ¬b c = record { exp = * (find-p L C (gr Pp) (& p0))  ; I∋exp = gf17 Pp ; q⊆exp = λ qx → gf15 _ qx
                    ; p⊆exp = λ {x} px → ppn _ (subst (λ k → odef k x) (sym *iso) px)  } where
                 gf16 : gr Pq ≤ gr Pp
                 gf16 = <to≤ c
                 gf15 :  (y : Ordinal) → odef q y → odef (* (find-p L C (gr Pp) (& p0))) y
                 gf15 y xqy = p-monotonic L p0 C gf16 (PDN.pn<gr Pq y (subst (λ k → odef k y) (sym *iso) xqy) )
       fdense : (D : Dense L ) → (ctl-M C ) ∋ Dense.dense D  → ¬ (Dense.dense D ∩ (PDHOD L p0 C)) ≡ od∅
       fdense D MD eq0  = ⊥-elim (  ∅< {Dense.dense D ∩ PDHOD L p0 C} fd01 (≡od∅→=od∅ eq0 )) where
           open Dense
           open Expansion
           an : ℕ
           an = ctl← C (& (dense D)) MD
           pn : Ordinal
           pn = find-p L C an (& p0)
           pn+1 : Ordinal
           pn+1 = find-p L C (suc an) (& p0)
           d=an : dense D ≡ * (ctl→ C an)
           d=an = begin dense D ≡⟨ sym *iso ⟩
                    * ( & (dense D)) ≡⟨ cong (*) (sym (ctl-iso→  C MD )) ⟩
                    * (ctl→ C an) ∎  where open ≡-Reasoning
           fd07 : odef (dense D) pn+1
           fd07 with is-o∅ ( & ( PGHOD an L C (find-p L C an (& p0))) )
           ... | yes y = ⊥-elim ( ¬x<0 ( _==_.eq→ fd10 fd21 ) ) where
              L∋pn : L ∋ * (find-p L C an (& p0))
              L∋pn = subst (λ k → odef L k) (sym &iso) (Lan an )
              ex = has-exp D L∋pn
              L∋df : L ∋ ( exp ex )
              L∋df = (d⊆P D) (D∋exp ex)
              pn∋df : (* (ctl→ C an)) ∋ ( exp ex)
              pn∋df = subst (λ k → odef k (& ( exp ex))) d=an (D∋exp ex )
              pn⊆df : (y : Ordinal) → odef (* (find-p L C an (& p0))) y → odef (* (& (exp ex))) y
              pn⊆df y py = subst (λ k → odef k y ) (sym *iso) (p⊆exp ex py)
              fd21 : odef (PGHOD an L C (find-p L C an (& p0)) ) (& (exp ex))
              fd21 = ⟪ L∋df , ⟪ pn∋df , pn⊆df ⟫ ⟫
              fd10 :  PGHOD an L C (find-p L C an (& p0)) =h= od∅
              fd10 = ≡o∅→=od∅ y
           ... | no not = fd27 where
              fd29 =  ODC.minimal O ( PGHOD an L C (find-p L C an (& p0))) (λ eq → not (=od∅→≡o∅ eq))
              fd28 : PGHOD an L C (find-p L C an (& p0)) ∋ fd29
              fd28 = ODC.x∋minimal O (PGHOD an L C (find-p L C an (& p0))) (λ eq → not (=od∅→≡o∅ eq))
              fd27 :  odef (dense D) (& fd29)
              fd27 = subst (λ k → odef k (& fd29)) (sym d=an) (proj1 (proj2 fd28))
           fd03 : odef (PDHOD L p0 C) pn+1
           fd03 = record { gr = suc an ; pn<gr = λ y lt → lt ; x∈PP = Lan (suc an)}
           fd01 : (dense D ∩ PDHOD L p0 C) ∋ (* pn+1)
           fd01 = ⟪ subst (λ k → odef (dense D)  k ) (sym &iso) fd07 , subst (λ k → odef  (PDHOD L p0 C) k) (sym &iso) fd03 ⟫

open GenericFilter
-- open Filter

record Incompatible  (L p : HOD ) (L∋a : L ∋ p ) : Set (Level.suc (Level.suc n)) where
   field
      q r : HOD
      Lq : L ∋ q
      Lr : L ∋ r
      p⊆q : p ⊆ q
      p⊆r : p ⊆ r
      ¬compat : (s : HOD) → L ∋ s → ¬ ( (q ⊆ s) ∧ (r ⊆ s) )

Incompatible→¬M∋G : (P L p0 : HOD ) → (LPP : L ⊆ Power P) → (Lp0 : L ∋ p0 )
      → (C : CountableModel )
      → ctl-M C ∋ L
      → ( {p : HOD} → (Lp : L ∋ p ) → Incompatible L p Lp )
      →  ¬ ( ctl-M C ∋  ⊆-Ideal.ideal (genf ( P-GenericFilter P L p0 LPP Lp0 C )))
Incompatible→¬M∋G P L p0 LPP Lp0 C ML NC MF = ¬G∩D=0 D∩G=0 where
    PG = P-GenericFilter P L p0 LPP Lp0 C
    GF =  genf PG
    G =  ⊆-Ideal.ideal (genf PG)
    M = ctl-M C
    D : HOD
    D = L ＼ G
    D<M : & D o< & (ctl-M C)
    D<M = ordtrans≤-<  (⊆→o≤ proj1 ) (odef< ML)
    M∋DM : M ∋ (D ∩ M )
    M∋DM = is-model C D D<M
    -- G⊆M : G ⊆ M
    -- G⊆M {x} rx = TC C ML (subst (λ k → odef k x) (sym *iso) (⊆-Ideal.i⊆L GF rx))
    -- D⊆M : D ⊆ M
    -- D⊆M {x} dx = TC C ML (subst (λ k → odef k x) (sym *iso) (proj1 dx))
    D=D∩M : D ≡ D ∩ M
    D=D∩M = ==→o≡ record { eq→ = ddm00 ; eq← = proj1 } where
        ddm00 : {x : Ordinal} → odef D x → odef (D ∩ M) x
        ddm00 {x} ⟪ Lx , ¬Gx ⟫ = ⟪ ⟪ Lx , ¬Gx  ⟫  , TC C ML (subst (λ k → odef k x) (sym *iso) Lx ) ⟫
    M∋D : M ∋ D
    M∋D = subst (λ k → M ∋ k ) (sym D=D∩M) M∋DM
    D⊆PP : D ⊆ Power P
    D⊆PP {x} ⟪ Lx , ngx ⟫  = LPP Lx
    DD : Dense L
    DD = record { dense = D ; d⊆P = proj1 ; has-exp = exp } where
        exp : {p : HOD} → (Lp : L ∋ p) → Expansion p D
        exp {p} Lp = exp1 where
            q : HOD
            q = Incompatible.q (NC Lp)
            r : HOD
            r = Incompatible.r (NC Lp)
            Lq : L ∋ q
            Lq = Incompatible.Lq (NC Lp)
            Lr : L ∋ r
            Lr = Incompatible.Lr (NC Lp)
            exp1 : Expansion p D
            exp1  with ODC.p∨¬p O (G ∋ q)
            ... | case2 ngq = record { exp = q  ; D∋exp = ⟪ Lq , ngq ⟫ ; p⊆exp = Incompatible.p⊆q (NC Lp)}
            ... | case1 gq with ODC.p∨¬p O (G ∋ r)
            ... | case2 ngr = record { exp = r  ; D∋exp = ⟪ Lr , ngr ⟫ ; p⊆exp = Incompatible.p⊆r (NC Lp)}
            ... | case1 gr = ⊥-elim ( Incompatible.¬compat (NC Lp) ex2 Le ⟪  q⊆ex2 , r⊆ex2 ⟫ ) where
                ex2 = Exp2.exp (⊆-Ideal.exp GF gq gr)
                Le =  ⊆-Ideal.i⊆L GF (Exp2.I∋exp (⊆-Ideal.exp GF gq gr))
                q⊆ex2 = Exp2.p⊆exp (⊆-Ideal.exp GF gq gr)
                r⊆ex2 = Exp2.q⊆exp (⊆-Ideal.exp GF gq gr)
    ¬G∩D=0 : ¬ ( (D ∩ G ) =h= od∅ )
    ¬G∩D=0 eq =  generic PG DD M∋D (==→o≡ eq)
    D∩G=0 : (D ∩ G ) =h= od∅  -- because D = L ＼ G
    D∩G=0 = record { eq→ = λ {x} G∩D → ⊥-elim( proj2 (proj1 G∩D) (proj2 G∩D))
        ; eq← = λ lt → ⊥-elim (¬x<0 lt) } 

--
-- P-Generic Filter defines a countable model D ⊂ C from P
--

--
-- val x G = { val y G | ∃ p → G ∋ p → x ∋ < y , p > }
--
--  We can define the valuation, but to use this, we need V=L, which makes things complicated.

val< : {x y p : Ordinal} → odef (* x) ( & < * y , * p >  ) → y o< x
val< {x} {y} {p} xyp = osucprev ( begin
    osuc y ≤⟨ osucc (odef< (subst (λ k → odef (* y , * y)  k) &iso (v00 _  _ ) )) ⟩
    & (* y , * y) <⟨ c<→o< (v01 _ _)  ⟩
    & < * y , * p > <⟨ odef< xyp ⟩
    & (* x) ≡⟨ &iso ⟩
    x ∎ ) where
       v00 : (x y : HOD) → odef (x , y) (& x)
       v00 _ _ = case1 refl
       v01 : (x y : HOD) → < x , y > ∋ (x , x)
       v01 _ _ = case1 refl
       open o≤-Reasoning O

record valS (G : HOD) (x z : Ordinal) (val : (y : Ordinal) → y o< x → HOD): Set n where
   field
     y p : Ordinal
     G∋p : odef G p
     is-val : odef (* x) ( & < * y , * p >  )
     z=valy : z ≡ & (val y (val< is-val))
     z<x : z o< x

val : (x : HOD) →  (G : HOD) →  HOD
val x G = TransFinite {λ x → HOD } ind (& x) where
  ind : (x : Ordinal) → (valy : (y : Ordinal) → y o< x → HOD) → HOD
  ind x valy = record { od = record { def = λ z → valS G x z  valy  } ; odmax = x ; <odmax = v02 } where
       v02 : {z : Ordinal} → valS G x z valy → z o< x
       v02 {z} lt = valS.z<x lt

--
-- What we nedd
--   M[G] : HOD
--     M ⊆ M[G]
--     M[G] ∋ G
--     M[G] ∋ ∪G
--
--     assume countable L as M
--     L is a countable subset of Power ω i.e. Power ω ∩ M
--     it defines countable Ordinal
--
--  Generic Filter is a countable sequence of element of M
--    Mg is set of all elementns of M which contains an element of G
--
--  Mg : HOD
--  Mg 

record Mg {L P : HOD} (LP : L ⊆ Power P) (M : HOD) (G : GenericFilter {L} {P} LP M) (x : Ordinal) : Set n where
    field
       gi : Ordinal
       G∋gi : odef (⊆-Ideal.ideal (genf G)) gi
       x∋gi : odef (* x) gi

MgH : {L P : HOD} (LP : L ⊆ Power P) (M : HOD) (G : GenericFilter {L} {P} LP M) → HOD
MgH {L} {P} LP M G = record { od = record { def = λ x → odef M x ∧ Mg LP M G x } ; odmax = & M ; <odmax = odef∧<  }

MG1 : {L P : HOD} (LP : L ⊆ Power P) (M : HOD) (G : GenericFilter {L} {P} LP M) → HOD
MG1 {L} {P} LP M G = M ∪ Union (MgH LP M G)

TCS : (G : HOD) → Set (Level.suc n)
TCS G = {x y : HOD} → G ∋ x → x ∋ y → G ∋ y

GH : (P L p0 : HOD ) → (LPP : L ⊆ Power P) → (Lp0 : L ∋ p0 )
      → (C : CountableModel ) → HOD
GH P L p0 LPP Lp0 C = ⊆-Ideal.ideal (genf ( P-GenericFilter P L p0 LPP Lp0 C ))

module _ {L P : HOD} (LP : L ⊆ Power P) (M : HOD) (GF : GenericFilter {L} {P} LP M) where

    MG = MG1 {L} {P} LP M GF 
    G = ⊆-Ideal.ideal (genf GF)

    M⊆MG : M ⊆ MG 
    M⊆MG = case1

    MG∋G : MG ∋ G
    MG∋G = ?

    MG∋UG : MG ∋ Union G
    MG∋UG = ?


