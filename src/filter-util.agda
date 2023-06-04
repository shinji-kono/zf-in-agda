{-# OPTIONS --allow-unsolved-metas #-}
open import Level
open import Ordinals
module filter-util {n : Level } (O : Ordinals {n})   where

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
open import ZProduct O
-- open import maximum-filter O

open Filter

filter-⊆ : {P Q : HOD } → (F : Filter {Power (ZFP P Q)} {ZFP P Q} (λ x → x)) →  {x : HOD} → filter F ∋ x  →  { z : Ordinal } 
    → odef x z → odef (ZFP P Q) z
filter-⊆ {P} {Q} F {x} fx {z} xz  = f⊆L F fx _ (subst (λ k → odef k z) (sym *iso) xz )

rcp :  {P Q : HOD } → (F : Filter {Power (ZFP P Q)} {ZFP P Q} (λ x → x)) → RXCod (filter F) P (λ x fx → ZP-proj1 P Q x (filter-⊆ F fx))
rcp {P} {Q} F = record { ≤COD = λ {x} fx {z} ly → ZP1.aa ly }

Filter-Proj1 : {P Q a : HOD } → ZFP P Q ∋ a → 
     (F : Filter {Power (ZFP P Q)} {ZFP P Q} (λ x → x))  
      →    Filter {Power P} {P} (λ x → x) 
Filter-Proj1 {P} {Q} pqa F = record { filter = FP ; f⊆L = fp00 ; filter1 = f1 ; filter2 = f2 }  where
    FP : HOD
    FP = Replace' (filter F) (λ x fx → ZP-proj1 P Q x (filter-⊆ F fx)) {P} (rcp  F)
    isP→PxQ : {x : HOD} → (x⊆P : x ⊆ P ) → ZFP x Q ⊆ ZFP P Q
    isP→PxQ {x} x⊆P (ab-pair p q) = ab-pair (x⊆P p) q
    isQ→PxQ : {x : HOD} → (x⊆P : x ⊆ Q ) → ZFP P x ⊆ ZFP P Q
    isQ→PxQ {x} x⊆Q (ab-pair p q) = ab-pair p (x⊆Q q) 
    fp00 : FP ⊆ Power P 
    fp00 {x} record { z = z ; az = az ; x=ψz = x=ψz } w xw with subst (λ k → odef k w) (trans (cong (*) x=ψz) *iso ) xw
    ... | record { b = b ; aa = aa ; bb = bb ; c∋ab = c∋ab } = aa
    f0 :  {p q : HOD} → Power (ZFP P Q) ∋ q → filter F ∋ p → p ⊆ q → filter F ∋ q
    f0 {p} {q} PQq fp p⊆q = filter1 F PQq fp p⊆q 
    f1 :  {p q : HOD} → Power P ∋ q → FP ∋ p → p ⊆ q → FP ∋ q
    f1 {p} {q} Pq record { z = z ; az = az ; x=ψz = x=ψz } p⊆q = record { z = & (ZFP q Q) ; az = fp01 ty05 ty06 ; x=ψz = q=proj1 } where
       PQq : Power (ZFP P Q) ∋ ZFP q Q
       PQq z zpq = isP→PxQ {* (& q)} (Pq _) ( subst (λ k → odef k z ) (trans *iso (cong (λ k → ZFP k Q) (sym *iso))) zpq )
       q⊆P : q ⊆ P
       q⊆P {w} qw = Pq _ (subst (λ k → odef k w ) (sym *iso) qw )
       p⊆P : p ⊆ P
       p⊆P {w} pw = q⊆P (p⊆q pw)
       p=proj1 : & p ≡ & (ZP-proj1 P Q (* z) (filter-⊆ F (subst (odef (filter F)) (sym &iso) az)))
       p=proj1 = x=ψz
       p⊆ZP : (* z) ⊆ ZFP p Q
       p⊆ZP = subst (λ k → (* z) ⊆ ZFP k Q) (sym (&≡&→≡ p=proj1)) ZP-proj1⊆ZFP 
       ty05 : filter F ∋  ZFP p Q
       ty05 = filter1 F (λ z wz → isP→PxQ p⊆P (subst (λ k → odef k z) *iso wz)) (subst (λ k → odef (filter F) k) (sym &iso) az) p⊆ZP
       ty06 : ZFP p Q ⊆ ZFP q Q
       ty06 (ab-pair wp wq ) = ab-pair (p⊆q wp) wq
       fp01 : filter F ∋ ZFP p Q → ZFP p Q ⊆ ZFP q Q → filter F ∋ ZFP q Q
       fp01 fzp zp⊆zq = filter1 F PQq fzp zp⊆zq
       q=proj1 : & q ≡ & (ZP-proj1 P Q (* (& (ZFP q Q))) (filter-⊆ F (subst (odef (filter F)) (sym &iso) (fp01 ty05 ty06))))
       q=proj1 = cong (&) (ZP-proj1=rev (zp2 pqa) q⊆P *iso )
    f2 : {p q : HOD} → FP ∋ p → FP ∋ q → Power P ∋ (p ∩ q) → FP ∋ (p ∩ q)
    f2 {p} {q} record { z = zp ; az = fzp ; x=ψz = x=ψzp } record { z = zq ; az = fzq ; x=ψz = x=ψzq } Ppq 
         = record { z = _ ; az = ty50 ; x=ψz = pq=proj1 } where
       p⊆P : {zp : Ordinal} {p : HOD} (fzp : odef (filter F) zp) → ( & p ≡ &
            (ZP-proj1 P Q (* zp) (filter-⊆ F (subst (odef (filter F)) (sym &iso) fzp)))) → p ⊆ P
       p⊆P {zp} {p} fzp p=proj1 {x} px with subst (λ k → odef k x) (&≡&→≡ p=proj1) px
       ... | record { b = b ; aa = aa ; bb = bb ; c∋ab = c∋ab } = aa
       x⊆pxq : {zp : Ordinal} {p : HOD} (fzp : odef (filter F) zp) → ( & p ≡ &
            (ZP-proj1 P Q (* zp) (filter-⊆ F (subst (odef (filter F)) (sym &iso) fzp)))) → * zp ⊆ ZFP p Q
       x⊆pxq {zp} {p} fzp p=proj1 = subst (λ k → (* zp) ⊆ ZFP k Q) (sym (&≡&→≡ p=proj1)) ZP-proj1⊆ZFP
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
       pq=proj1 : & (p ∩ q) ≡ & (ZP-proj1 P Q (* (& (ZFP (p ∩ q) Q))) (filter-⊆ F (subst (odef (filter F)) (sym &iso) ty50)))
       pq=proj1 = cong (&) (ZP-proj1=rev (zp2 pqa) (λ {x} pqx → Ppq _ (subst (λ k → odef k x) (sym *iso) pqx)) *iso )

Filter-Proj1-UF : {P Q a : HOD } → (pqa : ZFP P Q ∋ a )
      → (F : Filter {Power (ZFP P Q)} {ZFP P Q} (λ x → x))  (UF : ultra-filter F)
      →  ultra-filter (Filter-Proj1 pqa F)
Filter-Proj1-UF {P} {Q} pqa F UF = record { proper = ty60 ; ultra = ty62 } where
       FP = Filter-Proj1 pqa F
       ty60 : ¬ (filter FP ∋ od∅)
       ty60 record { z = z ; az = az ; x=ψz = x=ψz } = ⊥-elim (ultra-filter.proper UF 
          (filter1 F (λ x x<0 → ⊥-elim (¬x<0 (subst (λ k → odef k x) (*iso) x<0))) (subst (λ k → odef (filter F) k ) (sym &iso) az) ty61 )) where
           ty61 : * z ⊆  od∅
           ty61 {x} lt = ⊥-elim (¬x<0 (subst (λ k → odef k x) (trans (cong (*) (ZP-proj1-0 (sym (&≡&→≡ x=ψz)))) *iso)  lt ))
       ty62 :  {p : HOD} → Power P ∋ p → Power P ∋ (P ＼ p) → (filter (Filter-Proj1 pqa F) ∋ p) ∨ (filter (Filter-Proj1 pqa F) ∋ (P ＼ p))
       ty62 {p} Pp NEGP = uf05  where
             p⊆P : p ⊆ P
             p⊆P {z} px = Pp _ (subst (λ k → odef k z) (sym *iso) px)
             mp : HOD
             mp = ZFP p Q 
             uf03 : Power (ZFP P Q) ∋  mp
             uf03 x xz with subst (λ k → odef k x ) *iso xz
             ... | ab-pair ax by = ab-pair (p⊆P ax) by
             uf04 : Power (ZFP P Q) ∋ (ZFP P Q ＼ mp)
             uf04 x xz = proj1 (subst (λ k → odef k x) *iso xz)
             uf02 : (filter F ∋ mp) ∨ (filter F ∋ (ZFP P Q ＼ mp))
             uf02 = ultra-filter.ultra UF uf03 uf04
             uf05 : (filter FP ∋ p) ∨ (filter FP ∋ (P ＼ p))
             uf05 with uf02
             ... | case1 fp  = case1 record { z = _ ; az = fp  ; x=ψz = cong (&) (ZP-proj1=rev (zp2 pqa) p⊆P *iso)  }
             ... | case2 fnp = case2 record { z = _ ; az = fnp ; x=ψz = cong (&) (ZP-proj1=rev (zp2 pqa) proj1 (trans *iso (proj1 ZFP\Q)) )  } 

rcq :  {P Q : HOD } → (F : Filter {Power (ZFP P Q)} {ZFP P Q} (λ x → x)) → RXCod (filter F) Q (λ x fx → ZP-proj2 P Q x (filter-⊆ F fx))
rcq {P} {Q} F = record { ≤COD = λ {x} fx {z} ly → ZP2.bb ly }

Filter-Proj2 : {P Q a : HOD } → ZFP P Q ∋ a → 
     (F : Filter {Power (ZFP P Q)} {ZFP P Q} (λ x → x))  
      →    Filter {Power Q} {Q} (λ x → x) 
Filter-Proj2 {P} {Q} pqa F = record { filter = FQ ; f⊆L = fp00 ; filter1 = f1 ; filter2 = f2 }  where
    FQ : HOD
    FQ = Replace' (filter F) (λ x fx → ZP-proj2 P Q x (filter-⊆ F fx)) {Q} (rcq  F)
    isP→PxQ : {x : HOD} → (x⊆P : x ⊆ P ) → ZFP x Q ⊆ ZFP P Q
    isP→PxQ {x} x⊆P (ab-pair p q) = ab-pair (x⊆P p) q
    isQ→PxQ : {x : HOD} → (x⊆P : x ⊆ Q ) → ZFP P x ⊆ ZFP P Q
    isQ→PxQ {x} x⊆Q (ab-pair p q) = ab-pair p (x⊆Q q) 
    fp00 : FQ ⊆ Power Q 
    fp00 {x} record { z = z ; az = az ; x=ψz = x=ψz } w xw with subst (λ k → odef k w) (trans (cong (*) x=ψz) *iso ) xw
    ... | record { a = a ; aa = aa ; bb = bb ; c∋ab = c∋ab } = bb
    f0 :  {p q : HOD} → Power (ZFP P Q) ∋ q → filter F ∋ p → p ⊆ q → filter F ∋ q
    f0 {p} {q} PQq fp p⊆q = filter1 F PQq fp p⊆q 
    f1 :  {p q : HOD} → Power Q ∋ q → FQ ∋ p → p ⊆ q → FQ ∋ q
    f1 {p} {q} Qq record { z = z ; az = az ; x=ψz = x=ψz } p⊆q = record { z = & (ZFP P q) ; az = fp01 ty05 ty06 ; x=ψz = q=proj2 } where
       PQq : Power (ZFP P Q) ∋ ZFP P q
       PQq z zpq = isQ→PxQ {* (& q)}  (Qq _) ( subst (λ k → odef k z ) (trans *iso (cong (λ k → ZFP P k) (sym *iso))) zpq ) 
       q⊆P : q ⊆ Q
       q⊆P {w} qw = Qq _ (subst (λ k → odef k w ) (sym *iso) qw )
       p⊆P : p ⊆ Q
       p⊆P {w} pw = q⊆P (p⊆q pw)
       p=proj2 : & p ≡ & (ZP-proj2 P Q (* z) (filter-⊆ F (subst (odef (filter F)) (sym &iso) az)))
       p=proj2 = x=ψz
       p⊆ZP : (* z) ⊆ ZFP P p
       p⊆ZP = subst (λ k → (* z) ⊆ ZFP P k ) (sym (&≡&→≡ p=proj2)) ZP-proj2⊆ZFP 
       ty05 : filter F ∋  ZFP P p
       ty05 = filter1 F (λ z wz → isQ→PxQ p⊆P (subst (λ k → odef k z) *iso wz)) (subst (λ k → odef (filter F) k) (sym &iso) az) p⊆ZP
       ty06 : ZFP P p ⊆ ZFP P q
       ty06 (ab-pair wp wq ) = ab-pair wp (p⊆q wq) 
       fp01 : filter F ∋ ZFP P p → ZFP P p ⊆ ZFP P q → filter F ∋ ZFP P q
       fp01 fzp zp⊆zq = filter1 F PQq fzp zp⊆zq
       q=proj2 : & q ≡ & (ZP-proj2 P Q (* (& (ZFP P q))) (filter-⊆ F (subst (odef (filter F)) (sym &iso) (fp01 ty05 ty06))))
       q=proj2 = cong (&) (ZP-proj2=rev (zp1 pqa) q⊆P *iso )
    f2 : {p q : HOD} → FQ ∋ p → FQ ∋ q → Power Q ∋ (p ∩ q) → FQ ∋ (p ∩ q)
    f2 {p} {q} record { z = zp ; az = fzp ; x=ψz = x=ψzp } record { z = zq ; az = fzq ; x=ψz = x=ψzq } Ppq 
         = record { z = _ ; az = ty50 ; x=ψz = pq=proj2 } where
       p⊆Q : {zp : Ordinal} {p : HOD} (fzp : odef (filter F) zp) → ( & p ≡ &
            (ZP-proj2 P Q (* zp) (filter-⊆ F (subst (odef (filter F)) (sym &iso) fzp)))) → p ⊆ Q
       p⊆Q {zp} {p} fzp p=proj2 {x} px with subst (λ k → odef k x) (&≡&→≡ p=proj2) px
       ... | record { a = a ; aa = aa ; bb = bb ; c∋ab = c∋ab } = bb
       x⊆pxq : {zp : Ordinal} {p : HOD} (fzp : odef (filter F) zp) → ( & p ≡ &
            (ZP-proj2 P Q (* zp) (filter-⊆ F (subst (odef (filter F)) (sym &iso) fzp)))) → * zp ⊆ ZFP P p 
       x⊆pxq {zp} {p} fzp p=proj2 = subst (λ k → (* zp) ⊆ ZFP P k ) (sym (&≡&→≡ p=proj2)) ZP-proj2⊆ZFP
       ty54 : Power (ZFP P Q) ∋ (ZFP P p  ∩ ZFP P q )
       ty54 z xz = subst (λ k → ZFProduct P Q k ) (zp-iso pqz) (ab-pair pqz1 pqz2 ) where
         pqz :  odef (ZFP P (p ∩ q) )  z
         pqz = subst (λ k → odef k z ) (trans *iso (sym (proj2 ZFP∩) ))  xz
         pqz1 : odef P (zπ1 pqz)
         pqz1 = zp1 pqz
         pqz2 : odef Q (zπ2 pqz)
         pqz2 = p⊆Q fzp x=ψzp (proj1 (zp2 pqz))
       ty53 : filter F ∋ ZFP P p 
       ty53 = filter1 F (λ z wz → isQ→PxQ (p⊆Q fzp x=ψzp)
         (subst (λ k → odef k z) *iso wz))
         (subst (λ k → odef (filter F) k) (sym &iso) fzp ) (x⊆pxq fzp x=ψzp)
       ty52 : filter F ∋ ZFP P q 
       ty52 = filter1 F (λ z wz → isQ→PxQ (p⊆Q fzq x=ψzq)
         (subst (λ k → odef k z) *iso wz))
         (subst (λ k → odef (filter F) k) (sym &iso) fzq ) (x⊆pxq fzq x=ψzq)
       ty51 : filter F ∋ ( ZFP P p ∩ ZFP P q  )
       ty51 = filter2 F ty53 ty52 ty54
       ty50 : filter F ∋ ZFP P (p ∩ q) 
       ty50 = subst (λ k → filter F ∋ k ) (sym (proj2 ZFP∩)) ty51
       pq=proj2 : & (p ∩ q) ≡ & (ZP-proj2 P Q (* (& (ZFP P (p ∩ q) ))) (filter-⊆ F (subst (odef (filter F)) (sym &iso) ty50)))
       pq=proj2 = cong (&) (ZP-proj2=rev (zp1 pqa) (λ {x} pqx → Ppq _ (subst (λ k → odef k x) (sym *iso) pqx)) *iso )

Filter-Proj2-UF : {P Q a : HOD } → (pqa : ZFP P Q ∋ a )
      → (F : Filter {Power (ZFP P Q)} {ZFP P Q} (λ x → x))  (UF : ultra-filter F)
      →  ultra-filter (Filter-Proj2 pqa F)
Filter-Proj2-UF {P} {Q} pqa F UF = record { proper = ty60 ; ultra = ty62 } where
       FQ = Filter-Proj2 pqa F
       ty60 : ¬ (filter FQ ∋ od∅)
       ty60 record { z = z ; az = az ; x=ψz = x=ψz } = ⊥-elim (ultra-filter.proper UF 
          (filter1 F (λ x x<0 → ⊥-elim (¬x<0 (subst (λ k → odef k x) (*iso) x<0))) (subst (λ k → odef (filter F) k ) (sym &iso) az) ty61 )) where
           ty61 : * z ⊆  od∅
           ty61 {x} lt = ⊥-elim (¬x<0 (subst (λ k → odef k x) (trans (cong (*) (ZP-proj2-0 (sym (&≡&→≡ x=ψz)))) *iso)  lt ))
       ty62 :  {p : HOD} → Power Q ∋ p → Power Q ∋ (Q ＼ p) → (filter (Filter-Proj2 pqa F) ∋ p) ∨ (filter (Filter-Proj2 pqa F) ∋ (Q ＼ p))
       ty62 {p} Qp NEGQ = uf05  where
             p⊆Q : p ⊆ Q
             p⊆Q {z} px = Qp _ (subst (λ k → odef k z) (sym *iso) px)
             mq : HOD
             mq = ZFP P p  
             uf03 : Power (ZFP P Q) ∋  mq
             uf03 x xz with subst (λ k → odef k x ) *iso xz
             ... | ab-pair ax by = ab-pair ax (p⊆Q by) 
             uf04 : Power (ZFP P Q) ∋ (ZFP P Q ＼ mq)
             uf04 x xz = proj1 (subst (λ k → odef k x) *iso xz)
             uf02 : (filter F ∋ mq) ∨ (filter F ∋ (ZFP P Q ＼ mq))
             uf02 = ultra-filter.ultra UF uf03 uf04
             uf05 : (filter FQ ∋ p) ∨ (filter FQ ∋ (Q ＼ p))
             uf05 with uf02
             ... | case1 fp  = case1 record { z = _ ; az = fp  ; x=ψz = cong (&) (ZP-proj2=rev (zp1 pqa) p⊆Q *iso)  }
             ... | case2 fnp = case2 record { z = _ ; az = fnp ; x=ψz = cong (&) (ZP-proj2=rev (zp1 pqa) proj1 (trans *iso (proj2 ZFP\Q)) )  } 

rcf :  {P Q : HOD } → (F : Filter {Power (ZFP P Q)} {ZFP P Q} (λ x → x)) → RXCod (filter F) (ZFP Q P) (λ x fx → ZPmirror P Q x (filter-⊆ F fx))
rcf {P} {Q} F = record { ≤COD = λ {x} fx {z} ly → ZPmirror⊆ZFPBA P Q x (filter-⊆ F fx) ly }

Filter-sym : {P Q : HOD } → 
     (F : Filter {Power (ZFP P Q)} {ZFP P Q} (λ x → x))  
     → Filter {Power (ZFP Q P)} {ZFP Q P} (λ x → x)
Filter-sym {P} {Q} F = 
    record { filter = fqp ; f⊆L = fqp<P ; filter1 = f1 ; filter2 = f2 }  where
    fqp : HOD
    fqp = Replace' (filter F) (λ x fx → ZPmirror P Q x (filter-⊆ F fx)) {ZFP Q P} (rcf  F)
    fqp<P : fqp ⊆ Power (ZFP Q P)
    fqp<P {z} record { z = x ; az = fx ; x=ψz = x=ψz } w xw = 
         ZPmirror⊆ZFPBA P Q (* x) (filter-⊆ F (subst (λ k → odef (filter F) k) (sym &iso) fx )) 
            (subst (λ k → odef k w) (trans (cong (*) x=ψz) *iso ) xw) 
    f1 : {p q : HOD} → Power (ZFP Q P) ∋ q → fqp ∋ p → p ⊆ q → fqp ∋ q
    f1 {p} {q} QPq fqp p⊆q = record { z = _ ; az = fis00 {ZPmirror Q P p p⊆ZQP } {ZPmirror Q P q q⊆ZQP } fig01 fig03 fis04 
      ; x=ψz = fis05 }  where
         fis00 : {p q : HOD} → Power (ZFP P Q) ∋ q → filter F ∋ p → p ⊆ q → filter F ∋ q
         fis00 = filter1 F 
         q⊆ZQP : q ⊆ ZFP Q P
         q⊆ZQP {x} qx = QPq _ (subst (λ k → odef k x) (sym *iso) qx) 
         p⊆ZQP : p ⊆ ZFP Q P
         p⊆ZQP {z} px = q⊆ZQP (p⊆q px)
         fig06 : & p ≡ & (ZPmirror P Q (* (Replaced1.z fqp)) (filter-⊆ F (subst (odef (filter F)) (sym &iso) (Replaced1.az fqp))))
         fig06 = Replaced1.x=ψz fqp
         fig03 : filter F ∋  ZPmirror Q P p p⊆ZQP
         fig03 with Replaced1.az fqp 
         ... | fz = subst (λ k → odef (filter F) k ) fig07  fz where
             fig07 :  Replaced1.z fqp ≡ & (ZPmirror Q P p (λ {x} px → QPq x (subst (λ k → def (HOD.od k) x ) (sym *iso) (p⊆q px))))
             fig07 = trans (sym &iso) ( sym (cong (&) (ZPmirror-rev (subst₂ (λ j k → j ≡ k) *iso *iso (cong (*) (sym fig06) )))))
         fig01 : Power (ZFP P Q) ∋ ZPmirror Q P q q⊆ZQP
         fig01 x xz  = ZPmirror⊆ZFPBA Q P q q⊆ZQP (subst (λ k → odef k x) *iso xz)
         fis04 : ZPmirror Q P p (λ z → q⊆ZQP (p⊆q z)) ⊆ ZPmirror Q P q q⊆ZQP
         fis04 = ZPmirror-⊆ p⊆q
         fis05 : & q ≡ & (ZPmirror P Q (* (& (ZPmirror Q P q q⊆ZQP)))
             (filter-⊆ F (subst (odef (filter F)) (sym &iso) (fis00 fig01 fig03 fis04))))
         fis05 = cong (&) (sym ( ZPmirror-rev (sym *iso) ))
    f2 : {p q : HOD} → fqp ∋ p → fqp ∋ q → Power (ZFP Q P) ∋ (p ∩ q) → fqp ∋ (p ∩ q)
    f2 {p} {q} fp fq QPpq = record { z = _ ; az = fis12 {ZPmirror Q P p p⊆ZQP} {ZPmirror Q P q q⊆ZQP} fig03 fig04 fig01
      ; x=ψz = fis05 }  where
         fis12 : {p q : HOD} → filter F ∋ p → filter F ∋ q → Power (ZFP P Q) ∋ (p ∩ q) → filter F ∋ (p ∩ q)
         fis12 {p} {q} fp fq PQpq = filter2 F fp fq PQpq
         p⊆ZQP : p ⊆ ZFP Q P
         p⊆ZQP {z} px = fqp<P fp _ (subst (λ k → odef k z) (sym *iso) px)
         q⊆ZQP : q ⊆ ZFP Q P
         q⊆ZQP {z} qx = fqp<P fq _ (subst (λ k → odef k z) (sym *iso) qx)
         pq⊆ZQP : (p ∩ q) ⊆ ZFP Q P
         pq⊆ZQP {z} pqx = QPpq _ (subst (λ k → odef k z) (sym *iso) pqx)
         fig06 : & p ≡ & (ZPmirror P Q (* (Replaced1.z fp)) (filter-⊆ F (subst (odef (filter F)) (sym &iso) (Replaced1.az fp))))
         fig06 = Replaced1.x=ψz fp
         fig09 : & q ≡ & (ZPmirror P Q (* (Replaced1.z fq)) (filter-⊆ F (subst (odef (filter F)) (sym &iso) (Replaced1.az fq))))
         fig09 = Replaced1.x=ψz fq
         fig03 : filter F ∋  ZPmirror Q P p p⊆ZQP
         fig03 = subst (λ k → odef (filter F) k ) fig07 ( Replaced1.az fp )  where
             fig07 :  Replaced1.z fp ≡ & (ZPmirror Q P p p⊆ZQP )
             fig07 = trans (sym &iso) ( sym (cong (&) (ZPmirror-rev (subst₂ (λ j k → j ≡ k) *iso *iso (cong (*) (sym fig06) )))))
         fig04 : filter F ∋  ZPmirror Q P q q⊆ZQP
         fig04 = subst (λ k → odef (filter F) k ) fig08 ( Replaced1.az fq )  where
             fig08 :  Replaced1.z fq ≡ & (ZPmirror Q P q q⊆ZQP )
             fig08 = trans (sym &iso) ( sym (cong (&) (ZPmirror-rev (subst₂ (λ j k → j ≡ k) *iso *iso (cong (*) (sym fig09) )))))
         fig01 : Power (ZFP P Q) ∋ ( ZPmirror Q P p p⊆ZQP ∩ ZPmirror Q P q q⊆ZQP )
         fig01 x xz  = ZPmirror⊆ZFPBA Q P q q⊆ZQP (proj2 (subst (λ k → odef k x) *iso xz))
         fis05 : & (p ∩ q) ≡ & (ZPmirror P Q (* (& (ZPmirror Q P p p⊆ZQP ∩ ZPmirror Q P q q⊆ZQP))) 
             (filter-⊆ F (subst (odef (filter F)) (sym &iso) (fis12 fig03 fig04 fig01) )))
         fis05 = cong (&) (sym ( ZPmirror-rev {Q} {P} {_} {_} {pq⊆ZQP} (trans ZPmirror-∩ (sym *iso) ) ))

Filter-sym-UF : {P Q : HOD } → 
     (F : Filter {Power (ZFP P Q)} {ZFP P Q} (λ x → x))  (UF : ultra-filter F)
     → ultra-filter (Filter-sym F)
Filter-sym-UF {P} {Q} F UF = record { proper = uf00 ; ultra = uf01 } where
     FQP = Filter-sym F
     uf00 : ¬ (Replace' (filter F) (λ x fx → ZPmirror P Q x (filter-⊆ F fx)) {ZFP Q P} (rcf  F) ∋ od∅)
     uf00 record { z = z ; az = az ; x=ψz = x=ψz } = ⊥-elim ( ultra-filter.proper UF (subst (λ k → odef (filter F) k) uf10 az )) where
         uf10 : z ≡ & od∅
         uf10 = ZPmirror-0 (sym (&≡&→≡ x=ψz))
     uf01 : {p : HOD} → Power (ZFP Q P) ∋ p → Power (ZFP Q P) ∋ (ZFP Q P ＼ p) →
            (filter FQP ∋ p) ∨ (filter FQP ∋ (ZFP Q P ＼ p))
     uf01 {p} QPp NEGP = uf05  where
         p⊆ZQP : p ⊆ ZFP Q P
         p⊆ZQP {z} px = QPp _ (subst (λ k → odef k z) (sym *iso) px)
         mp : HOD
         mp = ZPmirror Q P p p⊆ZQP
         uf03 : Power (ZFP P Q) ∋  mp
         uf03 x xz = ZPmirror⊆ZFPBA Q P p p⊆ZQP (subst (λ k → odef k x) *iso xz)
         uf04 : Power (ZFP P Q) ∋ (ZFP P Q ＼ mp)
         uf04 x xz = proj1 (subst (λ k → odef k x) *iso xz)
         uf02 : (filter F ∋ mp) ∨ (filter F ∋ (ZFP P Q ＼ mp))
         uf02 = ultra-filter.ultra UF uf03 uf04
         uf05 : (filter FQP ∋ p) ∨ (filter FQP ∋ (ZFP Q P ＼ p))
         uf05 with uf02
         ... | case1 fp  = case1 record { z = _ ; az = fp   ; x=ψz = cong (&) (sym ( ZPmirror-rev (sym *iso) )) }
         ... | case2 fnp = case2 record { z = _ ; az = uf06 ; x=ψz = cong (&) (sym ( ZPmirror-rev (sym *iso) )) } where
               uf06 : odef (filter F) (& (ZPmirror Q P (ZFP Q P ＼ p) proj1 ))
               uf06 = subst (λ k → odef (filter F)  k) (cong (&) (sym (trans ZPmirror-neg 
                  (cong (λ k → k ＼ (ZPmirror Q P p (λ {z} px → QPp z (subst (λ k → OD.def (HOD.od k) z) (sym *iso) px)))) ZPmirror-whole) ))) fnp

-- this makes check very slow
-- Filter-Proj2 : {P Q a : HOD } → ZFP P Q ∋ a → 
--      (F : Filter {Power (ZFP P Q)} {ZFP P Q} (λ x → x))  
--       →    Filter {Power Q} {Q} (λ x → x) 
-- Filter-Proj2 {P} {Q} {a} pqa F = Filter-Proj1 {Q} {P} qpa (Filter-sym F ) where
--      qpa : ZFP Q P ∋ < * (zπ2 pqa) , * (zπ1 pqa) >
--      qpa = ab-pair (zp2 pqa) (zp1 pqa)

-- Filter-Proj2-UF : {P Q a : HOD } → (pqa : ZFP P Q ∋ a )
--       → (F : Filter {Power (ZFP P Q)} {ZFP P Q} (λ x → x))  (UF : ultra-filter F)
--       →  ultra-filter (Filter-Proj2 pqa F)
-- Filter-Proj2-UF {P} {Q} {a} pqa F UF = Filter-Proj1-UF {Q} {P} qpa (Filter-sym F) (Filter-sym-UF F UF) where 
--      qpa : ZFP Q P ∋ < * (zπ2 pqa) , * (zπ1 pqa) >
--      qpa = ab-pair (zp2 pqa) (zp1 pqa)

FPSet⊆F : {P Q a : HOD } → (pqa : ZFP P Q ∋ a ) → 
     (F : Filter {Power (ZFP P Q)} {ZFP P Q} (λ x → x))  
      →   {x : Ordinal } → odef (filter (Filter-Proj1 {P} {Q} pqa F )) x →  odef (filter F) (& (ZFP (* x) Q))
FPSet⊆F {P} {Q} {a} pqa F {x} record { z = z ; az = az ; x=ψz = x=ψz } = filter1 F uf09 (subst (λ k → odef (filter F) k) (sym &iso) az) uf08 where
      uf08 : * z ⊆ ZFP (* x) Q
      uf08 = subst (λ k  → * z ⊆ ZFP k Q) (trans (sym *iso) (cong (*) (sym x=ψz))) ZP-proj1⊆ZFP 
      uf09 : Power (ZFP P Q) ∋ ZFP (* x) Q
      uf09 z xqz with subst (λ k → odef k z) *iso xqz
      ... | ab-pair {c} {d} xc by = ab-pair uf10  by where
          uf10 : odef P c
          uf10 with subst (λ k → odef k c) (sym (trans (sym *iso) (cong (*) (sym x=ψz)))) xc
          ... | record { b = b ; aa = aa ; bb = bb ; c∋ab = c∋ab } = aa

FQSet⊆F : {P Q a : HOD } → (pqa : ZFP P Q ∋ a ) → 
     (F : Filter {Power (ZFP P Q)} {ZFP P Q} (λ x → x))  
      →   {x : Ordinal } → odef (filter (Filter-Proj2 {P} {Q} pqa F )) x →  odef (filter F) (& (ZFP P (* x) ))
FQSet⊆F {P} {Q} {a} pqa F {x} record { z = z ; az = az ; x=ψz = x=ψz } = filter1 F uf09 (subst (λ k → odef (filter F) k) (sym &iso) az ) uf08 where
      uf08 : * z ⊆ ZFP P (* x) 
      uf08 = subst (λ k  → * z ⊆ ZFP P k ) (trans (sym *iso) (cong (*) (sym x=ψz))) ZP-proj2⊆ZFP 
      uf09 : Power (ZFP P Q) ∋ ZFP P (* x) 
      uf09 z xpz with subst (λ k → odef k z) *iso xpz
      ... | ab-pair {c} {d} ax yc = ab-pair ax uf10 where
          uf10 : odef Q d
          uf10 with subst (λ k → odef k d) (sym (trans (sym *iso) (cong (*) (sym x=ψz)))) yc 
          ... | record { a = a ; aa = aa ; bb = bb ; c∋ab = c∋ab } = bb 


-- FQSet⊆F : {P Q a : HOD } → (pqa : ZFP P Q ∋ a ) → 
--     (F : Filter {Power (ZFP P Q)} {ZFP P Q} (λ x → x))  
--      →   {x : Ordinal } → odef (filter (Filter-Proj2 {P} {Q} pqa F )) x →  odef (filter F) (& (ZFP P (* x) ))
--FQSet⊆F {P} {Q} {a} pqa F {x} f2x = FPSet⊆F {P} {Q} {a} qpa (Filter-sym F) {x} ?  where
--     qpa : ZFP Q P ∋ < * (zπ2 pqa) , * (zπ1 pqa) >
--     qpa = ab-pair (zp2 pqa) (zp1 pqa)










