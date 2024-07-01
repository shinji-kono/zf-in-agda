{-# OPTIONS --cubical-compatible --safe #-}
open import Level renaming (zero to Zero ; suc to Suc)
open import Ordinals
open import logic
open import Relation.Nullary

open import Ordinals
import HODBase
import OD
open import Relation.Nullary
open import Relation.Binary
open import  Relation.Binary.PropositionalEquality hiding ( [_] )

module maximum-filter {n : Level } (O : Ordinals {n} ) (HODAxiom : HODBase.ODAxiom O)  (ho< : OD.ODAxiom-ho< O HODAxiom )
       (AC : OD.AxiomOfChoice O HODAxiom ) where

-- open import  Relation.Binary.Structures
open import Data.Empty
open import Data.Nat hiding ( _≤_  ; _<_ )

import OrdUtil
open inOrdinal O

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

open import filter O HODAxiom ho< AC
open import ZProduct O HODAxiom ho<

open Filter

PO : IsStrictPartialOrder _≡_ _⊂_ 
PO = record { isEquivalence = record { refl = refl ; sym = sym ; trans = trans }
   ; trans = λ {a} {b} {c} → trans-⊂ {a} {b} {c}
   ; irrefl = λ x=y x<y → o<¬≡ (cong (&) x=y) (proj1 x<y)
   ; <-resp-≈ =  record { fst = ( λ {x} {y} {y1} y=y1 xy1 → subst (λ k → x ⊂ k) y=y1 xy1  )
                        ; snd = (λ {x} {x1} {y} x=x1 x1y → subst (λ k → k ⊂ x) x=x1 x1y ) } }

⊂-cong : {x y w z : HOD} → (O HODBase.== od x) (od w) → (O HODBase.== od y) (od z) → x ⊂ y → w ⊂ z
⊂-cong x=w y=z ⟪ x<y , x⊆y ⟫ = ⟪ subst₂ (λ j k → j o< k) (==→o≡ x=w) (==→o≡ y=z) x<y , (λ wx → eq→ y=z (x⊆y (eq← x=w wx))) ⟫

import zorn 
open zorn O HODAxiom ho< AC _⊂_ ⊂-cong PO

-- all filter contains F                                                                              
F⊆X : { L P : HOD  } (LP : L ⊆ Power P) → Filter {L} {P} LP  → HOD
F⊆X {L} {P} LP F = record { od = record { def = λ x → IsFilter {L} {P} LP x ∧ ( filter F ⊆ * x)  } ; odmax = osuc (& L)
      ; <odmax = λ {x} lt → fx00 lt } where                                                             
      fx00 : {x : Ordinal } → IsFilter LP x ∧ filter F ⊆ * x → x o< osuc (& L)
      fx00 {x} lt = subst (λ k → k o< osuc (& L)) &iso ( ⊆→o≤ (IsFilter.f⊆L (proj1 lt ))  )

F→Maximum : {L P : HOD} (LP : L ⊆ Power P) → ({p q : HOD} → L ∋ p → L ∋ q → L ∋ (p ∩ q))
      → (F : Filter {L} {P} LP) → o∅ o< & L →  {y : Ordinal } → odef (filter F) y →  (¬ (filter F ∋ od∅)) → MaximumFilter {L} {P} LP F
F→Maximum {L} {P} LP CAP F 0<L {y} 0<F Fprop = record { mf = mf ; F⊆mf = λ {x} lt → eq← *iso (mf52 lt)
         ; proper = subst (λ k → ¬ ( odef (filter mf ) k)) (sym ord-od∅) ( IsFilter.proper imf)  ; is-maximum = mf50 }  where
      FX : HOD
      FX = F⊆X {L} {P} LP F
      oF = & (filter F)
      mf11 : { p q : Ordinal } → odef L q → odef (* oF) p →  (* p) ⊆ (* q)  → odef (* oF) q
      mf11 {p} {q} Lq Fp p⊆q = eq← *iso ( subst (λ k → odef (filter F) k ) &iso ( filter1 F (subst (λ k → odef L k) (sym &iso) Lq) 
             (eq→  *iso (subst (λ k → odef (* oF) k ) (sym &iso)  Fp)) p⊆q ))
      mf12 : { p q : Ordinal } → odef (* oF)  p →  odef (* oF) q  → odef L (& ((* p) ∩ (* q))) → odef (* oF) (& ((* p) ∩ (* q)))
      mf12 {p} {q} Fp Fq Lpq = eq← *iso  
        ( filter2 F (eq→ *iso (subst (λ k → odef (* oF) k ) (sym &iso)  Fp)) (eq→ *iso (subst (λ k → odef (* oF) k ) (sym &iso)  Fq)) Lpq)
      FX∋F : odef FX (& (filter F))
      FX∋F = ⟪ record { f⊆L = λ lt → f⊆L F (eq→ *iso lt ) ; filter1 = mf11 ; filter2 = mf12 
        ; proper = λ not → Fprop  (eq→ *iso (subst (λ k → odef (* (& (filter F)) ) k) (sym ord-od∅) not )) }  
          , (λ lt → eq← *iso lt ) ⟫ 
      -- 
      -- if filter B (which contains F) is transitive, Union B is also a filter which contains F
      --   and this is a SUP
      -- 
      SUP⊆ : (B : HOD) → B ⊆ FX → IsTotalOrderSet B → SUP FX B
      SUP⊆ B B⊆FX OB with trio< (& B) o∅ 
      ... | tri< a ¬b ¬c = ⊥-elim (¬x<0 a )
      ... | tri≈ ¬a b ¬c = record { sup = filter F ; isSUP = record { ax = FX∋F ; x≤sup = λ {y} zy → ⊥-elim (o<¬≡ (sym b) (∈∅< zy))  } } 
      ... | tri> ¬a ¬b 0<B = record { sup = Union B ; isSUP = record { ax = mf13 ; x≤sup = mf40 } } where
          mf20 : HOD
          mf20 = minimal B (λ eq → (o<¬≡ (sym (==→o≡ eq)) (subst (λ k → k o< & B) (sym ord-od∅) 0<B )))
          mf18 : odef B (& mf20 )
          mf18 = x∋minimal B (λ eq → (o<¬≡ (sym (==→o≡ eq)) (subst (λ k → k o< & B) (sym ord-od∅) 0<B )))
          mf16 : Union B ⊆ L
          mf16 record { owner = b ; ao = Bb ; ox = bx } = IsFilter.f⊆L ( proj1 ( B⊆FX Bb )) bx
          mf17 : {p q : Ordinal} → odef L q → odef (* (& (Union B))) p → * p ⊆ * q → odef (* (& (Union B))) q
          mf17 {p} {q} Lq bp p⊆q with eq→ *iso bp 
          ... | record { owner = owner ; ao = ao ; ox = ox } = eq← *iso  
             record { owner = owner ; ao = ao ; ox = IsFilter.filter1 mf30 Lq ox p⊆q } where
              mf30 : IsFilter {L} {P} LP owner
              mf30 = proj1 ( B⊆FX ao ) 
          mf31 : {p q : Ordinal} → odef (* (& (Union B))) p → odef (* (& (Union B))) q → odef L (& ((* p) ∩ (* q))) → odef (* (& (Union B))) (& ((* p) ∩ (* q)))
          mf31 {p} {q} bp bq Lpq with eq→ *iso bp | eq→ *iso bq
          ... | record { owner = bp ; ao = Bbp ; ox = bbp } | record { owner = bq ; ao = Bbq ; ox = bbq } 
             with OB (subst (λ k → odef B k) (sym &iso) Bbp) (subst (λ k → odef B k) (sym &iso) Bbq)
          ... | tri< bp⊂bq ¬b ¬c = eq← *iso record { owner = bq ; ao = Bbq ; ox = mf36 } where
              mf36 : odef (* bq) (& ((* p) ∩ (* q)))
              mf36 = IsFilter.filter2 mf30 (eq→ *iso (proj2 bp⊂bq (eq← *iso bbp))) bbq Lpq where
                  mf30 : IsFilter {L} {P} LP bq
                  mf30 = proj1 ( B⊆FX Bbq ) 
          ... | tri≈ ¬a bq=bp ¬c = eq← *iso record { owner = bp ; ao = Bbp ; ox = mf36 } where
              mf36 : odef (* bp) (& ((* p) ∩ (* q)))
              mf36 = IsFilter.filter2 mf30 bbp (eq→ (ord→== (sym bq=bp)) bbq) Lpq where
                  mf30 : IsFilter {L} {P} LP bp
                  mf30 = proj1 ( B⊆FX Bbp ) 
          ... | tri> ¬a ¬b bq⊂bp = eq← *iso  record { owner = bp ; ao = Bbp ; ox = mf36 } where
              mf36 : odef (* bp) (& ((* p) ∩ (* q)))
              mf36 = IsFilter.filter2 mf30 bbp (eq→ *iso (proj2 bq⊂bp (eq← *iso bbq))) Lpq where
                  mf30 : IsFilter {L} {P} LP bp
                  mf30 = proj1 ( B⊆FX Bbp ) 
          mf32 : ¬ odef (Union B) o∅
          mf32 record { owner = owner ; ao = bo ; ox = o0 } with proj1 ( B⊆FX bo ) 
          ... | record { f⊆L = f⊆L ; filter1 = filter1 ; filter2 = filter2 ; proper = proper } = ⊥-elim ( proper o0 )
          mf14 : IsFilter LP (& (Union B)) 
          mf14 = record { f⊆L = λ lt → mf16 (eq→ *iso lt) ; filter1 = mf17 ; filter2 = mf31 ; proper = λ not → mf32 (eq→ *iso not) } 
          mf15 :  filter F ⊆ Union B
          mf15 {x} Fx = record { owner = & mf20 ; ao = mf18 ; ox = eq← *iso (mf22 Fx) } where
               mf22 : odef (filter F) x → odef mf20 x
               mf22 Fx = eq→ *iso  ( proj2 (B⊆FX mf18) Fx )
          mf13 : odef FX (& (Union B))
          mf13 = ⟪ mf14  , (λ lt → eq← *iso (mf15 lt) ) ⟫
          mf42 : {z : Ordinal} → odef B z → * z ⊆  Union B
          mf42 {z} Bz {x} zx = record { owner  = _ ; ao = Bz ; ox = zx }
          mf40 : {z : Ordinal} → odef B z → (z ≡ & (Union B)) ∨ ( * z ⊂ * (& (Union B)) )
          mf40 {z} Bz with B⊆FX Bz
          ... | ⟪ filterz , F⊆z ⟫ with osuc-≡< ( ⊆→o≤ {* z} {Union B} (mf42 Bz) )
          ... | case1 eq = case1 (trans (sym &iso) eq )
          ... | case2 lt = case2 ⟪ subst₂ (λ j k →  j o< k ) refl (sym (==→o≡ *iso)) lt   , (λ lt → eq← *iso  (mf42 Bz lt ))  ⟫
      mx : Maximal  FX
      mx = Zorn-lemma (∈∅< FX∋F) SUP⊆  
      imf : IsFilter {L} {P} LP (& (Maximal.maximal mx))
      imf = proj1 (Maximal.as mx)
      mf00 : (* (& (Maximal.maximal mx))) ⊆ L
      mf00 = IsFilter.f⊆L imf   
      mf01 : { p q : HOD } →  L ∋ q → (* (& (Maximal.maximal mx))) ∋ p →  p ⊆ q  → (* (& (Maximal.maximal mx))) ∋ q
      mf01 {p} {q} Lq Fq p⊆q = IsFilter.filter1 imf Lq Fq 
              (λ {x} lt → eq← *iso ( p⊆q (eq→ *iso lt ) ))
      mf02 : { p q : HOD } → (* (& (Maximal.maximal mx))) ∋ p → (* (& (Maximal.maximal mx)))  ∋ q  → L ∋ (p ∩ q) 
          → (* (& (Maximal.maximal mx))) ∋ (p ∩ q)
      mf02 {p} {q} Fp Fq Lpq = subst (λ k → odef (* (& (Maximal.maximal mx))) k) (sym (==→o≡ *iso∩)) (
          IsFilter.filter2 imf Fp Fq (subst (λ k → odef L k) (==→o≡ *iso∩  ) Lpq ))
      mf : Filter {L} {P} LP
      mf = record { filter = * (& (Maximal.maximal mx)) ; f⊆L = mf00  
         ; filter1 = mf01  
         ; filter2 = mf02 }
      mf52 : filter F ⊆ Maximal.maximal mx
      mf52 = λ lt →  eq→ *iso (proj2 mf53 lt) where
         mf53 : FX ∋ Maximal.maximal mx 
         mf53 = Maximal.as mx 
      mf50 : (f : Filter LP) → ¬ (filter f ∋ od∅) → filter F ⊆ filter f → ¬ (* (& (zorn.Maximal.maximal mx)) ⊂ filter f)
      mf50 f proper F⊆f = λ m<f →(Maximal.¬maximal<x mx ⟪ Filter-is-Filter {L} {P} LP f proper  , mf51 ⟫  
            ⟪ subst (λ k → k o< & (filter f)) (==→o≡ *iso) (proj1 m<f) , (λ lt → proj2 m<f (eq← *iso lt)) ⟫ ) where
         mf51 : filter F ⊆ * (& (filter f))
         mf51 = λ lt → eq← *iso (F⊆f lt)

F→ultra : {L P : HOD} (LP : L ⊆ Power P) → (CAP : {p q : HOD} → L ∋ p → L ∋ q → L ∋ (p ∩ q))
      → (F : Filter {L} {P} LP) → (0<L : o∅ o< & L) →  {y : Ordinal} →  (0<F : odef (filter F) y) →  (proper : ¬ (filter F ∋ od∅)) 
      → ultra-filter ( MaximumFilter.mf (F→Maximum {L} {P} LP CAP F 0<L 0<F proper ))
F→ultra {L} {P} LP CAP F 0<L 0<F proper = max→ultra {L} {P} LP CAP F 0<F (F→Maximum {L} {P} LP CAP F 0<L 0<F proper ) 


