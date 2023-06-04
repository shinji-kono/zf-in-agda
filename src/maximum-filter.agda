{-# OPTIONS --allow-unsolved-metas #-} 

open import Level
open import Ordinals
module maximum-filter {n : Level } (O : Ordinals {n})   where

open import logic
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
-- open Ordinals.IsNext isNext
open OrdUtil O
open ODUtil O


import ODC
open ODC O

open _∧_
open _∨_
open Bool

open import filter O

open Filter


open import  Relation.Binary
open import  Relation.Binary.Structures

PO : IsStrictPartialOrder _≡_ _⊂_ 
PO = record { isEquivalence = record { refl = refl ; sym = sym ; trans = trans }
   ; trans = λ {a} {b} {c} → trans-⊂ {a} {b} {c}
   ; irrefl = λ x=y x<y → o<¬≡ (cong (&) x=y) (proj1 x<y)
   ; <-resp-≈ =  record { fst = ( λ {x} {y} {y1} y=y1 xy1 → subst (λ k → x ⊂ k) y=y1 xy1  )
                        ; snd = (λ {x} {x1} {y} x=x1 x1y → subst (λ k → k ⊂ x) x=x1 x1y ) } }

import zorn 
open zorn O _⊂_ PO


-- all filter contains F                                                                              
F⊆X : { L P : HOD  } (LP : L ⊆ Power P) → Filter {L} {P} LP  → HOD
F⊆X {L} {P} LP F = record { od = record { def = λ x → IsFilter {L} {P} LP x ∧ ( filter F ⊆ * x)  } ; odmax = osuc (& L)
      ; <odmax = λ {x} lt → fx00 lt } where                                                             
      fx00 : {x : Ordinal } → IsFilter LP x ∧ filter F ⊆ * x → x o< osuc (& L)
      fx00 {x} lt = subst (λ k → k o< osuc (& L)) &iso ( ⊆→o≤ (IsFilter.f⊆L (proj1 lt ))  )

F→Maximum : {L P : HOD} (LP : L ⊆ Power P) → ({p q : HOD} → L ∋ p → L ∋ q → L ∋ (p ∩ q))
      → (F : Filter {L} {P} LP) → o∅ o< & L →  {y : Ordinal } → odef (filter F) y →  (¬ (filter F ∋ od∅)) → MaximumFilter {L} {P} LP F
F→Maximum {L} {P} LP CAP F 0<L {y} 0<F Fprop = record { mf = mf ; F⊆mf = subst (λ k → filter F ⊆ k ) (sym *iso) mf52  
         ; proper = subst (λ k → ¬ ( odef (filter mf ) k)) (sym ord-od∅) ( IsFilter.proper imf)  ; is-maximum = mf50 }  where
      FX : HOD
      FX = F⊆X {L} {P} LP F
      oF = & (filter F)
      mf11 : { p q : Ordinal } → odef L q → odef (* oF) p →  (* p) ⊆ (* q)  → odef (* oF) q
      mf11 {p} {q} Lq Fp p⊆q = subst₂ (λ j k → odef j k ) (sym *iso) &iso ( filter1 F (subst (λ k → odef L k) (sym &iso) Lq) 
             (subst₂ (λ j k → odef j k ) *iso (sym &iso)  Fp) p⊆q )
      mf12 : { p q : Ordinal } → odef (* oF)  p →  odef (* oF) q  → odef L (& ((* p) ∩ (* q))) → odef (* oF) (& ((* p) ∩ (* q)))
      mf12 {p} {q} Fp Fq Lpq = subst (λ k → odef k (& ((* p) ∩ (* q))) ) (sym *iso) 
        ( filter2 F (subst₂ (λ j k → odef j k ) *iso (sym &iso)  Fp) (subst₂ (λ j k → odef j k ) *iso (sym &iso)  Fq) Lpq)
      FX∋F : odef FX (& (filter F))
      FX∋F = ⟪ record { f⊆L = subst (λ k → k ⊆ L) (sym *iso) (f⊆L F) ; filter1 = mf11 ; filter2 = mf12 
        ; proper = subst₂ (λ j k →  ¬ (odef j k) ) (sym *iso) ord-od∅ Fprop  }  
          , subst (λ k → filter F ⊆ k ) (sym *iso) ( λ x → x ) ⟫ 
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
          mf20 = ODC.minimal O B (λ eq → (o<¬≡ (cong (&) (sym (==→o≡ eq))) (subst (λ k → k o< & B) (sym ord-od∅) 0<B )))
          mf18 : odef B (& mf20 )
          mf18 = ODC.x∋minimal O B (λ eq → (o<¬≡ (cong (&) (sym (==→o≡ eq))) (subst (λ k → k o< & B) (sym ord-od∅) 0<B )))
          mf16 : Union B ⊆ L
          mf16 record { owner = b ; ao = Bb ; ox = bx } = IsFilter.f⊆L ( proj1 ( B⊆FX Bb )) bx
          mf17 : {p q : Ordinal} → odef L q → odef (* (& (Union B))) p → * p ⊆ * q → odef (* (& (Union B))) q
          mf17 {p} {q} Lq bp p⊆q with subst (λ k → odef k p ) *iso bp
          ... | record { owner = owner ; ao = ao ; ox = ox } = subst (λ k → odef k q) (sym *iso) 
                record { owner = owner ; ao = ao ; ox = IsFilter.filter1 mf30 Lq ox p⊆q } where
              mf30 : IsFilter {L} {P} LP owner
              mf30 = proj1 ( B⊆FX ao ) 
          mf31 : {p q : Ordinal} → odef (* (& (Union B))) p → odef (* (& (Union B))) q → odef L (& ((* p) ∩ (* q))) → odef (* (& (Union B))) (& ((* p) ∩ (* q)))
          mf31 {p} {q} bp bq Lpq with subst (λ k → odef k p ) *iso bp | subst (λ k → odef k q ) *iso bq
          ... | record { owner = bp ; ao = Bbp ; ox = bbp } | record { owner = bq ; ao = Bbq ; ox = bbq } 
             with OB (subst (λ k → odef B k) (sym &iso) Bbp) (subst (λ k → odef B k) (sym &iso) Bbq)
          ... | tri< bp⊂bq ¬b ¬c = subst₂ (λ j k → odef j k ) (sym  *iso) refl record { owner = bq ; ao = Bbq ; ox = mf36 } where
              mf36 : odef (* bq) (& ((* p) ∩ (* q)))
              mf36 = IsFilter.filter2 mf30 (proj2 bp⊂bq bbp) bbq Lpq where
                  mf30 : IsFilter {L} {P} LP bq
                  mf30 = proj1 ( B⊆FX Bbq ) 
          ... | tri≈ ¬a bq=bp ¬c = subst₂ (λ j k → odef j k ) (sym  *iso) refl record { owner = bp ; ao = Bbp ; ox = mf36 } where
              mf36 : odef (* bp) (& ((* p) ∩ (* q)))
              mf36 = IsFilter.filter2 mf30 bbp (subst (λ k → odef k q) (sym bq=bp) bbq) Lpq where
                  mf30 : IsFilter {L} {P} LP bp
                  mf30 = proj1 ( B⊆FX Bbp ) 
          ... | tri> ¬a ¬b bq⊂bp = subst₂ (λ j k → odef j k ) (sym  *iso) refl record { owner = bp ; ao = Bbp ; ox = mf36 } where
              mf36 : odef (* bp) (& ((* p) ∩ (* q)))
              mf36 = IsFilter.filter2 mf30 bbp (proj2 bq⊂bp bbq) Lpq where
                  mf30 : IsFilter {L} {P} LP bp
                  mf30 = proj1 ( B⊆FX Bbp ) 
          mf32 : ¬ odef (Union B) o∅
          mf32 record { owner = owner ; ao = bo ; ox = o0 } with proj1 ( B⊆FX bo ) 
          ... | record { f⊆L = f⊆L ; filter1 = filter1 ; filter2 = filter2 ; proper = proper } = ⊥-elim ( proper o0 )
          mf14 : IsFilter LP (& (Union B)) 
          mf14 = record { f⊆L = subst (λ k → k ⊆ L) (sym *iso) mf16 ; filter1 = mf17 ; filter2 = mf31 ; proper = subst (λ k → ¬ odef k o∅) (sym *iso) mf32 } 
          mf15 :  filter F ⊆ Union B
          mf15 {x} Fx = record { owner = & mf20 ; ao = mf18 ; ox = subst (λ k → odef k x) (sym *iso) (mf22 Fx) } where
               mf22 : odef (filter F) x → odef mf20 x
               mf22 Fx = subst (λ k → odef k x) *iso ( proj2 (B⊆FX mf18) Fx )
          mf13 : odef FX (& (Union B))
          mf13 = ⟪ mf14  , subst (λ k → filter F ⊆ k ) (sym *iso) mf15  ⟫
          mf42 : {z : Ordinal} → odef B z → * z ⊆  Union B
          mf42 {z} Bz {x} zx = record { owner  = _ ; ao = Bz ; ox = zx }
          mf40 : {z : Ordinal} → odef B z → (z ≡ & (Union B)) ∨ ( * z ⊂ * (& (Union B)) )
          mf40 {z} Bz with B⊆FX Bz
          ... | ⟪ filterz , F⊆z ⟫ with osuc-≡< ( ⊆→o≤ {* z} {Union B} (mf42 Bz) )
          ... | case1 eq = case1 (trans (sym &iso) eq )
          ... | case2 lt = case2 ⟪ subst₂ (λ j k → j o< & k ) refl (sym *iso) lt  , subst (λ  k → * z ⊆ k) (sym *iso)  (mf42 Bz)  ⟫
      mx : Maximal  FX
      mx = Zorn-lemma (∈∅< FX∋F) SUP⊆  
      imf : IsFilter {L} {P} LP (& (Maximal.maximal mx))
      imf = proj1 (Maximal.as mx)
      mf00 : (* (& (Maximal.maximal mx))) ⊆ L
      mf00 = IsFilter.f⊆L imf   
      mf01 : { p q : HOD } →  L ∋ q → (* (& (Maximal.maximal mx))) ∋ p →  p ⊆ q  → (* (& (Maximal.maximal mx))) ∋ q
      mf01 {p} {q} Lq Fq p⊆q = IsFilter.filter1 imf Lq Fq 
              (λ {x} lt → subst (λ k → odef k x) (sym *iso) ( p⊆q (subst (λ k → odef k x) *iso lt ) ))
      mf02 : { p q : HOD } → (* (& (Maximal.maximal mx))) ∋ p → (* (& (Maximal.maximal mx)))  ∋ q  → L ∋ (p ∩ q) 
          → (* (& (Maximal.maximal mx))) ∋ (p ∩ q)
      mf02 {p} {q} Fp Fq Lpq = subst₂ (λ j k → odef (* (& (Maximal.maximal mx))) (& (j ∩ k ))) *iso *iso (
          IsFilter.filter2 imf Fp Fq (subst₂ (λ j k → odef L (& (j ∩ k ))) (sym *iso) (sym *iso) Lpq ))
      mf : Filter {L} {P} LP
      mf = record { filter = * (& (Maximal.maximal mx)) ; f⊆L = mf00  
         ; filter1 = mf01  
         ; filter2 = mf02 }
      mf52 : filter F ⊆ Maximal.maximal mx
      mf52 = subst (λ k → filter F ⊆ k ) *iso (proj2 mf53) where
         mf53 : FX ∋ Maximal.maximal mx 
         mf53 = Maximal.as mx 
      mf50 : (f : Filter LP) → ¬ (filter f ∋ od∅) → filter F ⊆ filter f → ¬ (* (& (zorn.Maximal.maximal mx)) ⊂ filter f)
      mf50 f proper F⊆f = subst (λ k → ¬ ( k ⊂ filter f )) (sym *iso) (Maximal.¬maximal<x mx ⟪ Filter-is-Filter {L} {P} LP f proper  , mf51 ⟫ ) where
         mf51 : filter F ⊆ * (& (filter f))
         mf51 = subst (λ k → filter F ⊆ k ) (sym *iso) F⊆f 

F→ultra : {L P : HOD} (LP : L ⊆ Power P) → (CAP : {p q : HOD} → L ∋ p → L ∋ q → L ∋ (p ∩ q))
      → (F : Filter {L} {P} LP) → (0<L : o∅ o< & L) →  {y : Ordinal} →  (0<F : odef (filter F) y) →  (proper : ¬ (filter F ∋ od∅)) 
      → ultra-filter ( MaximumFilter.mf (F→Maximum {L} {P} LP CAP F 0<L 0<F proper ))
F→ultra {L} {P} LP CAP F 0<L 0<F proper = max→ultra {L} {P} LP CAP F 0<F (F→Maximum {L} {P} LP CAP F 0<L 0<F proper ) 


