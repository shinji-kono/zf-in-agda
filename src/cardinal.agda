{-# OPTIONS --allow-unsolved-metas #-}

open import Level hiding (suc ; zero )
open import Ordinals
module cardinal {n : Level } (O : Ordinals {n}) where

open import logic
-- import OD
import OD hiding ( _⊆_ )

import ODC
open import Data.Nat 
open import Relation.Binary.PropositionalEquality
open import Data.Nat.Properties
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.Core

open inOrdinal O
open OD O
open OD.OD
open ODAxiom odAxiom
open import ZProduct O

import OrdUtil
import ODUtil
open Ordinals.Ordinals  O
open Ordinals.IsOrdinals isOrdinal
-- open Ordinals.IsNext isNext
open OrdUtil O
open ODUtil O

_⊆_ : ( A B : HOD ) → Set n
_⊆_ A B = {x : Ordinal } → odef A x → odef B x


open _∧_
open _∨_
open Bool
open _==_

open HOD

-- record HODBijection (A B : HOD ) : Set n where
--   field
--       fun←  : (x : Ordinal ) → odef A  x → Ordinal
--       fun→  : (x : Ordinal ) → odef B  x → Ordinal
--       funB  : (x : Ordinal ) → ( lt : odef A  x ) → odef B ( fun← x lt )
--       funA  : (x : Ordinal ) → ( lt : odef B  x ) → odef A ( fun→ x lt )
--       fiso← : (x : Ordinal ) → ( lt : odef B  x ) → fun← ( fun→ x lt ) ( funA x lt ) ≡ x
--       fiso→ : (x : Ordinal ) → ( lt : odef A  x ) → fun→ ( fun← x lt ) ( funB x lt ) ≡ x
-- 
-- rrdbij-refl : { a b : HOD } → a ≡ b → HODBijection a b
-- rrdbij-refl {a} refl = record {
--       fun←  = λ x _ → x 
--     ; fun→  = λ x _ → x 
--     ; funB  = λ x lt → lt
--     ; funA  = λ x lt → lt
--     ; fiso← = λ x lt → refl
--     ; fiso→ = λ x lt → refl
--    }

open Injection
open HODBijection

record IsImage (a b : Ordinal) (iab : Injection a b ) (x : Ordinal ) : Set n where
   field
      y : Ordinal 
      ay : odef (* a) y
      x=fy : x ≡ i→ iab _ ay

Image : (a : Ordinal) { b : Ordinal } → Injection a b → HOD
Image a {b} iab = record { od = record { def = λ x → IsImage a b iab x } ; odmax = b ; <odmax = im00  } where
    im00 : {x : Ordinal } → IsImage a b iab x → x o< b
    im00 {x} record { y = y ; ay = ay ; x=fy = x=fy } = subst₂ ( λ j k → j o< k) (trans &iso (sym x=fy)) &iso 
         (c<→o< (subst ( λ k → odef (* b) k) (sym &iso) (iB iab y ay)) )

record IsImage0 (a b : HOD) (f : (x : Ordinal) → odef a x → Ordinal) (x : Ordinal ) : Set n where
   field
      y : Ordinal 
      ay : odef a y
      x=fy : x ≡ f y ay

Image⊆b : { a b : Ordinal } → (iab : Injection a b) → Image a iab ⊆ * b 
Image⊆b {a} {b} iab {x} record { y = y ; ay = ay ; x=fy = x=fy } = subst (λ k → odef (* b) k) (sym x=fy) (iB iab y ay)

_=c=_ : ( A B : HOD ) → Set n
A =c= B = HODBijection A B 

≡→c= : {A B : HOD} → A ≡ B → A =c= B
≡→c= eq = hodbij-refl eq

open import BAlgebra O

_-_ : (a b : Ordinal ) → Ordinal 
a - b = & ( (* a) ＼ (* b) )

-→<  : (a b : Ordinal ) → (a - b) o≤ a
-→< a b = subst₂ (λ j k → j o≤ k) &iso &iso ( ⊆→o≤ ( λ {x} a-b → proj1 (subst ( λ k → odef k x) *iso a-b) ) )

b-a⊆b : {a b x : Ordinal } → odef (* (b - a)) x → odef (* b) x
b-a⊆b {a} {b} {x} lt with subst (λ k → odef k x) *iso lt
... | ⟪ bx , ¬ax ⟫ = bx

Injection-⊆ : {a b c : Ordinal } → * c ⊆ * a → Injection a b → Injection c b
Injection-⊆ {a} {b} {c} le f = record { i→ = λ x cx → i→ f x (le cx) ; iB = λ x cx → iB f x (le cx) 
        ; inject = λ x y ix iy eq → inject f x y (le ix) (le iy) eq  } 

Injection-∙ : {a b c : Ordinal } → Injection a b → Injection b c → Injection a c
Injection-∙ {a} {b} {c} f g = record { i→ = λ x ax → i→ g (i→ f x ax) (iB f x ax) ; iB = λ x ax → iB g (i→ f x ax) (iB f x ax)
        ; inject = λ x y ix iy eq → inject f x y ix iy (inject g (i→ f x ix) (i→ f y iy) (iB f x ix) (iB f y iy) eq)   } 

bi-∪  : {A B C D : HOD } → (ab : HODBijection A B) → (cd : HODBijection C D )  
       → HODBijection (A ∪ C) (B ∪ D)
bi-∪  {A} {B} {C} {D} ab cd = record { 
         fun←  = fa
       ; fun→  = fb
       ; funB  = fa-isb
       ; funA  = fb-isa
       ; fiso← = faiso
       ; fiso→ = fbiso
       } where
          fa : (x : Ordinal) → odef (A ∪ C) x → Ordinal
          fa x (case1 a) = fun← ab x a
          fa x (case2 c) = fun← cd x c
          fb : (x : Ordinal) → odef (B ∪ D) x → Ordinal
          fb x (case1 b) = fun→ ab x b
          fb x (case2 d) = fun→ cd x d
          fa-isb :  (x : Ordinal) (lt : odef (A ∪ C) x) → odef (B ∪ D) (fa x lt)
          fa-isb x (case1 a) = case1 (funB ab x a)
          fa-isb x (case2 c) = case2 (funB cd x c)
          fb-isa :  (x : Ordinal) (lt : odef (B ∪ D) x) → odef (A ∪ C) (fb x lt)
          fb-isa x (case1 b) = case1 (funA ab x b)
          fb-isa x (case2 d) = case2 (funA cd x d)
          faiso : (x : Ordinal) (lt : odef (B ∪ D) x) → fa (fb x lt) (fb-isa x lt) ≡ x
          faiso x (case1 b) = fiso← ab x b
          faiso x (case2 d) = fiso← cd x d
          fbiso : (x : Ordinal) (lt : odef (A ∪ C) x) → fb (fa x lt) (fa-isb x lt) ≡ x
          fbiso x (case1 b) = fiso→ ab x b
          fbiso x (case2 d) = fiso→ cd x d

Bernstein : {a b : Ordinal } → Injection a b → Injection b a → HODBijection (* a) (* b)
Bernstein {a} {b} (f @ record { i→ = fab ; iB = b∋fab ; inject = fab-inject }) ( g @ record { i→ = fba ; iB = a∋fba ; inject = fba-inject })
     = subst₂ (λ j k → HODBijection j k ) (sym a=UC∨a-UC) (sym b=fUC∨b-fUC) (bi-∪  bi-UC  bi-fUC)
 where
      gf : Injection a a
      gf = record { i→ = λ x ax → fba (fab x ax) (b∋fab x ax) ; iB = λ x ax → a∋fba _ (b∋fab x ax) 
         ; inject = λ x y ax ay eq → fab-inject _ _ ax ay ( fba-inject _ _ (b∋fab _ ax) (b∋fab _ ay) eq) } 

      data gfImage :  (x : Ordinal) → Set n where
          a-g : {x : Ordinal} → (ax : odef (* a) x ) → (¬ib : ¬ ( IsImage b a g x )) → gfImage  x
          next-gf : {x : Ordinal} → (ix : IsImage a a gf x) → (gfiy : gfImage (IsImage.y ix) ) → gfImage  x

      a∋gfImage : {x : Ordinal } → gfImage x → odef (* a) x
      a∋gfImage {x} (a-g ax ¬ib) = ax
      a∋gfImage  {x} (next-gf record { y = y ; ay = ay ; x=fy = x=fy } lt ) = subst (λ k → odef (* a) k ) (sym x=fy) (a∋fba _ (b∋fab y ay) )

      UC : HOD
      UC = record { od = record { def = λ x → gfImage x } ; odmax = & (* a) ; <odmax = λ lt → odef< (a∋gfImage lt)  }

      a-UC : HOD
      a-UC = record { od = record { def = λ x → odef (* a) x ∧ (¬ gfImage x) } ; odmax = & (* a) 
          ; <odmax = λ lt → odef< (proj1 lt)  }

      a=UC∨a-UC : * a ≡ UC ∪ a-UC
      a=UC∨a-UC = ==→o≡ record { eq→ = be00 ; eq← = be01 } where
           be00 : {x : Ordinal} → odef (* a) x → odef (UC ∪ a-UC) x
           be00 {x} ax with ODC.p∨¬p O ( gfImage x)
           ... | case1 gfx = case1 gfx
           ... | case2 ngfx = case2 ⟪ ax , ngfx ⟫
           be01 : {x : Ordinal} → odef (UC ∪ a-UC) x → odef (* a) x 
           be01 {x} (case1 gfx) = a∋gfImage gfx
           be01 {x} (case2 ngfx) = proj1 ngfx

      FA : (x : Ordinal) → (ax : gfImage x) → Ordinal
      FA x ax = fab x (a∋gfImage ax)

      b∋Uf1 : (x : Ordinal) → IsImage0 UC (* b) FA x → odef (* b) x
      b∋Uf1 x record { y = y ; ay = ay ; x=fy = x=fy } = subst (λ k → odef (* b) k ) (sym x=fy) (b∋fab y (a∋gfImage ay))

      fUC : HOD
      fUC = record { od = record { def = λ x → IsImage0 UC (* b) FA  x } ; odmax = & (* b) ; <odmax = λ {x} lt → odef< (b∋Uf1 x lt)} 

      b-fUC : HOD
      b-fUC = record { od = record { def = λ x → odef (* b) x ∧ (¬ IsImage0 UC (* b) FA  x) } ; odmax = & (* b) ; <odmax = λ lt → odef∧< lt  }

      b=fUC∨b-fUC : * b ≡ fUC ∪ b-fUC
      b=fUC∨b-fUC = ==→o≡ record { eq→ = be00 ; eq← = be01 } where
           be00 : {x : Ordinal} → odef (* b) x → odef (fUC ∪ b-fUC) x
           be00 {x} bx with ODC.p∨¬p O (IsImage0 UC (* b) FA  x)
           ... | case1 gfx = case1 gfx
           ... | case2 ngfx = case2 ⟪ bx , ngfx ⟫
           be01 : {x : Ordinal} → odef (fUC ∪ b-fUC) x → odef (* b) x 
           be01 {x} (case1 record { y = y ; ay = ay ; x=fy = x=fy }) = subst (λ k → odef (* b) k) (sym x=fy) ( b∋fab y (a∋gfImage ay))
           be01 {x} (case2 ngfx) = proj1 ngfx

      nimg : {x : Ordinal } → (ax : odef (* a) x ) → ¬ (odef UC x) → IsImage b a g x
      nimg {x} ax ncn with ODC.p∨¬p O (IsImage b a g x)
      ... | case1 img = img
      ... | case2 nimg = ⊥-elim ( ncn (a-g ax nimg ) )

      open import Relation.Binary.HeterogeneousEquality as HE using (_≅_ )

      fab-eq : {x y : Ordinal } → {ax : odef (* a) x} {ax1 : odef (* a) y}  → x ≡ y  → fab x ax ≡ fab y ax1
      fab-eq {x} {x} {ax} {ax1} refl = cong (λ k → fab x k) ( HE.≅-to-≡ ( ∋-irr {* a} ax ax1 ))  

      fba-eq : {x y : Ordinal } → {bx : odef (* b) x} {bx1 : odef (* b) y}  → x ≡ y  → fba x bx ≡ fba y bx1
      fba-eq {x} {x} {bx} {bx1} refl = cong (λ k → fba x k) ( HE.≅-to-≡ ( ∋-irr {* b} bx bx1 ))  

      g⁻¹ : {x : Ordinal } → (ax : odef (* a) x) → (nc0 : IsImage b a g x ) → Ordinal
      g⁻¹ {x} ax record { y = y ; ay = ay ; x=fy = x=fy } = y

      b∋g⁻¹ : {x : Ordinal } → (ax : odef (* a) x) (nc0 : IsImage b a g x ) → odef (* b) (g⁻¹ ax nc0)
      b∋g⁻¹ {x} ax record { y = y ; ay = ay ; x=fy = x=fy } = ay

      g⁻¹-iso : {x : Ordinal } → (ax : odef (* a) x) → (nc0 : IsImage b a g x ) → fba (g⁻¹ ax nc0) (b∋g⁻¹ ax nc0) ≡ x
      g⁻¹-iso {x} ax record { y = y ; ay = ay ; x=fy = x=fy } = sym x=fy

      g⁻¹-iso1 : {x : Ordinal } → (bx : odef (* b) x) → (nc0 : IsImage b a g (fba x bx) )  → g⁻¹ (a∋fba x bx) nc0  ≡ x
      g⁻¹-iso1 {x} bx nc0 = inject g _ _ (b∋g⁻¹ (a∋fba x bx) nc0) bx (g⁻¹-iso (a∋fba x bx) nc0) 

      g⁻¹-eq : {x : Ordinal } → (ax ax' : odef (* a) x) → {nc0 nc0' : IsImage b a g x } → g⁻¹ ax nc0 ≡ g⁻¹ ax' nc0'
      g⁻¹-eq {x} ax ax' {record { y = y₁ ; ay = ay₁ ; x=fy = x=fy₁ }} {record { y = y ; ay = ay ; x=fy = x=fy }} 
           = inject g _ _ ay₁ ay (trans (sym x=fy₁) x=fy )


      cc11-case2 : {x : Ordinal} (ax : odef (* a) x) 
          → (ncn : ¬ gfImage x) 
          → ¬ IsImage0 UC (* b) (λ x ax → fab x (a∋gfImage ax))  (g⁻¹ ax (nimg ax ncn))
      cc11-case2 {x} ax ncn record { y = y ; ay = ay ; x=fy = x=fy } with nimg ax ncn
      ... | record { y = y1 ; ay = ay1 ; x=fy = x=fy1 } = ncn ( subst (λ k → gfImage k) be113 
                                            (next-gf record { y = y ; ay = (a∋gfImage ay) ; x=fy = refl } ay ) )  where
               be113 : fba (fab y (a∋gfImage ay)) (b∋fab y (a∋gfImage ay)) ≡ x
               be113 = begin
                    fba (fab y (a∋gfImage ay)) (b∋fab y (a∋gfImage ay)) ≡⟨ fba-eq (sym x=fy)  ⟩
                    fba y1 ay1 ≡⟨ sym (x=fy1) ⟩
                    x ∎ where open ≡-Reasoning

      cc10-case2 : {x : Ordinal } → (bx : odef (* b) x )
         → ¬ IsImage0 UC (* b) (λ x ax → fab x (a∋gfImage ax))  x
         → ¬ gfImage (fba x bx)
      cc10-case2 {x} bx nix (a-g ax ¬ib) = ¬ib record { y = _ ; ay = bx ; x=fy = refl }
      cc10-case2 {x} bx nix (next-gf record { y = y ; ay = ay ; x=fy = x=fy } gfy) 
           = nix record { y = _ ; ay = gfy ; x=fy = inject g _ _ bx (b∋fab y (a∋gfImage gfy)) (trans x=fy (fba-eq (fab-eq refl))) }

      fU1 : (x : Ordinal) → odef UC x → Ordinal
      fU1 x gfx = fab x (a∋gfImage gfx)

      Uf1 : (x : Ordinal) → IsImage0 UC (* b) FA x → Ordinal
      Uf1 x record { y = y ; ay = ay ; x=fy = x=fy } = y


      UC∋Uf1 : {x : Ordinal } → (lt : odef fUC x) → odef UC (Uf1 x lt )
      UC∋Uf1 {x} record { y = y ; ay = ay ; x=fy = x=fy } = ay

      fU-iso1 : {x : Ordinal } → (lt : odef fUC x) → fU1 (Uf1 x lt) (UC∋Uf1 lt) ≡ x
      fU-iso1 {x} record { y = y ; ay = (a-g ax ¬ib) ; x=fy = x=fy } = trans (fab-eq refl) (sym x=fy) 
      fU-iso1 {x} record { y = y ; ay = (next-gf record { y = y₁ ; ay = ay₁ ; x=fy = x=fy₁ } ay) ; x=fy = x=fy } = trans (fab-eq refl) (sym x=fy) 

      fU-iso0 : {x : Ordinal } → (lt : odef UC x) → Uf1 (fU1 x lt) record { y = _ ; ay = lt ; x=fy = refl } ≡ x
      fU-iso0 {x} (a-g ax ¬ib) = refl 
      fU-iso0 {x} (next-gf record { y = y ; ay = ay ; x=fy = x=fy } lt) = refl

      bi-UC : HODBijection UC fUC
      bi-UC = record { 
         fun←  = λ x lt → fU1 x lt
       ; fun→  = λ x lt → Uf1 x lt
       ; funB  = λ x lt → record { y = _ ; ay = lt  ; x=fy = refl }
       ; funA  = λ x lt → UC∋Uf1 lt
       ; fiso← = λ x lt → fU-iso1 lt
       ; fiso→ = λ x lt → fU-iso0 lt
       }

      b-FUC∋g⁻¹ : {x : Ordinal } → (lt : odef a-UC x )→ odef b-fUC (g⁻¹ (proj1 lt) (nimg (proj1 lt) (proj2 lt))) 
      b-FUC∋g⁻¹ {x} ⟪ ax , ngfix ⟫ = ⟪ b∋g⁻¹ ax (nimg ax ngfix) , cc11-case2 ax ngfix  ⟫

      a-UC∋g : {x : Ordinal } → (lt : odef b-fUC x) → odef a-UC (fba x (proj1 lt ))
      a-UC∋g {x} ⟪ bx , ¬img ⟫ = ⟪ a∋fba x bx , cc10-case2 bx ¬img ⟫

      fUC-iso1 : {x : Ordinal } → (lt : odef b-fUC x ) → g⁻¹ (proj1 (a-UC∋g lt)) (nimg (proj1 (a-UC∋g lt)) (proj2 (a-UC∋g lt))) ≡ x
      fUC-iso1 {x} lt with nimg (proj1 (a-UC∋g lt)) (proj2 (a-UC∋g lt))
      ... | record { y = y ; ay = ay ; x=fy = x=fy } = sym ( inject g _ _ (proj1 lt) ay x=fy )

      fUC-iso0 : {x : Ordinal} → (lt : odef a-UC x) →  fba (g⁻¹ (proj1 lt) (nimg (proj1 lt) (proj2 lt))) (proj1 (b-FUC∋g⁻¹ lt)) ≡ x
      fUC-iso0 {x} lt with nimg (proj1 lt) (proj2 lt)
      ... | record { y = y ; ay = ay ; x=fy = x=fy } = sym x=fy

      bi-fUC : HODBijection a-UC b-fUC
      bi-fUC = record { 
         fun←  = λ x lt → g⁻¹ (proj1 lt) (nimg (proj1 lt) (proj2 lt))
       ; fun→  = λ x lt → fba x (proj1 lt)
       ; funB  = λ x lt → b-FUC∋g⁻¹  lt
       ; funA  = λ x lt → a-UC∋g lt
       ; fiso← = λ x lt → fUC-iso1 lt
       ; fiso→ = λ x lt → fUC-iso0 lt
       }


_c<_ : ( A B : HOD ) → Set n
A c< B = ¬ ( Injection (& A)  (& B) )

Card : OD
Card = record { def = λ x → (a : Ordinal) → a o< x → ¬ HODBijection (* a) (* x) }

record Cardinal (a : Ordinal ) : Set (Level.suc n) where
   field
       card : Ordinal
       ciso : HODBijection (* a) (* card)
       cmax : (x : Ordinal) → card o< x → ¬ HODBijection (* a) (* x)

Cardinal∈ : { s : HOD } → { t : Ordinal } → Ord t ∋ s →   s c< Ord t
Cardinal∈ = {!!}

Cardinal⊆ : { s t : HOD } → s ⊆ t →  ( s c< t ) ∨ ( s =c= t )
Cardinal⊆ = {!!}

Cantor1 : { u : HOD } → u c< Power u
Cantor1 = {!!}

Cantor2 : { u : HOD } → ¬ ( u =c=  Power u )
Cantor2 = {!!}




