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
module cardinal {n : Level } (O : Ordinals {n} ) (HODAxiom : HODBase.ODAxiom O)  (ho< : OD.ODAxiom-ho< O HODAxiom )
       (AC : OD.AxiomOfChoice O HODAxiom ) where


open import  Relation.Binary.PropositionalEquality hiding ( [_] )
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

-- open import Relation.Binary hiding ( _⇔_ )
open import Data.Empty 
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Definitions
open import Data.Nat renaming ( zero to Zero ; suc to Suc ;  ℕ to Nat ; _⊔_ to _n⊔_ ) 
import BAlgebra 

-- open BAlgebra O
open import ZProduct O HODAxiom ho<


-------
--    the set of finite partial functions from ω to 2
--
--

open import Data.List hiding (filter)
open import Data.Maybe 


-- record HODBijection (A B : HOD ) : Set n where
--   field
--       fun→  : (x : Ordinal ) → odef B  x → Ordinal
--       fun←  : (x : Ordinal ) → odef A  x → Ordinal
--       funB  : (x : Ordinal ) → ( lt : odef A  x ) → odef B ( fun← x lt )
--       funA  : (x : Ordinal ) → ( lt : odef B  x ) → odef A ( fun→ x lt )
--       fiso→ : (x : Ordinal ) → ( lt : odef A  x ) → fun→ ( fun← x lt ) ( funB x lt ) ≡ x
--       fiso← : (x : Ordinal ) → ( lt : odef B  x ) → fun← ( fun→ x lt ) ( funA x lt ) ≡ x
 
open Injection        -- in ZProduct
open HODBijection

record IsImage0 (a b : HOD) (f : (x : Ordinal) → odef a x → Ordinal) (x : Ordinal ) : Set n where
   field
      y : Ordinal 
      ay : odef a y
      x=fy : x ≡ f y ay

IsImage : (a b : Ordinal) (iab : Injection a b ) (x : Ordinal ) → Set n 
IsImage a b iab x = IsImage0 (* a) (* b) (λ x ax → i→ iab x) x

Image : (a : Ordinal) { b : Ordinal } → Injection a b → HOD
Image a {b} iab = record { od = record { def = λ x → IsImage a b iab x } ; odmax = b ; <odmax = im00  } where
    im00 : {x : Ordinal } → IsImage a b iab x → x o< b
    im00 {x} record { y = y ; ay = ay ; x=fy = x=fy } = subst₂ ( λ j k → j o< k) (trans &iso (sym x=fy)) &iso 
         (c<→o< (subst ( λ k → odef (* b) k) (sym &iso) (iB iab y ay)) )

Image⊆b : { a b : Ordinal } → (iab : Injection a b) → Image a iab ⊆ (* b )
Image⊆b {a} {b} iab {x} record { y = y ; ay = ay ; x=fy = x=fy } = subst (λ k → odef (* b) k) (sym x=fy) (iB iab y ay)

_=c=_ : ( A B : HOD ) → Set n
A =c= B = HODBijection A B 

≡→c= : {A B : HOD} → A ≡ B → A =c= B
≡→c= eq = hodbij-refl eq

open import BAlgebra O

b-a⊆b : {a b x : Ordinal } → odef ((* b) ＼ (* a)) x → odef (* b) x
b-a⊆b {a} {b} {x} ⟪ bx , nax ⟫ = bx

Injection-⊆ : {a b c : Ordinal } → * c ⊆ * a → Injection a b → Injection c b
Injection-⊆ {a} {b} {c} le f = record { i→ = λ x → i→ f x  ; iB = λ x cx → iB f x (le cx) 
        ; inject = λ x y ix iy eq → inject f x y (le ix) (le iy) eq  }

Injection-∙ : {a b c : Ordinal } → Injection a b → Injection b c → Injection a c
Injection-∙ {a} {b} {c} f g = record { i→ = λ x  → i→ g (i→ f x ) ; iB = λ x ax → iB g (i→ f x ) (iB f x ax) 
           ; inject = λ x y ix iy eq → inject f _ _ ix iy (inject g _ _ (iB f x ix ) (iB f y iy ) eq ) }

WellDefined : {A : HOD} → (f : (x : Ordinal ) → odef A x → Ordinal ) → Set n
WellDefined {A} f = (x : Ordinal ) → ( lt1 lt2 : odef A  x ) → f x lt1 ≡ f x lt2 

==-bi : {A B C : HOD } → (ab : HODBijection A B) 
    → (A =h= C → HODBijection C B) ∧ (B =h= C → HODBijection A C) 
proj1 (==-bi {A} {B} {C} ab ) a=c = record {
         fun→  = λ x cx → fun→ ab x (eq← a=c cx)
       ; fun←  = fun← ab 
       ; funB  = λ x cx → funB ab x (eq← a=c cx)
       ; funA  = λ x cx → eq→ a=c (funA ab x cx)
       ; fiso→ = λ x bx → trans (fcong→ ab _ _ _ _  refl ) (fiso→ ab x bx )
       ; fiso← = λ x cx → fiso← ab x (eq← a=c cx)
       ; fcong→ = λ x y cx cy eq → fcong→ ab x y (eq← a=c cx) (eq← a=c cy) eq
       ; fcong← = fcong← ab 
       } 
proj2 (==-bi {A} {B} {C} ab ) b=c = record {
         fun→  = λ x cx → fun→ ab x cx
       ; fun←  = λ x bx → fun← ab x (eq← b=c bx)
       ; funB  = λ x cx → eq→  b=c (funB ab x cx)
       ; funA  = λ x cx → funA ab x (eq← b=c cx)
       ; fiso→ = λ x cx → fiso→ ab x (eq← b=c cx)
       ; fiso← = λ x bx → trans (fcong← ab _ _ _ _  refl ) (fiso← ab x bx )
       ; fcong→ = fcong→ ab
       ; fcong← = λ x y cx cy eq → fcong← ab x y (eq← b=c cx) (eq← b=c cy) eq
       }    

--
-- Two injection can be joined
--   A and C may overrap
--
bi-∪  : {A B C D : HOD } → (ab : HODBijection A B) → (cd : HODBijection C D )  
       → ((A ∩ C) =h= od∅) → ((B ∩ D) =h= od∅)
       → HODBijection (A ∪ C) (B ∪ D)
bi-∪  {A} {B} {C} {D} ab cd nac nbd = record { 
         fun→  = fa
       ; fun←  = fb
       ; funB  = fa-isb
       ; funA  = fb-isa
       ; fiso→ = faiso
       ; fiso← = fbiso
       ; fcong→ = facong
       ; fcong← = fbcong
       } where
          fa : (x : Ordinal) → odef (A ∪ C) x → Ordinal
          fa x (case1 a) = fun→ ab x a
          fa x (case2 c) = fun→ cd x c
          fb : (x : Ordinal) → odef (B ∪ D) x → Ordinal
          fb x (case1 b) = fun← ab x b
          fb x (case2 d) = fun← cd x d
          fa-isb :  (x : Ordinal) (lt : odef (A ∪ C) x) → odef (B ∪ D) (fa x lt)
          fa-isb x (case1 a) = case1 (funB ab x a)
          fa-isb x (case2 c) = case2 (funB cd x c)
          fb-isa :  (x : Ordinal) (lt : odef (B ∪ D) x) → odef (A ∪ C) (fb x lt)
          fb-isa x (case1 b) = case1 (funA ab x b)
          fb-isa x (case2 d) = case2 (funA cd x d)
          faiso : (x : Ordinal) (lt : odef (B ∪ D) x) → fa (fb x lt) (fb-isa x lt) ≡ x
          faiso x (case1 b) = fiso→ ab x b
          faiso x (case2 d) = fiso→ cd x d
          fbiso : (x : Ordinal) (lt : odef (A ∪ C) x) → fb (fa x lt) (fa-isb x lt) ≡ x
          fbiso x (case1 b) = fiso← ab x b
          fbiso x (case2 d) = fiso← cd x d
          -- without fcong, we don't need nac and nbd
          facong : (x y : Ordinal) (ltx : odef (A ∪ C) x) (lty : odef (A ∪ C) y) → x ≡ y → fa x ltx ≡ fa y lty
          facong x .x (case1 x₁) (case1 x₂) refl = fcong→ ab x x x₁ x₂ refl
          facong x .x (case1 x₁) (case2 x₂) refl = ⊥-elim (¬x<0 (eq→  nac ⟪ x₁ , x₂ ⟫))
          facong x .x (case2 x₁) (case1 x₂) refl = ⊥-elim (¬x<0 (eq→  nac ⟪ x₂ , x₁ ⟫))
          facong x .x (case2 x₁) (case2 x₂) refl = fcong→ cd x x x₁ x₂ refl
          fbcong : (x y : Ordinal) (ltx : odef (B ∪ D) x) (lty : odef (B ∪ D) y) → x ≡ y → fb x ltx ≡ fb y lty
          fbcong x .x (case1 x₁) (case1 x₂) refl = fcong← ab x x x₁ x₂ refl
          fbcong x .x (case1 x₁) (case2 x₂) refl = ⊥-elim (¬x<0 (eq→  nbd ⟪ x₁ , x₂ ⟫))
          fbcong x .x (case2 x₁) (case1 x₂) refl = ⊥-elim (¬x<0 (eq→  nbd ⟪ x₂ , x₁ ⟫))
          fbcong x .x (case2 x₁) (case2 x₂) refl = fcong← cd x x x₁ x₂ refl

--
--  f : A → B        OrdBijection A           (Image A f)
--  g : B → A        OrdBijection (Image B g) B
--                     UC (closure of g ∙ f from ¬ Image B g )
--                         A =   UC ∪ (A \ Image B gi )
--                         B =   (Image B g) UC 
--
Bernstein : {a b : Ordinal } → Injection a b → Injection b a → HODBijection (* a) (* b)
Bernstein {a} {b} ( fi @ record { i→ = f ; iB = b∋f ; inject = f-inject }) 
                  ( gi @ record { i→ = g ; iB = a∋g ; inject = g-inject })
     = proj1 (==-bi (proj2 (==-bi (bi-∪  bi-UC  bi-fUC exUC exfUC ) ) (==-sym b=fUC∨b-fUC)) ) (==-sym a=UC∨a-UC) 
 where
      gf : Injection a a
      gf = record { i→ = λ x → g (f x ) ; iB = λ x ax → a∋g _ (b∋f x ax) 
         ; inject = λ x y ax ay eq → f-inject _ _ ax ay ( g-inject _ _ (b∋f _ ax) (b∋f _ ay) eq) } 

      -- HOD UC is closure of gi ∙ fi starting from a - Image g
      -- and a-UC is the remaining part of a. Both sets have inverse functions.
      --
      -- We cannot directly create h : * a → * b from these functions, because
      -- the choise of UC ∨  a-UC is non constructive and
      -- LEM cannot be used in this non positive context. 
      --
      -- We use the following trick:
      --
      --    bi-UC  : HODBijection UC fUC
      --    bi-fUC : HODBijection a-UC b-fUC
      --
      -- The HODBijection (* a) (* b) is a merge of these bijections.
      -- The merging bi-UC and  bi-fUC uses also LEM but use it positively.
      --
      -- bijection on each side is easy, because these are images of fi and g.
      --    somehow we don't use injection of f.
      --
      --
      data gfImage :  (x : Ordinal) → Set n where
          a-g : {x : Ordinal} → (ax : odef (* a) x ) → (¬ib : ¬ ( IsImage b a gi x )) → gfImage  x
          next-gf : {x : Ordinal} → (ix : IsImage a a gf x) → (gfiy : gfImage (IsImage0.y ix) ) → gfImage  x

      a∋gfImage : {x : Ordinal } → gfImage x → odef (* a) x
      a∋gfImage {x} (a-g ax ¬ib) = ax
      a∋gfImage  {x} (next-gf record { y = y ; ay = ay ; x=fy = x=fy } lt ) = subst (λ k → odef (* a) k ) (sym x=fy) (a∋g _ (b∋f y ay) )

      UC : HOD
      UC = record { od = record { def = λ x → gfImage x } ; odmax = & (* a) ; <odmax = λ lt → odef< (a∋gfImage lt)  }

      a-UC : HOD
      a-UC = record { od = record { def = λ x → odef (* a) x ∧ (¬ gfImage x) } ; odmax = & (* a) 
          ; <odmax = λ lt → odef< (proj1 lt)  }

      a=UC∨a-UC : (* a) =h= (UC ∪ a-UC)
      a=UC∨a-UC = record { eq→ = be00 ; eq← = be01 } where
           be00 : {x : Ordinal} → odef (* a) x → odef (UC ∪ a-UC) x
           be00 {x} ax with p∨¬p ( gfImage x)
           ... | case1 gfx = case1 gfx
           ... | case2 ngfx = case2 ⟪ ax , ngfx ⟫
           be01 : {x : Ordinal} → odef (UC ∪ a-UC) x → odef (* a) x 
           be01 {x} (case1 gfx) = a∋gfImage gfx
           be01 {x} (case2 ngfx) = proj1 ngfx

      exUC : (UC ∩ a-UC) =h= od∅
      exUC = record { eq→ = be00 ; eq← = be01 } where
           be00 : {x : Ordinal} → odef (UC ∩ a-UC) x → odef od∅ x
           be00 {x} ⟪ uc , ⟪ ax , nuc ⟫ ⟫ = ⊥-elim ( nuc uc )
           be01 : {x : Ordinal} → odef od∅ x → odef (UC ∩ a-UC) x
           be01 {x} lt = ⊥-elim ( ¬x<0 lt )

      FA : (x : Ordinal) → (ax : gfImage x) → Ordinal
      FA x ax = f x -- (a∋gfImage ax)

      b∋f⁻¹ : (x : Ordinal) → IsImage0 UC (* b) FA x → odef (* b) x
      b∋f⁻¹ x record { y = y ; ay = ay ; x=fy = x=fy } = subst (λ k → odef (* b) k ) (sym x=fy) (b∋f y (a∋gfImage ay))

      fUC : HOD
      fUC = record { od = record { def = λ x → IsImage0 UC (* b) FA  x } ; odmax = & (* b) ; <odmax = λ {x} lt → odef< (b∋f⁻¹ x lt)} 

      b-fUC : HOD
      b-fUC = record { od = record { def = λ x → odef (* b) x ∧ (¬ IsImage0 UC (* b) FA  x) } ; odmax = & (* b) ; <odmax = λ lt → odef∧< lt  }

      b=fUC∨b-fUC : * b =h= (fUC ∪ b-fUC)
      b=fUC∨b-fUC = record { eq→ = be00 ; eq← = be01 } where
           be00 : {x : Ordinal} → odef (* b) x → odef (fUC ∪ b-fUC) x
           be00 {x} bx with p∨¬p  (IsImage0 UC (* b) FA  x)
           ... | case1 gfx = case1 gfx
           ... | case2 ngfx = case2 ⟪ bx , ngfx ⟫
           be01 : {x : Ordinal} → odef (fUC ∪ b-fUC) x → odef (* b) x 
           be01 {x} (case1 record { y = y ; ay = ay ; x=fy = x=fy }) = subst (λ k → odef (* b) k) (sym x=fy) ( b∋f y (a∋gfImage ay))
           be01 {x} (case2 ngfx) = proj1 ngfx

      exfUC : (fUC ∩ b-fUC) =h= od∅
      exfUC = record { eq→ = be00 ; eq← = be01 } where
           be00 : {x : Ordinal} → odef (fUC ∩ b-fUC) x → odef od∅ x
           be00 {x} ⟪ uc , ⟪ ax , nuc ⟫ ⟫ = ⊥-elim ( nuc uc )
           be01 : {x : Ordinal} → odef od∅ x → odef (fUC ∩ b-fUC) x
           be01 {x} lt = ⊥-elim ( ¬x<0 lt )

      nimg : {x : Ordinal } → (ax : odef (* a) x ) → ¬ (odef UC x) → IsImage b a gi x
      nimg {x} ax ncn with p∨¬p  (IsImage b a gi x)
      ... | case1 img = img
      ... | case2 nimg = ⊥-elim ( ncn (a-g ax nimg ) )

      -- f-cong : {x y : Ordinal } → {ax : odef (* a) x} {ax1 : odef (* a) y}  → x ≡ y  → f x ≡ f y 
      -- f-cong {x} {x} {ax} {ax1} refl = refl 

      -- g-cong : {x y : Ordinal } → {bx : odef (* b) x} {bx1 : odef (* b) y}  → x ≡ y  → g x ≡ g y 
      -- g-cong {x} {x} {bx} {bx1} refl = refl 

      g⁻¹ : {x : Ordinal } → (ax : odef (* a) x) → (nc0 : IsImage b a gi x ) → Ordinal
      g⁻¹ {x} ax record { y = y ; ay = ay ; x=fy = x=fy } = y

      b∋g⁻¹ : {x : Ordinal } → (ax : odef (* a) x) (nc0 : IsImage b a gi x ) → odef (* b) (g⁻¹ ax nc0)
      b∋g⁻¹ {x} ax record { y = y ; ay = ay ; x=fy = x=fy } = ay

      g⁻¹-iso : {x : Ordinal } → (ax : odef (* a) x) → (nc0 : IsImage b a gi x ) → g (g⁻¹ ax nc0)  ≡ x
      g⁻¹-iso {x} ax record { y = y ; ay = ay ; x=fy = x=fy } = sym x=fy

      g⁻¹-iso1 : {x : Ordinal } → (bx : odef (* b) x) → (nc0 : IsImage b a gi (g x ) )  → g⁻¹ (a∋g x bx) nc0  ≡ x
      g⁻¹-iso1 {x} bx nc0 = inject gi _ _ (b∋g⁻¹ (a∋g x bx) nc0) bx (g⁻¹-iso (a∋g x bx) nc0) 

      g⁻¹-eq : {x : Ordinal } → (ax ax' : odef (* a) x) → {nc0 nc0' : IsImage b a gi x } → g⁻¹ ax nc0 ≡ g⁻¹ ax' nc0'
      g⁻¹-eq {x} ax ax' {record { y = y₁ ; ay = ay₁ ; x=fy = x=fy₁ }} {record { y = y ; ay = ay ; x=fy = x=fy }} 
           = inject gi _ _ ay₁ ay (trans (sym x=fy₁) x=fy )

      cc11-case2 : {x : Ordinal} (ax : odef (* a) x) 
          → (ncn : ¬ gfImage x) 
          → ¬ IsImage0 UC (* b) (λ x ax → f x )  (g⁻¹ ax (nimg ax ncn))
      cc11-case2 {x} ax ncn record { y = y ; ay = ay ; x=fy = x=fy } with nimg ax ncn
      ... | record { y = y1 ; ay = ay1 ; x=fy = x=fy1 } = ncn ( subst (λ k → gfImage k) be113 
                                            (next-gf record { y = y ; ay = (a∋gfImage ay) ; x=fy = refl } ay ) )  where
               be113 : g (f y )  ≡ x
               be113 = begin
                    g (f y )  ≡⟨ cong g (sym x=fy)  ⟩
                    g y1 ≡⟨ sym (x=fy1) ⟩
                    x ∎ where open ≡-Reasoning

      cc10-case2 : {x : Ordinal } → (bx : odef (* b) x )
         → ¬ IsImage0 UC (* b) (λ x ax → f x )  x
         → ¬ gfImage (g x )
      cc10-case2 {x} bx nix (a-g ax ¬ib) = ¬ib record { y = _ ; ay = bx ; x=fy = refl }
      cc10-case2 {x} bx nix (next-gf record { y = y ; ay = ay ; x=fy = x=fy } gfy) 
           = nix record { y = _ ; ay = gfy ; x=fy = inject gi _ _ bx (b∋f y (a∋gfImage gfy)) (trans x=fy (cong g (cong f refl))) }

      fU1 : (x : Ordinal) → odef UC x → Ordinal
      fU1 x gfx = f x 

      f⁻¹ : (x : Ordinal) → IsImage0 UC (* b) FA x → Ordinal
      f⁻¹ x record { y = y ; ay = ay ; x=fy = x=fy } = y

      UC∋f⁻¹ : {x : Ordinal } → (lt : odef fUC x) → odef UC (f⁻¹ x lt )
      UC∋f⁻¹ {x} record { y = y ; ay = ay ; x=fy = x=fy } = ay

      fU-iso1 : {x : Ordinal } → (lt : odef fUC x) → fU1 (f⁻¹ x lt) (UC∋f⁻¹ lt) ≡ x
      fU-iso1 {x} record { y = y ; ay = (a-g ax ¬ib) ; x=fy = x=fy } = sym x=fy
      fU-iso1 {x} record { y = y ; ay = (next-gf record { y = y₁ ; ay = ay₁ ; x=fy = x=fy₁ } ay) ; x=fy = x=fy } = sym x=fy

      fU-iso0 : {x : Ordinal } → (lt : odef UC x) → f⁻¹ (fU1 x lt) record { y = _ ; ay = lt ; x=fy = refl } ≡ x
      fU-iso0 {x} (a-g ax ¬ib) = refl 
      fU-iso0 {x} (next-gf record { y = y ; ay = ay ; x=fy = x=fy } lt) = refl

      f⁻¹-cong : (x y : Ordinal) → (isx : IsImage0 UC (* b) FA x) → (isy : IsImage0 UC (* b) FA y) → x ≡ y → f⁻¹ x isx ≡ f⁻¹ y isy
      f⁻¹-cong x y isx@record { y = yx ; ay = ayx ; x=fy = x=fyx } isy@record { y = yy ; ay = ay ; x=fy = x=fy } eq = inject fi _ _ f01 f02 f00 where
          f01 : odef (* a) (f⁻¹ x isx)
          f01 = a∋gfImage (UC∋f⁻¹ isx)
          f02 : odef (* a) (f⁻¹ y isy)
          f02 = a∋gfImage (UC∋f⁻¹ isy)
          f00 : f (f⁻¹ x isx) ≡ f (f⁻¹ y isy)  
          f00 = trans ( fU-iso1 isx) (trans eq (sym (fU-iso1 isy)))

      bi-UC : HODBijection UC fUC
      bi-UC = record { 
         fun→  = λ x lt → f x 
       ; fun←  = λ x lt → f⁻¹ x lt
       ; funB  = λ x lt → record { y = _ ; ay = lt  ; x=fy = refl }
       ; funA  = λ x lt → UC∋f⁻¹ lt
       ; fiso→ = λ x lt → fU-iso1 lt
       ; fiso← = λ x lt → fU-iso0 lt
       ; fcong→ = λ x y ax ay eq → cong f eq
       ; fcong← = λ x y ax ay eq → f⁻¹-cong x y ax ay eq
       }

      b-FUC∋g⁻¹ : {x : Ordinal } → (lt : odef a-UC x )→ odef b-fUC (g⁻¹ (proj1 lt) (nimg (proj1 lt) (proj2 lt))) 
      b-FUC∋g⁻¹ {x} ⟪ ax , ngfix ⟫ = ⟪ b∋g⁻¹ ax (nimg ax ngfix) , cc11-case2 ax ngfix  ⟫

      a-UC∋g : {x : Ordinal } → (lt : odef b-fUC x) → odef a-UC (g x )
      a-UC∋g {x} ⟪ bx , ¬img ⟫ = ⟪ a∋g x bx , cc10-case2 bx ¬img ⟫

      fUC-iso1 : {x : Ordinal } → (lt : odef b-fUC x ) → g⁻¹ (proj1 (a-UC∋g lt)) (nimg (proj1 (a-UC∋g lt)) (proj2 (a-UC∋g lt))) ≡ x
      fUC-iso1 {x} lt with nimg (proj1 (a-UC∋g lt)) (proj2 (a-UC∋g lt))
      ... | record { y = y ; ay = ay ; x=fy = x=fy } = sym ( inject gi _ _ (proj1 lt) ay x=fy )

      fUC-iso0 : {x : Ordinal} → (lt : odef a-UC x) →  g (g⁻¹ (proj1 lt) (nimg (proj1 lt) (proj2 lt)))  ≡ x
      fUC-iso0 {x} lt with nimg (proj1 lt) (proj2 lt)
      ... | record { y = y ; ay = ay ; x=fy = x=fy } = sym x=fy

      g⁻¹-cong : (x y : Ordinal) → (ax : odef a-UC x) ( ay : odef a-UC y) 
          → x ≡ y
          → g⁻¹ (proj1 ax) (nimg (proj1 ax) (proj2 ax)) ≡ g⁻¹ (proj1 ay) (nimg (proj1 ay) (proj2 ay))
      g⁻¹-cong x y ax ay eq = inject gi _ _ ( b∋g⁻¹ (proj1 ax) (nimg (proj1 ax) (proj2 ax))) ( b∋g⁻¹ (proj1 ay) (nimg (proj1 ay) (proj2 ay))) g00 where
          g00 : g (g⁻¹ (proj1 ax) (nimg (proj1 ax) (proj2 ax))) ≡ g (g⁻¹ (proj1 ay) (nimg (proj1 ay) (proj2 ay)))
          g00 = trans (fUC-iso0 ax) ( trans eq (sym (fUC-iso0 ay)))

      bi-fUC : HODBijection a-UC b-fUC
      bi-fUC = record { 
         fun→  = λ x lt → g⁻¹ (proj1 lt) (nimg (proj1 lt) (proj2 lt))
       ; fun←  = λ x lt → g x 
       ; funB  = λ x lt → b-FUC∋g⁻¹  lt
       ; funA  = λ x lt → a-UC∋g lt
       ; fiso→ = λ x lt → fUC-iso1 lt
       ; fiso← = λ x lt → fUC-iso0 lt
       ; fcong→ = λ x y ax ay eq → g⁻¹-cong x y ax ay eq
       ; fcong← = λ x y ax ay eq → cong g eq
       }


_c<_ : ( A B : HOD ) → Set n
A c< B = ¬ ( Injection (& B)  (& A) )

record Cardinal (a : Ordinal ) : Set (Level.suc n) where
   field
       card : Ordinal
       ciso : HODBijection (* a) (* card)
       cmax : (x : Ordinal) → card o< x → ¬ HODBijection (* a) (* x)

-- Cardinal∈ : { s : HOD } → { t : Ordinal } → Ord t ∋ s →   s c< Ord t
-- Cardinal∈ = {!!}

-- Cardinal⊆ : { s t : HOD } → s ⊆ t →  ( s c< t ) ∨ ( s =c= t ) -- this is not valid
-- Cardinal⊆ = {!!}                                              -- we may have infinite sets with the same cardinality

PtoF : {u : HOD} {x s : Ordinal } → odef (Power u) s → odef u x → Bool
PtoF {u} {x} {s} su ux with p∨¬p (odef (* s) x )
... | case1 a = true
... | case2 b = false

fun←cong : {P S : HOD} (b : HODBijection P S ) {x y : Ordinal } → {ax : odef S x} {ax1 : odef S y}  
    → x ≡ y  → fun← b x ax ≡ fun← b y ax1
fun←cong {P} {S} b {x} {x} {ax} {ax1} refl = fcong← b x x ax ax1 refl
     
fun→cong : {P S : HOD} (b : HODBijection P S ) {x y : Ordinal } → {ax : odef P x} {ax1 : odef P y}  
    → x ≡ y  → fun→ b x ax ≡ fun→ b y ax1
fun→cong {P} {S} b {x} {x} {ax} {ax1} refl = fcong→ b x x ax ax1 refl
     

--    S
--    t ⊆ S    ( Power S ∋ t )
--    S   s₀    s₁      ...  sn
--    t   true  false   ...  false
---
Cantor1 : ( S : HOD ) → S c< Power S
Cantor1 S f = diag4 where 
     f1 : Injection (& S) (& (Power S))
     f1 = record { i→ = λ x → & (* x , * x) ; iB = c00 ;  inject = c02 }where
         c02 : (x y : Ordinal) (ltx : odef (* (& S)) x) (lty : odef (* (& S)) y) →
            & (* x , * x) ≡ & (* y , * y) → x ≡ y
         c02 x y ltx lty eq = subst₂ (λ j k → j ≡ k ) &iso &iso (==→o≡ (xx=zy→x=y c03 )) where
             c03 : (* x , * x) =h= (* y , * y)
             c03 = ord→== eq
         c00 : (x : Ordinal) (lt : odef (* (& S)) x) → odef (* (& (Power S))) (& (* x , * x))
         c00 x lt  = eq← *iso (λ y lt → c01 y (eq→ *iso lt) ) where
             c01 : (y : Ordinal ) → odef (* x , * x ) y  → odef S y
             c01 y (case1 eq) = eq→ *iso (subst (λ k  → odef (* (& S)) k ) (trans (sym &iso) (sym eq) ) lt)
             c01 y (case2 eq) = eq→ *iso (subst (λ k  → odef (* (& S)) k ) (trans (sym &iso) (sym eq) ) lt)
     f2 : Injection (& (Power S)) (& S) 
     f2 = f
     -- postulate   -- yes we have a proof but it is very slow
     b : HODBijection (Power S) S 
     b = proj1 (==-bi (proj2 (==-bi ( Bernstein f2 f1) ) *iso ) ) *iso
     -- -- subst₂ (λ j k → HODBijection j k) ? ? ( Bernstein f2 f1)   -- this makes check very slow
     --      but postulate makes check weak eg. irrerevance of ∋ 

     -- we have at least one element since Power S contains od∅
     --

     p0 : odef (Power S) o∅
     p0 = Power∋∅  {S}

     s : Ordinal 
     s = fun→ b o∅ p0

     ss : odef S s
     ss = funB b o∅ p0

     is-S : (S : HOD) → (x : Ordinal ) →  Bool
     is-S S x with p∨¬p (odef S x )
     ... | case1 _ = true
     ... | case2 _ = false

     diag : {x : Ordinal} → (sx : odef S x) → Bool 
     diag {x} sx = is-S (* (fun← b x sx)) x

     Diag : HOD
     Diag = record { od = record { def = λ x → odef S x ∧ ((sx : odef S x) → diag sx ≡ false) } 
         ; odmax = & S ; <odmax = odef∧< } 

     diag3 : odef (Power S) (& Diag)
     diag3 z xz with eq→ *iso xz
     ... | ⟪ sx , eq ⟫ = sx

     not-isD : (x : Ordinal) → (sn : odef S x)  → not (  is-S (* (fun← b x sn )) x ) ≡ is-S Diag x
     not-isD x sn with  p∨¬p (odef (* (fun← b x sn )) x)  | p∨¬p (odef Diag x) | (is-S (* (fun← b x sn ))) x in eq1
     ... | case1 lt | case1 ⟪ sx , eq ⟫ | true  =  ⊥-elim ( ¬-bool {diag sx} ni00 ni01)  where
           ni00 : diag sx ≡ false
           ni00 = eq sx
           ni01 : diag sx ≡ true
           ni01 with p∨¬p (odef (* (fun← b x sx)) x)
           ... | case1 eq1 = refl
           ... | case2 ne = ⊥-elim (ne (subst (λ k → odef (* k) x) ni02 lt) ) where
              ni02 : fun← b x sn ≡ fun← b x sx
              ni02 = fcong← b _ _ sn sx refl
     ... | case1 lt | case2 lt1 | p1 = subst (λ k → not k ≡ false ) eq1 refl
     ... | case2 lt | case1 lt1 | p1 = subst (λ k → not k ≡ true ) eq1 refl
     ... | case2 lt | case2 neg | false = ⊥-elim (neg ⟪ sn , (λ sx → ni00 sx ) ⟫) where
           ni00 : (sx : odef S x ) → diag sx ≡ false
           ni00 sx with p∨¬p (odef (* (fun← b x sx)) x)
           ... | case1 dx = ⊥-elim ( lt (subst (λ k → odef (* k) x) ni02 dx) ) where
              ni03 : odef (* (fun← b x sx)) x
              ni03 = dx
              ni02 : fun← b x sx ≡ fun← b x sn
              ni02 = sym (fcong← b _ _ sn sx refl)
           ... | case2 ndx = refl

     is-S-congS : (S S1 : HOD ) → (x : Ordinal) → S =h= S1 →  is-S S x ≡ is-S S1 x
     is-S-congS S S1 x eq with p∨¬p (odef S x) | p∨¬p (odef S1 x)
     ... | case1 sx | case1 sx1 = refl
     ... | case2 sx | case2 sx1 = refl
     ... | case1 sx | case2 sx1 = ⊥-elim ( sx1 (eq→ eq sx) )
     ... | case2 sx | case1 sx1 = ⊥-elim ( sx (eq← eq sx1) )

     diagn1 : (n : Ordinal ) → odef S n → ¬ (fun→ b (& Diag) diag3 ≡ n)
     diagn1 n sn dn = ¬t=f (is-S Diag n) (begin
          not (is-S Diag n)
        ≡⟨ cong (λ k → not k) (is-S-congS Diag (* (& Diag)) _ (==-sym *iso) ) ⟩
          not (is-S (* (& Diag)) n)
        ≡⟨ cong (λ k → not (is-S (* k) n)) (sym (fiso← b (& Diag) diag3 )) ⟩
          not (  is-S (* (fun← b (fun→ b (& Diag) diag3) (funB b (& Diag) diag3 ))) n ) 
        ≡⟨ cong (λ k → not (is-S (* k) n)) ( fun←cong b {_} {_} {funB b _ diag3} {sn} dn )   ⟩
          not (  is-S (* (fun← b n sn )) n ) 
        ≡⟨ not-isD _ sn  ⟩
          is-S Diag n
        ∎ ) where 
          open ≡-Reasoning
 
     diag4 : ⊥ 
     diag4 = diagn1  (fun→ b (& Diag) diag3) (funB b (& Diag) diag3) refl
 
c<¬= : { u s : HOD } →  u c< s → ¬ ( u =c=  s )
c<¬= {u} {s} c<u ceq = c<u record { i→ = λ x  → cf x
     ; iB = c00
     ; inject = c01 } where
         cf : (x : Ordinal ) → Ordinal
         cf x with p∨¬p (odef s x)
         ... | case1 sx = fun← ceq x sx 
         ... | case2 nsx = o∅
         c00 : (x : Ordinal) → odef (* (& s)) x → odef (* (& u)) (cf x)
         c00 x sx  with p∨¬p (odef s x)
         ... | case1 sx = eq← *iso (funA ceq x sx )
         ... | case2 nsx = ⊥-elim (nsx (eq→ *iso sx))
         c01 : (x y : Ordinal) → odef (* (& s)) x → odef (* (& s)) y → cf x ≡ cf y → x ≡ y
         c01 x y ssx ssy cfeq with p∨¬p (odef s x) | p∨¬p (odef s y)
         ... | case2 nsx | case1 sy = ⊥-elim (nsx (eq→ *iso ssx))
         ... | case1 sx | case2 nsy = ⊥-elim (nsy (eq→ *iso ssy))
         ... | case2 nsx | case2 nsy = ⊥-elim (nsx (eq→ *iso ssx))
         ... | case1 sx | case1 sy = begin
                x ≡⟨ sym ( fiso→ ceq x c05 ) ⟩
                fun→ ceq ( fun← ceq x c05 ) (funA ceq x c05)  ≡⟨ fcong→  ceq _ _ (funA ceq _ c05 ) (funA ceq _ c06 ) ( begin
                   fun← ceq x c05 ≡⟨ fcong← ceq x x c05 sx refl ⟩
                   fun← ceq x sx ≡⟨ cfeq ⟩
                   fun← ceq y sy ≡⟨ fcong← ceq y y sy c06 refl ⟩
                   fun← ceq y c06  ∎ ) ⟩
                fun→ ceq ( fun← ceq y c06 ) (funA ceq y c06)  ≡⟨ fiso→ ceq y c06 ⟩
                y ∎ where 
                  open ≡-Reasoning
                  c05 : odef s x
                  c05 = eq→ *iso ssx
                  c06 : odef s y
                  c06 = eq→ *iso ssy

Cantor2 : (u : HOD) → ¬ ( u =c=  Power u )
Cantor2 u =  c<¬= (Cantor1 u )




