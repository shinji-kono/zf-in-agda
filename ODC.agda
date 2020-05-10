open import Level
open import Ordinals
module ODC {n : Level } (O : Ordinals {n} ) where

open import zf
open import Data.Nat renaming ( zero to Zero ; suc to Suc ;  ℕ to Nat ; _⊔_ to _n⊔_ ) 
open import  Relation.Binary.PropositionalEquality
open import Data.Nat.Properties 
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.Core

open import logic
open import nat
import OD

open inOrdinal O
open OD O
open OD.OD
open OD._==_
open ODAxiom odAxiom

postulate      
  -- mimimul and x∋minimal is an Axiom of choice
  minimal : (x : OD  ) → ¬ (x == od∅ )→ OD 
  -- this should be ¬ (x == od∅ )→ ∃ ox → x ∋ Ord ox  ( minimum of x )
  x∋minimal : (x : OD  ) → ( ne : ¬ (x == od∅ ) ) → def x ( od→ord ( minimal x ne ) )
  -- minimality (may proved by ε-induction )
  minimal-1 : (x : OD  ) → ( ne : ¬ (x == od∅ ) ) → (y : OD ) → ¬ ( def (minimal x ne) (od→ord y)) ∧ (def x (od→ord  y) )


--
-- Axiom of choice in intutionistic logic implies the exclude middle
--     https://plato.stanford.edu/entries/axiom-choice/#AxiChoLog
--

ppp :  { p : Set n } { a : OD  } → record { def = λ x → p } ∋ a → p
ppp  {p} {a} d = d

p∨¬p : ( p : Set n ) → p ∨ ( ¬ p )         -- assuming axiom of choice
p∨¬p  p with is-o∅ ( od→ord ( record { def = λ x → p } ))
p∨¬p  p | yes eq = case2 (¬p eq) where
   ps = record { def = λ x → p }
   lemma : ps == od∅ → p → ⊥
   lemma eq p0 = ¬x<0  {od→ord ps} (eq→ eq p0 )
   ¬p : (od→ord ps ≡ o∅) → p → ⊥
   ¬p eq = lemma ( subst₂ (λ j k → j ==  k ) oiso o∅≡od∅ ( o≡→== eq ))
p∨¬p  p | no ¬p = case1 (ppp  {p} {minimal ps (λ eq →  ¬p (eqo∅ eq))} lemma) where
   ps = record { def = λ x → p }
   eqo∅ : ps ==  od∅  → od→ord ps ≡  o∅  
   eqo∅ eq = subst (λ k → od→ord ps ≡ k) ord-od∅ ( cong (λ k → od→ord k ) (==→o≡ eq)) 
   lemma : ps ∋ minimal ps (λ eq →  ¬p (eqo∅ eq)) 
   lemma = x∋minimal ps (λ eq →  ¬p (eqo∅ eq))

decp : ( p : Set n ) → Dec p   -- assuming axiom of choice    
decp  p with p∨¬p p
decp  p | case1 x = yes x
decp  p | case2 x = no x

double-neg-eilm : {A : Set n} → ¬ ¬ A → A      -- we don't have this in intutionistic logic
double-neg-eilm  {A} notnot with decp  A                         -- assuming axiom of choice
... | yes p = p
... | no ¬p = ⊥-elim ( notnot ¬p )

OrdP : ( x : Ordinal  ) ( y : OD  ) → Dec ( Ord x ∋ y )
OrdP  x y with trio< x (od→ord y)
OrdP  x y | tri< a ¬b ¬c = no ¬c
OrdP  x y | tri≈ ¬a refl ¬c = no ( o<¬≡ refl )
OrdP  x y | tri> ¬a ¬b c = yes c

open import zfc

OD→ZFC : ZFC
OD→ZFC   = record { 
    ZFSet = OD 
    ; _∋_ = _∋_ 
    ; _≈_ = _==_ 
    ; ∅  = od∅
    ; Select = Select
    ; isZFC = isZFC
 } where
    -- infixr  200 _∈_
    -- infixr  230 _∩_ _∪_
    isZFC : IsZFC (OD )  _∋_  _==_ od∅ Select 
    isZFC = record {
       choice-func = choice-func ;
       choice = choice
     } where
         -- Axiom of choice ( is equivalent to the existence of minimal in our case )
         -- ∀ X [ ∅ ∉ X → (∃ f : X → ⋃ X ) → ∀ A ∈ X ( f ( A ) ∈ A ) ] 
         choice-func : (X : OD  ) → {x : OD } → ¬ ( x == od∅ ) → ( X ∋ x ) → OD
         choice-func X {x} not X∋x = minimal x not
         choice : (X : OD  ) → {A : OD } → ( X∋A : X ∋ A ) → (not : ¬ ( A == od∅ )) → A ∋ choice-func X not X∋A 
         choice X {A} X∋A not = x∋minimal A not

