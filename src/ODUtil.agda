{-# OPTIONS --allow-unsolved-metas #-} 
open import Level
open import Ordinals
module ODUtil {n : Level } (O : Ordinals {n} ) where

open import zf
open import Data.Nat renaming ( zero to Zero ; suc to Suc ;  ℕ to Nat ; _⊔_ to _n⊔_ ) 
open import  Relation.Binary.PropositionalEquality hiding ( [_] )
open import Data.Nat.Properties 
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary hiding ( _⇔_ )

open import logic
open import nat

open Ordinals.Ordinals  O
open Ordinals.IsOrdinals isOrdinal
open Ordinals.IsNext isNext
import OrdUtil
open OrdUtil O

import OD
open OD O
open OD.OD
open ODAxiom odAxiom

open HOD
open _⊆_
open _∧_
open _==_

cseq :  HOD  →  HOD 
cseq x = record { od = record { def = λ y → odef x (osuc y) } ; odmax = osuc (odmax x) ; <odmax = lemma } where
    lemma : {y : Ordinal} → def (od x) (osuc y) → y o< osuc (odmax x)
    lemma {y} lt = ordtrans <-osuc (ordtrans (<odmax x lt) <-osuc ) 


pair-xx<xy : {x y : HOD} → & (x , x) o< osuc (& (x , y) )
pair-xx<xy {x} {y} = ⊆→o≤  lemma where
   lemma : {z : Ordinal} → def (od (x , x)) z → def (od (x , y)) z
   lemma {z} (case1 refl) = case1 refl
   lemma {z} (case2 refl) = case1 refl

pair-<xy : {x y : HOD} → {n : Ordinal}  → & x o< next n →  & y o< next n  → & (x , y) o< next n
pair-<xy {x} {y} {o} x<nn y<nn with trio< (& x) (& y) | inspect (omax (& x)) (& y)
... | tri< a ¬b ¬c | record { eq = eq1 } = next< (subst (λ k → k o< next o ) (sym eq1) (osuc<nx y<nn)) ho< 
... | tri> ¬a ¬b c | record { eq = eq1 } = next< (subst (λ k → k o< next o ) (sym eq1) (osuc<nx x<nn)) ho< 
... | tri≈ ¬a b ¬c | record { eq = eq1 } = next< (subst (λ k → k o< next o ) (omax≡ _ _ b) (subst (λ k → osuc k o< next o) b (osuc<nx x<nn))) ho< 

--  another form of infinite
-- pair-ord< :  {x : Ordinal } → Set n
pair-ord< : {x : HOD } → ( {y : HOD } → & y o< next (odmax y) ) → & ( x , x ) o< next (& x)
pair-ord< {x} ho< = subst (λ k → & (x , x) o< k ) lemmab0 lemmab1  where
       lemmab0 : next (odmax (x , x)) ≡ next (& x)
       lemmab0 = trans (cong (λ k → next k) (omxx _)) (sym nexto≡)
       lemmab1 : & (x , x) o< next ( odmax (x , x))
       lemmab1 = ho<

trans-⊆ :  { A B C : HOD} → A ⊆ B → B ⊆ C → A ⊆ C
trans-⊆ A⊆B B⊆C = record { incl = λ x → incl B⊆C (incl A⊆B x) }

refl-⊆ : {A : HOD} → A ⊆ A
refl-⊆ {A} = record { incl = λ x → x }

od⊆→o≤  : {x y : HOD } → x ⊆ y → & x o< osuc (& y)
od⊆→o≤ {x} {y} lt  =  ⊆→o≤ {x} {y} (λ {z} x>z  → subst (λ k → def (od y) k ) &iso (incl lt (d→∋ x x>z)))

⊆→= : {F U : HOD} → F ⊆ U  → U ⊆ F → F =h= U
⊆→= {F} {U} FU UF = record { eq→ = λ {x} lt → subst (λ k → odef U k) &iso (incl FU (subst (λ k → odef F k) (sym &iso) lt) )
                                     ; eq← = λ {x} lt → subst (λ k → odef F k) &iso (incl UF (subst (λ k → odef U k) (sym &iso) lt) ) }

¬A∋x→A≡od∅ : (A : HOD) → {x : HOD} → A ∋ x  → ¬ ( & A ≡ o∅ )
¬A∋x→A≡od∅ A {x} ax a=0 = ¬x<0 ( subst (λ k → & x o< k) a=0 (c<→o< ax ))

subset-lemma : {A x : HOD  } → ( {y : HOD } →  x ∋ y → (A ∩ x ) ∋  y ) ⇔  ( x ⊆ A  )
subset-lemma  {A} {x} = record {
      proj1 = λ lt  → record { incl = λ x∋z → proj1 (lt x∋z)  }
    ; proj2 = λ x⊆A lt → ⟪ incl x⊆A lt , lt ⟫
   } 

ω<next-o∅ : {y : Ordinal} → infinite-d y → y o< next o∅
ω<next-o∅ {y} lt = <odmax infinite lt

nat→ω : Nat → HOD
nat→ω Zero = od∅
nat→ω (Suc y) = Union (nat→ω y , (nat→ω y , nat→ω y)) 

ω→nato : {y : Ordinal} → infinite-d y → Nat
ω→nato iφ = Zero
ω→nato (isuc lt) = Suc (ω→nato lt)

ω→nat : (n : HOD) → infinite ∋ n → Nat
ω→nat n = ω→nato 

ω∋nat→ω : {n : Nat} → def (od infinite) (& (nat→ω n))
ω∋nat→ω {Zero} = subst (λ k → def (od infinite) k) (sym ord-od∅) iφ
ω∋nat→ω {Suc n} = subst (λ k → def (od infinite) k) lemma (isuc ( ω∋nat→ω {n})) where
    lemma :  & (Union (* (& (nat→ω n)) , (* (& (nat→ω n)) , * (& (nat→ω n))))) ≡ & (nat→ω (Suc n))
    lemma = subst (λ k → & (Union (k , ( k , k ))) ≡ & (nat→ω (Suc n))) (sym *iso) refl

pair1 : { x y  : HOD  } →  (x , y ) ∋ x
pair1 = case1 refl

pair2 : { x y  : HOD  } →  (x , y ) ∋ y
pair2 = case2 refl

single : {x y : HOD } → (x , x ) ∋ y → x ≡ y
single (case1 eq) = ==→o≡ ( ord→== (sym eq) )
single (case2 eq) = ==→o≡ ( ord→== (sym eq) )

open import Relation.Binary.HeterogeneousEquality as HE using (_≅_ ) 
-- postulate f-extensionality : { n m : Level}  → HE.Extensionality n m

ω-prev-eq1 : {x y : Ordinal} →  & (Union (* y , (* y , * y))) ≡ & (Union (* x , (* x , * x))) → ¬ (x o< y)
ω-prev-eq1 {x} {y} eq x<y = eq→ (ord→== eq) {& (* y)} (λ not2 → not2 (& (* y , * y))
      ⟪ case2 refl , subst (λ k → odef k (& (* y))) (sym *iso) (case1 refl)⟫ ) (λ u → lemma u ) where
   lemma : (u : Ordinal) → ¬ def (od (* x , (* x , * x))) u ∧ def (od (* u)) (& (* y))
   lemma u t with proj1 t
   lemma u t | case1 u=x = o<> (c<→o< {* y} {* u} (proj2 t)) (subst₂ (λ j k → j o< k )
        (trans (sym &iso) (trans (sym u=x) (sym &iso)) ) (sym &iso) x<y ) -- x ≡ & (* u)
   lemma u t | case2 u=xx = o<¬≡ (lemma1 (subst (λ k → odef k (& (* y)) ) (trans (cong (λ k → * k ) u=xx) *iso )  (proj2 t))) x<y where
       lemma1 : {x y : Ordinal } → (* x , * x ) ∋ * y → x ≡ y    --  y = x ∈ ( x , x ) = u 
       lemma1 (case1 eq) = subst₂ (λ j k → j ≡ k ) &iso &iso (sym eq)
       lemma1 (case2 eq) = subst₂ (λ j k → j ≡ k ) &iso &iso (sym eq)

ω-prev-eq : {x y : Ordinal} →  & (Union (* y , (* y , * y))) ≡ & (Union (* x , (* x , * x))) → x ≡ y
ω-prev-eq {x} {y} eq with trio< x y
ω-prev-eq {x} {y} eq | tri< a ¬b ¬c = ⊥-elim (ω-prev-eq1 eq a)
ω-prev-eq {x} {y} eq | tri≈ ¬a b ¬c = b
ω-prev-eq {x} {y} eq | tri> ¬a ¬b c = ⊥-elim (ω-prev-eq1 (sym eq) c)

ω-∈s : (x : HOD) →  Union ( x , (x , x)) ∋ x
ω-∈s x not = not (& (x , x)) ⟪ case2 refl , subst (λ k → odef k (& x) ) (sym *iso) (case1 refl) ⟫

ωs≠0 : (x : HOD) →  ¬ ( Union ( x , (x , x)) ≡ od∅ )
ωs≠0 y eq =  ⊥-elim ( ¬x<0 (subst (λ k → & y  o< k ) ord-od∅ (c<→o< (subst (λ k → odef k (& y )) eq (ω-∈s y) ))) )

nat→ω-iso : {i : HOD} → (lt : infinite ∋ i ) → nat→ω ( ω→nat i lt ) ≡ i
nat→ω-iso {i} = ε-induction {λ i →  (lt : infinite ∋ i ) → nat→ω ( ω→nat i lt ) ≡ i  } ind i where
     ind : {x : HOD} → ({y : HOD} → x ∋ y → (lt : infinite ∋ y) → nat→ω (ω→nat y lt) ≡ y) →
                                            (lt : infinite ∋ x) → nat→ω (ω→nat x lt) ≡ x
     ind {x} prev lt = ind1 lt *iso where
         ind1 : {ox : Ordinal } → (ltd : infinite-d ox ) → * ox ≡ x → nat→ω (ω→nato ltd) ≡ x
         ind1 {o∅} iφ refl = sym o∅≡od∅
         ind1 (isuc {x₁} ltd) ox=x = begin
              nat→ω (ω→nato (isuc ltd) )         
           ≡⟨⟩
              Union (nat→ω (ω→nato ltd) , (nat→ω (ω→nato ltd) , nat→ω (ω→nato ltd)))
           ≡⟨ cong (λ k → Union (k , (k , k ))) lemma  ⟩
              Union (* x₁ , (* x₁ , * x₁))
           ≡⟨ trans ( sym *iso) ox=x ⟩
              x 
           ∎ where
               open ≡-Reasoning 
               lemma0 :  x ∋ * x₁
               lemma0 = subst (λ k → odef k (& (* x₁))) (trans (sym *iso) ox=x) (λ not → not 
                  (& (* x₁ , * x₁))  ⟪ pair2 , subst (λ k → odef k (& (* x₁))) (sym *iso) pair1 ⟫ )
               lemma1 : infinite ∋ * x₁
               lemma1 = subst (λ k → odef infinite k) (sym &iso) ltd
               lemma3 : {x y : Ordinal} → (ltd : infinite-d x ) (ltd1 : infinite-d y ) → y ≡ x → ltd ≅ ltd1
               lemma3 iφ iφ refl = HE.refl
               lemma3 iφ (isuc {y} ltd1) eq = ⊥-elim ( ¬x<0 (subst₂ (λ j k → j o< k ) &iso eq (c<→o< (ω-∈s (* y)) )))
               lemma3 (isuc {y} ltd)  iφ eq = ⊥-elim ( ¬x<0 (subst₂ (λ j k → j o< k ) &iso (sym eq) (c<→o< (ω-∈s (* y)) )))
               lemma3 (isuc {x} ltd) (isuc {y} ltd1) eq with lemma3 ltd ltd1 (ω-prev-eq (sym eq))
               ... | t = HE.cong₂ (λ j k → isuc {j} k ) (HE.≡-to-≅  (ω-prev-eq eq)) t  
               lemma2 : {x y : Ordinal} → (ltd : infinite-d x ) (ltd1 : infinite-d y ) → y ≡ x → ω→nato ltd ≡ ω→nato ltd1
               lemma2 {x} {y} ltd ltd1 eq = lemma6 eq (lemma3 {x} {y} ltd ltd1 eq)  where
                   lemma6 : {x y : Ordinal} → {ltd : infinite-d x } {ltd1 : infinite-d y } → y ≡ x → ltd ≅ ltd1 → ω→nato ltd ≡ ω→nato ltd1
                   lemma6 refl HE.refl = refl
               lemma :  nat→ω (ω→nato ltd) ≡ * x₁
               lemma = trans  (cong (λ k →  nat→ω  k) (lemma2 {x₁} {_} ltd (subst (λ k → infinite-d k ) (sym &iso) ltd)  &iso ) ) ( prev {* x₁} lemma0 lemma1 )

ω→nat-iso : {i : Nat} → ω→nat ( nat→ω i ) (ω∋nat→ω {i}) ≡ i
ω→nat-iso {i} = lemma i (ω∋nat→ω {i}) *iso where
   lemma : {x : Ordinal } → ( i : Nat ) → (ltd : infinite-d x ) → * x ≡  nat→ω i → ω→nato ltd ≡ i
   lemma {x} Zero iφ eq = refl
   lemma {x} (Suc i) iφ eq = ⊥-elim ( ωs≠0 (nat→ω i) (trans (sym eq) o∅≡od∅ )) -- Union (nat→ω i , (nat→ω i , nat→ω i)) ≡ od∅
   lemma Zero (isuc {x} ltd) eq = ⊥-elim ( ωs≠0 (* x) (subst (λ k → k ≡ od∅  ) *iso eq ))
   lemma (Suc i) (isuc {x} ltd) eq = cong (λ k → Suc k ) (lemma i ltd (lemma1 eq) )  where -- * x ≡ nat→ω i
           lemma1 :  * (& (Union (* x , (* x , * x)))) ≡ Union (nat→ω i , (nat→ω i , nat→ω i)) → * x ≡ nat→ω i
           lemma1 eq = subst (λ k → * x ≡ k ) *iso (cong (λ k → * k)
                ( ω-prev-eq (subst (λ k → _ ≡ k ) &iso (cong (λ k → & k ) (sym
                    (subst (λ k → _ ≡ Union ( k , ( k , k ))) (sym *iso ) eq ))))))

