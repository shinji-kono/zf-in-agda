module bijection where

open import Level renaming ( zero to Zero ; suc to Suc )
open import Data.Nat
open import Data.Maybe
open import Data.List hiding ([_] ; sum )
open import Data.Nat.Properties
open import Relation.Nullary
open import Data.Empty
open import Data.Unit hiding ( _≤_ )
open import  Relation.Binary.Core hiding (_⇔_)
open import  Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality

open import logic
open import nat

-- record Bijection {n m : Level} (R : Set n) (S : Set m) : Set (n Level.⊔ m)  where
--    field
--        fun←  :  S → R
--        fun→  :  R → S
--        fiso← : (x : R)  → fun← ( fun→ x )  ≡ x 
--        fiso→ : (x : S ) → fun→ ( fun← x )  ≡ x 
-- 
-- injection :  {n m : Level} (R : Set n) (S : Set m) (f : R → S ) → Set (n Level.⊔ m)
-- injection R S f = (x y : R) → f x ≡ f y → x ≡ y

open Bijection 

bi-trans : {n m l : Level} (R : Set n) (S : Set m) (T : Set l)  → Bijection R S → Bijection S T → Bijection R T
bi-trans R S T rs st = record { fun← = λ x → fun← rs ( fun← st x ) ; fun→ = λ x → fun→ st ( fun→ rs x )
    ; fiso← = λ x →  trans (cong (λ k → fun← rs k) (fiso← st (fun→ rs x))) ( fiso← rs x)
    ; fiso→ = λ x →  trans (cong (λ k → fun→ st k) (fiso→ rs (fun← st x))) ( fiso→ st x) }

bid : {n : Level} (R : Set n)  → Bijection R R
bid {n} R = record {  fun← = λ x → x ; fun→  = λ x → x ; fiso← = λ _ → refl ;  fiso→ = λ _ → refl } 

bi-sym : {n m : Level} (R : Set n) (S : Set m) → Bijection R S →  Bijection S R
bi-sym R S eq = record {  fun← =  fun→ eq ; fun→  = fun← eq  ; fiso← =  fiso→ eq ;  fiso→ =  fiso← eq } 

open import Relation.Binary.Structures

bijIsEquivalence : {n : Level } → IsEquivalence  (Bijection {n} {n})
bijIsEquivalence = record { refl = λ {R} → bid R ; sym = λ {R} {S} → bi-sym R S ; trans = λ {R} {S} {T} → bi-trans R S T }

--  ¬ A = A → ⊥ 
--
-- famous diagnostic function
--

diag : {S : Set }  (b : Bijection  ( S → Bool ) S) → S → Bool
diag b n = not (fun← b n n)

diagonal : { S : Set } → ¬ Bijection  ( S → Bool ) S
diagonal {S} b = diagn1 (fun→ b (λ n → diag b n) ) refl where
    diagn1 : (n : S ) → ¬ (fun→ b (λ n → diag b n) ≡ n ) 
    diagn1 n dn = ¬t=f (diag b n ) ( begin
           not (diag b n)
        ≡⟨⟩
           not (not fun← b n n)
        ≡⟨ cong (λ k → not (k  n) ) (sym (fiso← b _)) ⟩
           not (fun← b (fun→ b (diag b))  n)
        ≡⟨ cong (λ k → not (fun← b k n) ) dn ⟩
           not (fun← b n n)
        ≡⟨⟩
           diag b n 
        ∎ ) where open ≡-Reasoning

b1 : (b : Bijection  ( ℕ → Bool ) ℕ) → ℕ 
b1 b = fun→ b (diag b)

b-iso : (b : Bijection  ( ℕ → Bool ) ℕ) → fun← b (b1 b) ≡ (diag b)
b-iso b = fiso← b _

--
-- ℕ <=> ℕ + 1
--
to1 : {n : Level} {R : Set n} → Bijection ℕ R → Bijection ℕ (⊤ ∨ R )
to1 {n} {R} b = record {
       fun←  = to11
     ; fun→  = to12
     ; fiso← = to13
     ; fiso→ = to14
   } where
       to11 : ⊤ ∨ R → ℕ
       to11 (case1 tt) = 0
       to11 (case2 x) = suc ( fun← b x )
       to12 : ℕ → ⊤ ∨ R
       to12 zero = case1 tt
       to12 (suc n) = case2 ( fun→ b n)
       to13 : (x : ℕ) → to11 (to12 x) ≡ x
       to13 zero = refl
       to13 (suc x) = cong suc (fiso← b x)
       to14 : (x : ⊤ ∨ R) → to12 (to11 x) ≡ x
       to14 (case1 x) = refl
       to14 (case2 x) = cong case2 (fiso→ b x)


open _∧_

record NN ( i  : ℕ) (nxn→n :  ℕ →  ℕ → ℕ)  : Set where
  field
     j k : ℕ
     k1 : nxn→n j k ≡ i
     nn-unique : {j0 k0 : ℕ } →  nxn→n j0 k0 ≡ i  → ⟪ j , k ⟫ ≡ ⟪ j0 , k0 ⟫ 

i≤0→i≡0 : {i : ℕ } → i ≤ 0 → i ≡ 0
i≤0→i≡0 {0} z≤n = refl


nxn : Bijection ℕ (ℕ ∧ ℕ)
nxn = record {
     fun← = λ p → nxn→n (proj1 p) (proj2 p)
   ; fun→ =  n→nxn 
   ; fiso← = λ i → NN.k1 (nn i)
   ; fiso→ = λ x → nn-id (proj1 x) (proj2 x)
  } where
     nxn→n :  ℕ →  ℕ → ℕ
     nxn→n zero zero = zero
     nxn→n zero (suc j) = j + suc (nxn→n zero j)
     nxn→n (suc i) zero = suc i + suc (nxn→n i zero)
     nxn→n (suc i) (suc j) = suc i + suc j + suc (nxn→n i (suc j))
     nn : ( i  : ℕ) → NN i nxn→n 
     n→nxn : ℕ → ℕ ∧ ℕ
     n→nxn n = ⟪ NN.j (nn n)  , NN.k (nn n) ⟫
     k0 : {i : ℕ } → n→nxn i ≡ ⟪ NN.j (nn i) , NN.k (nn i) ⟫ 
     k0 {i} = refl

     nxn→n0 : { j k : ℕ } →  nxn→n j k ≡ 0 → ( j ≡ 0 ) ∧ ( k ≡ 0 )
     nxn→n0 {zero} {zero} eq = ⟪ refl , refl ⟫
     nxn→n0 {zero} {(suc k)} eq = ⊥-elim ( nat-≡< (sym eq) (subst (λ k → 0 < k) (+-comm _ k) (s≤s z≤n)))
     nxn→n0 {(suc j)} {zero} eq = ⊥-elim ( nat-≡< (sym eq) (s≤s z≤n) )
     nxn→n0 {(suc j)} {(suc k)} eq = ⊥-elim ( nat-≡< (sym eq) (s≤s z≤n) )

     nid20 : (i : ℕ) →  i +  (nxn→n 0 i) ≡ nxn→n i 0
     nid20 zero = refl -- suc (i + (i + suc (nxn→n 0 i))) ≡ suc (i + suc (nxn→n i 0))
     nid20 (suc i) = begin
         suc (i + (i + suc (nxn→n 0 i)))  ≡⟨ cong (λ k → suc (i + k)) (sym (+-assoc i 1 (nxn→n 0 i))) ⟩
         suc (i + ((i + 1) + nxn→n 0 i))  ≡⟨ cong (λ k →  suc (i + (k + nxn→n 0 i))) (+-comm i 1)  ⟩
         suc (i + suc (i + nxn→n 0 i)) ≡⟨ cong ( λ k → suc (i + suc k)) (nid20 i)  ⟩
         suc (i + suc (nxn→n i 0)) ∎  where open ≡-Reasoning

     nid4 : {i j : ℕ} →  i + 1 + j ≡ i + suc j
     nid4 {zero} {j} = refl
     nid4 {suc i} {j} = cong suc (nid4 {i} {j} )
     nid5 : {i j k : ℕ} →  i + suc (suc j) + suc k ≡ i + suc j + suc (suc k )
     nid5 {zero} {j} {k} = begin
          suc (suc j) + suc k ≡⟨ +-assoc 1 (suc j) _ ⟩
          1 + (suc j + suc k) ≡⟨ +-comm 1 _ ⟩
          (suc j + suc k) + 1 ≡⟨ +-assoc (suc j) (suc k) _ ⟩
          suc j + (suc k + 1) ≡⟨ cong (λ k → suc j + k ) (+-comm (suc k) 1) ⟩
          suc j + suc (suc k) ∎ where open ≡-Reasoning
     nid5 {suc i} {j} {k} = cong suc (nid5 {i} {j} {k} )

     -- increment in the same stage
     nid2 : (i j : ℕ) → suc (nxn→n i (suc j)) ≡ nxn→n (suc i) j 
     nid2 zero zero = refl
     nid2 zero (suc j) = refl
     nid2 (suc i) zero = begin
          suc (nxn→n (suc i) 1)  ≡⟨ refl ⟩
          suc (suc (i + 1 + suc (nxn→n i 1)))  ≡⟨ cong (λ k → suc (suc k)) nid4  ⟩
          suc (suc (i + suc (suc (nxn→n i 1))))  ≡⟨ cong (λ k →  suc (suc (i + suc (suc k)))) (nid3 i) ⟩
          suc (suc (i + suc (suc (i + suc (nxn→n i 0)))))  ≡⟨ refl ⟩
          nxn→n (suc (suc i)) zero ∎ where
             open ≡-Reasoning
             nid3 : (i : ℕ) → nxn→n i 1 ≡ i + suc (nxn→n i 0)
             nid3 zero = refl
             nid3 (suc i) = begin
                 suc (i + 1 + suc (nxn→n i 1)) ≡⟨ cong suc nid4 ⟩
                 suc (i + suc (suc (nxn→n i 1))) ≡⟨ cong (λ k →  suc (i + suc (suc k))) (nid3 i) ⟩
                 suc (i + suc (suc (i + suc (nxn→n i 0)))) ∎
     nid2 (suc i) (suc j) = begin
          suc (nxn→n (suc i) (suc (suc j)))  ≡⟨ refl ⟩
          suc (suc (i + suc (suc j) + suc (nxn→n i (suc (suc j)))))  ≡⟨ cong (λ k → suc (suc (i + suc (suc j) + k))) (nid2 i (suc j)) ⟩
          suc (suc (i + suc (suc j) + suc      (i + suc j + suc (nxn→n i (suc j)))))  ≡⟨ cong ( λ k → suc (suc k)) nid5 ⟩
          suc (suc (i + suc j       + suc (suc (i + suc j + suc (nxn→n i (suc j)))))) ≡⟨ refl ⟩
          nxn→n (suc (suc i)) (suc j) ∎ where
             open ≡-Reasoning

     -- increment the stage
     nid00 : (i : ℕ) → suc (nxn→n i 0) ≡ nxn→n 0 (suc i) 
     nid00 zero = refl
     nid00 (suc i) = begin
        suc (suc (i + suc (nxn→n i 0))) ≡⟨ cong (λ k → suc (suc (i + k ))) (nid00 i) ⟩
        suc (suc (i + (nxn→n 0 (suc i)))) ≡⟨ refl ⟩
        suc (suc (i + (i + suc (nxn→n 0 i))))  ≡⟨ cong suc (sym ( +-assoc 1 i (i + suc (nxn→n 0 i)))) ⟩
        suc ((1 + i) + (i + suc (nxn→n 0 i))) ≡⟨ cong (λ k → suc (k + (i + suc (nxn→n 0 i)))) (+-comm 1 i) ⟩
        suc ((i + 1) + (i + suc (nxn→n 0 i))) ≡⟨ cong suc (+-assoc i 1 (i + suc (nxn→n 0 i))) ⟩
        suc (i + suc (i + suc (nxn→n 0 i))) ∎ where open ≡-Reasoning

     -----
     --
     -- create the invariant NN for all n
     --
     nn zero = record { j = 0 ; k = 0 ; k1 = refl 
        ;  nn-unique = λ {j0} {k0} eq → cong₂ (λ x y → ⟪ x , y ⟫) (sym (proj1 (nxn→n0 eq))) (sym (proj2 (nxn→n0 {j0} {k0} eq))) }
     nn (suc i) with NN.k (nn i)  | inspect  NN.k (nn i) 
     ... | zero | record { eq = eq } = record { k = suc (sum ) ; j = 0 
         ; k1 = nn02 ; nn-unique = nn04 } where
            ---
            --- increment the stage
            ---
            sum = NN.j (nn i) + NN.k (nn i)
            stage = minus i (NN.j (nn i))
            j = NN.j (nn i)
            NNnn :  NN.j (nn i) + NN.k (nn i) ≡ sum
            NNnn = sym refl
            nn02 :  nxn→n 0 (suc sum)  ≡ suc i
            nn02 = begin
               sum + suc (nxn→n 0 sum) ≡⟨ sym (+-assoc sum 1 (nxn→n 0 sum)) ⟩
               (sum + 1) + nxn→n 0 sum  ≡⟨ cong (λ k → k + nxn→n 0 sum )  (+-comm sum 1 )⟩
               suc (sum + nxn→n 0 sum) ≡⟨ cong suc (nid20 sum ) ⟩
               suc (nxn→n sum 0) ≡⟨ cong (λ k → suc (nxn→n k 0 )) (sym (NNnn )) ⟩
               suc (nxn→n (NN.j (nn i) + (NN.k (nn i))  ) 0) ≡⟨ cong₂ (λ j k → suc (nxn→n (NN.j (nn i) + j) k )) eq (sym eq)  ⟩
               suc (nxn→n (NN.j (nn i) + 0 ) (NN.k (nn i))) ≡⟨ cong (λ k → suc ( nxn→n k (NN.k (nn i)))) (+-comm (NN.j (nn i)) 0) ⟩
               suc (nxn→n (NN.j (nn i)) (NN.k (nn i))) ≡⟨ cong suc (NN.k1 (nn i) ) ⟩
               suc i ∎  where open ≡-Reasoning
            nn04 : {j0 k0 : ℕ} → nxn→n j0 k0 ≡ suc i → ⟪ 0 , suc (sum ) ⟫ ≡ ⟪ j0 , k0 ⟫
            nn04 {zero} {suc k0} eq1 = cong (λ k → ⟪ 0 , k ⟫ ) (cong suc (sym nn08)) where -- eq : nxn→n zero (suc k0) ≡ suc i -- 
               nn07 : nxn→n k0 0 ≡ i
               nn07 = cong pred ( begin
                  suc ( nxn→n k0 0 ) ≡⟨ nid00 k0 ⟩
                  nxn→n 0 (suc k0 )  ≡⟨ eq1 ⟩
                  suc i  ∎ )  where open ≡-Reasoning 
               nn08 : k0 ≡ sum 
               nn08 = begin
                  k0  ≡⟨ cong proj1 (sym (NN.nn-unique (nn i) nn07)) ⟩
                  NN.j (nn i)  ≡⟨ +-comm 0 _ ⟩
                  NN.j (nn i) + 0  ≡⟨ cong (λ k →  NN.j (nn i) + k) (sym eq) ⟩
                  NN.j (nn i) + NN.k (nn i)  ≡⟨ NNnn  ⟩
                  sum   ∎   where open ≡-Reasoning 
            nn04 {suc j0} {k0} eq1 = ⊥-elim ( nat-≡< (cong proj2 (nn06 nn05)) (subst (λ k → k < suc k0) (sym eq) (s≤s z≤n))) where
               nn05 : nxn→n j0 (suc k0) ≡ i
               nn05 = begin
                  nxn→n j0 (suc k0)  ≡⟨ cong pred ( begin 
                    suc (nxn→n j0 (suc k0))  ≡⟨ nid2 j0 k0 ⟩
                    nxn→n (suc j0) k0  ≡⟨ eq1 ⟩
                    suc i ∎ ) ⟩
                  i ∎   where open ≡-Reasoning 
               nn06 : nxn→n j0 (suc k0) ≡ i → ⟪ NN.j (nn i) , NN.k (nn i) ⟫ ≡ ⟪ j0 , suc k0 ⟫ 
               nn06 = NN.nn-unique (nn i)
     ... | suc k  | record {eq = eq} = record { k = k ; j = suc (NN.j (nn i)) ; k1 = nn11 ;  nn-unique = nn13 } where
            ---
            --- increment in a stage
            ---
            sum = NN.j (nn i) + NN.k (nn i)
            stage = minus i (NN.j (nn i))
            j = NN.j (nn i)
            NNnn :  NN.j (nn i) + NN.k (nn i) ≡ sum
            NNnn = sym refl
            nn10 : suc (NN.j (nn i)) + k ≡ sum 
            nn10 = begin
                suc (NN.j (nn i)) + k ≡⟨ cong (λ x → x + k) (+-comm 1 _)  ⟩
                (NN.j (nn i) + 1) + k ≡⟨  +-assoc (NN.j (nn i)) 1 k ⟩
                NN.j (nn i) + suc k  ≡⟨ cong (λ k → NN.j (nn i) + k) (sym eq) ⟩
                NN.j (nn i) + NN.k (nn i) ≡⟨ NNnn  ⟩
                sum   ∎   where open ≡-Reasoning 
            nn11 :  nxn→n (suc (NN.j (nn i))) k ≡ suc i --  nxn→n ( NN.j (nn i)) (NN.k (nn i) ≡ i
            nn11 = begin
                nxn→n (suc (NN.j (nn i))) k   ≡⟨ sym (nid2 (NN.j (nn i)) k) ⟩
                suc (nxn→n (NN.j (nn i)) (suc k)) ≡⟨ cong (λ k →   suc (nxn→n (NN.j (nn i)) k)) (sym eq) ⟩
                suc (nxn→n ( NN.j (nn i)) (NN.k (nn i)))  ≡⟨ cong suc (NN.k1 (nn i)) ⟩
                suc i  ∎   where open ≡-Reasoning 
            nn18 :  zero < NN.k (nn i)
            nn18 = subst (λ k → 0 < k ) ( begin
                    suc k ≡⟨ sym eq ⟩
                    NN.k (nn i)  ∎  ) (s≤s z≤n )  where open ≡-Reasoning  
            nn13 :  {j0 k0 : ℕ} → nxn→n j0 k0 ≡ suc i → ⟪ suc (NN.j (nn i)) , k ⟫ ≡ ⟪ j0 , k0 ⟫
            nn13 {zero} {suc k0} eq1 = ⊥-elim ( nat-≡< (sym (cong proj2 nn17)) nn18 ) where  -- (nxn→n zero (suc k0)) ≡ suc i
                nn16 : nxn→n k0 zero ≡ i
                nn16 =  cong pred ( subst (λ k → k ≡ suc i) (sym ( nid00 k0 )) eq1 )
                nn17 : ⟪ NN.j (nn i) , NN.k (nn i) ⟫ ≡ ⟪ k0 , zero ⟫
                nn17 = NN.nn-unique (nn i) nn16
            nn13 {suc j0} {k0} eq1 = begin
               ⟪ suc (NN.j (nn i)) , pred (suc k) ⟫ ≡⟨ cong (λ k →  ⟪ suc (NN.j (nn i)) , pred k ⟫ ) (sym eq) ⟩
               ⟪ suc (NN.j (nn i)) , pred (NN.k (nn i)) ⟫ ≡⟨ cong (λ k → ⟪ suc (proj1 k) , pred (proj2 k) ⟫) ( begin 
                 ⟪ NN.j (nn i) , NN.k (nn i) ⟫  ≡⟨ nn15 ⟩
                 ⟪ j0 , suc k0 ⟫ ∎ ) ⟩
               ⟪ suc j0 , k0 ⟫ ∎  where -- nxn→n (suc j0) k0 ≡ suc i
                open ≡-Reasoning
                nn14 : nxn→n j0 (suc k0) ≡ i
                nn14 = cong pred ( subst (λ k → k ≡ suc i) (sym ( nid2 j0 k0 )) eq1 )
                nn15 : ⟪ NN.j (nn i) , NN.k (nn i) ⟫ ≡ ⟪ j0 , suc k0 ⟫
                nn15 = NN.nn-unique (nn i) nn14

     nn-id : (j k : ℕ) → n→nxn (nxn→n j k) ≡ ⟪ j , k ⟫
     nn-id j k = begin
          n→nxn (nxn→n j k)  ≡⟨ refl ⟩
          ⟪ NN.j (nn (nxn→n j k)) , NN.k (nn (nxn→n j k)) ⟫ ≡⟨ NN.nn-unique (nn (nxn→n j k)) refl ⟩
          ⟪ j , k ⟫ ∎  where open ≡-Reasoning


--   []     0
--   0    → 1
--   1    → 2
--   01   → 3
--   11   → 4
--   ...

--
-- binary invariant
--
record LB (n : ℕ) (lton : List Bool → ℕ ) : Set where
  field
     nlist : List Bool
     isBin : lton nlist ≡ n
     isUnique :  (x : List Bool) → lton x ≡ n → nlist  ≡ x 

lb+1 : List Bool → List Bool
lb+1 [] =  false ∷ [] 
lb+1 (false ∷ t) = true ∷ t 
lb+1 (true ∷ t) =  false ∷ lb+1 t

lb-1 : List Bool → List Bool
lb-1 [] =  []
lb-1 (true ∷ t) = false ∷ t 
lb-1 (false ∷ t) with lb-1 t
... | [] = true ∷ []
... | x ∷ t1 = true ∷ x ∷ t1

LBℕ : Bijection ℕ ( List Bool ) 
LBℕ = record {
       fun←  = λ x → lton x 
     ; fun→  = λ n → LB.nlist (lb n) 
     ; fiso← = λ n → LB.isBin (lb n)
     ; fiso→ = λ x → LB.isUnique (lb (lton x)) x refl
   } where
     lton1 : List Bool → ℕ
     lton1 [] = 1
     lton1 (true ∷ t) = suc (lton1 t + lton1 t)
     lton1 (false ∷ t) = lton1 t + lton1 t
     lton : List Bool → ℕ
     lton x  = pred (lton1 x)

     lton1>0 : (x : List Bool ) → 0 < lton1 x 
     lton1>0 [] = a<sa
     lton1>0 (true ∷ x₁) = 0<s
     lton1>0 (false ∷ t) = ≤-trans (lton1>0 t) x≤x+y

     2lton1>0 : (t : List Bool ) →  0 < lton1 t + lton1 t
     2lton1>0 t = ≤-trans (lton1>0 t) x≤x+y

     lb=3 : {x y : ℕ} → 0 < x → 0 < y → 1 ≤ pred (x + y)
     lb=3 {suc x} {suc y} (s≤s 0<x) (s≤s 0<y) = subst (λ k → 1 ≤ k ) (+-comm (suc y) _ ) (s≤s z≤n)

     lton-cons>0 : {x : Bool} {y : List Bool } → 0 < lton (x ∷ y)
     lton-cons>0 {true} {[]} = refl-≤s
     lton-cons>0 {true} {x ∷ y} = ≤-trans ( lb=3 (lton1>0 (x ∷ y)) (lton1>0 (x ∷ y))) px≤x
     lton-cons>0 {false} {[]} = refl-≤
     lton-cons>0 {false} {x ∷ y} = lb=3 (lton1>0 (x ∷ y)) (lton1>0 (x ∷ y))

     lb=0 : {x y : ℕ } → pred x  < pred y → suc (x + x ∸ 1) < suc (y + y ∸ 1)
     lb=0 {0} {suc y} lt = s≤s (subst (λ k → 0 < k ) (+-comm (suc y) y ) 0<s)
     lb=0 {suc x} {suc y} lt = begin
            suc (suc ((suc x + suc x) ∸ 1)) ≡⟨ refl  ⟩
            suc (suc x) + suc x ≡⟨ refl ⟩
            suc (suc x + suc x) ≤⟨ <-plus (s≤s lt) ⟩
            suc y + suc x <⟨ <-plus-0 {suc x} {suc y} {suc y} (s≤s lt) ⟩
            suc y + suc y ≡⟨ refl ⟩
            suc ((suc y + suc y) ∸ 1) ∎  where open ≤-Reasoning
     lb=2 : {x y : ℕ } → pred x  < pred y → suc (x + x ) < suc (y + y )
     lb=2 {zero} {suc y} lt = s≤s 0<s
     lb=2 {suc x} {suc y} lt = s≤s (lb=0 {suc x} {suc y} lt)
     lb=1 : {x y : List Bool} {z : Bool} → lton (z ∷ x) ≡ lton (z ∷ y) → lton x ≡ lton y 
     lb=1 {x} {y} {true} eq with <-cmp (lton x) (lton y)
     ... | tri< a ¬b ¬c = ⊥-elim (nat-≡< (cong suc eq) (lb=2 {lton1 x} {lton1 y} a))
     ... | tri≈ ¬a b ¬c = b
     ... | tri> ¬a ¬b c = ⊥-elim (nat-≡< (cong suc (sym eq)) (lb=2 {lton1 y} {lton1 x} c))
     lb=1 {x} {y} {false} eq with <-cmp (lton x) (lton y)
     ... | tri< a ¬b ¬c = ⊥-elim (nat-≡< (cong suc eq) (lb=0 {lton1 x} {lton1 y} a))
     ... | tri≈ ¬a b ¬c = b
     ... | tri> ¬a ¬b c = ⊥-elim (nat-≡< (cong suc (sym eq)) (lb=0 {lton1 y} {lton1 x} c))

     ---
     --- lton is unique in a head
     ---
     lb-tf : {x y : List Bool } → ¬ (lton (true ∷ x) ≡ lton (false ∷ y))
     lb-tf {x} {y} eq with <-cmp (lton1 x) (lton1 y)
     ... | tri< a ¬b ¬c = ⊥-elim ( nat-≡< eq (lb=01 a)) where
        lb=01 : {x y : ℕ } → x  < y → x + x  < (y + y ∸ 1)
        lb=01 {x} {y} x<y = begin
            suc (x + x) ≡⟨ refl  ⟩
            suc x + x ≤⟨ ≤-plus x<y ⟩
            y + x ≡⟨ refl ⟩
            pred (suc y + x) ≡⟨ cong (λ k → pred ( k + x)) (+-comm 1 y) ⟩
            pred ((y + 1) + x ) ≡⟨ cong pred (+-assoc y 1 x)  ⟩
            pred (y + suc x) ≤⟨ px≤py (≤-plus-0 {suc x} {y} {y} x<y) ⟩
            (y + y) ∸ 1  ∎  where open ≤-Reasoning
     ... | tri> ¬a ¬b c = ⊥-elim ( nat-≡< (sym eq) (lb=02 c) ) where
        lb=02 : {x y : ℕ } → x  < y → x + x ∸ 1 < y + y
        lb=02 {0} {y} lt = ≤-trans lt x≤x+y 
        lb=02 {suc x} {y} lt = begin
            suc ( suc x + suc x ∸ 1 ) ≡⟨ refl ⟩
            suc x + suc x  ≤⟨ ≤-plus {suc x} (<to≤ lt) ⟩
            y + suc x  ≤⟨ ≤-plus-0 (<to≤ lt) ⟩
            y + y  ∎  where open ≤-Reasoning
     ... | tri≈ ¬a b ¬c = ⊥-elim ( nat-≡< (sym eq) ( begin
            suc (lton1 y + lton1 y ∸ 1) ≡⟨ sucprd ( 2lton1>0 y) ⟩
            lton1 y + lton1 y  ≡⟨  cong (λ k → k + k ) (sym b)  ⟩
            lton1 x + lton1 x ∎  )) where open ≤-Reasoning

     ---
     --- lton injection
     ---
     lb=b : (x y : List Bool) → lton x ≡ lton y → x ≡ y
     lb=b [] [] eq = refl
     lb=b [] (x ∷ y) eq = ⊥-elim ( nat-≡< eq (lton-cons>0 {x} {y} ))
     lb=b (x ∷ y) [] eq = ⊥-elim ( nat-≡< (sym eq) (lton-cons>0 {x} {y} ))
     lb=b (true ∷ x) (false ∷ y) eq = ⊥-elim ( lb-tf {x} {y} eq )
     lb=b (false ∷ x) (true ∷ y) eq = ⊥-elim ( lb-tf {y} {x} (sym eq) )
     lb=b (true ∷ x)  (true ∷ y)  eq = cong (λ k → true ∷ k  ) (lb=b x y (lb=1 {x} {y} {true}  eq)) 
     lb=b (false ∷ x) (false ∷ y) eq = cong (λ k → false ∷ k ) (lb=b x y (lb=1 {x} {y} {false} eq)) 

     lb : (n : ℕ) → LB n lton
     lb zero = record { nlist = [] ; isBin = refl ; isUnique = lb05 } where
         lb05 : (x : List Bool) → lton x ≡ zero → [] ≡ x
         lb05 x eq = lb=b [] x (sym eq)
     lb (suc n) with LB.nlist (lb n) | inspect LB.nlist (lb n) 
     ... | [] | record { eq = eq } = record { nlist = false ∷ [] ; isUnique = lb06 ; isBin = lb10 } where
         open ≡-Reasoning
         lb10 : lton1 (false ∷ []) ∸ 1 ≡ suc n
         lb10 = begin
           lton (false ∷ []) ≡⟨ refl ⟩ 
           suc 0  ≡⟨ refl ⟩ 
           suc (lton [])   ≡⟨ cong (λ k → suc (lton k)) (sym eq) ⟩ 
           suc (lton (LB.nlist (lb n)))  ≡⟨ cong suc (LB.isBin (lb n) ) ⟩ 
           suc n ∎    
         lb06 :  (x : List Bool) → pred (lton1 x ) ≡ suc n → false ∷ [] ≡ x
         lb06 x eq1 = lb=b (false ∷ []) x (trans lb10 (sym eq1)) -- lton (false ∷ []) ≡ lton x
     ... | false ∷ t | record { eq = eq } =  record { nlist = true ∷ t ; isBin = lb01 ; isUnique = lb09 } where
        lb01 : lton (true ∷ t) ≡ suc n
        lb01 = begin
           lton (true ∷ t)  ≡⟨ refl ⟩ 
           lton1 t + lton1 t   ≡⟨ sym ( sucprd (2lton1>0 t) ) ⟩ 
           suc (pred (lton1 t + lton1 t ))  ≡⟨ refl ⟩ 
           suc (lton (false ∷ t))   ≡⟨ cong (λ k → suc (lton k )) (sym eq) ⟩ 
           suc (lton (LB.nlist (lb n))) ≡⟨  cong suc (LB.isBin (lb n)) ⟩ 
           suc n ∎  where open ≡-Reasoning
        lb09 :  (x : List Bool) → lton1 x ∸ 1 ≡ suc n → true ∷ t ≡ x
        lb09 x eq1 = lb=b (true ∷ t) x (trans lb01 (sym eq1) ) --  lton (true ∷ t) ≡ lton x
     ... | true ∷ t | record { eq = eq } = record { nlist =  lb+1 (true ∷ t) ; isBin = lb02 (true ∷ t) lb03 ; isUnique = lb07 } where
        lb03 : lton (true ∷ t) ≡ n
        lb03 = begin
           lton (true ∷ t)   ≡⟨ cong (λ k → lton k ) (sym eq ) ⟩ 
           lton (LB.nlist (lb n)) ≡⟨ LB.isBin (lb n) ⟩ 
           n ∎  where open ≡-Reasoning

        add11 : (x1 : ℕ ) → suc x1 + suc x1 ≡ suc (suc  (x1 + x1))
        add11 zero = refl
        add11 (suc x) = cong (λ k → suc (suc k)) (trans (+-comm x _) (cong suc (+-comm _ x)))

        lb04 : (t : List Bool) →  suc (lton1 t) ≡ lton1 (lb+1 t) 
        lb04 [] = refl
        lb04 (false ∷ t) = refl
        lb04 (true ∷ []) = refl
        lb04 (true ∷ t0 )  = begin
           suc (suc (lton1 t0 + lton1 t0)) ≡⟨ sym (add11 (lton1 t0)) ⟩ 
           suc (lton1 t0) + suc (lton1 t0) ≡⟨ cong (λ k → k + k ) (lb04 t0  ) ⟩ 
           lton1 (lb+1 t0) + lton1 (lb+1 t0) ∎  where
              open ≡-Reasoning

        lb02 : (t : List Bool) → lton t ≡ n → lton (lb+1 t) ≡ suc n
        lb02 [] refl = refl
        lb02 t eq1 = begin
            lton (lb+1 t) ≡⟨ refl ⟩
            pred (lton1 (lb+1 t)) ≡⟨ cong pred (sym (lb04 t)) ⟩
            pred (suc (lton1 t))  ≡⟨ sym (sucprd (lton1>0 t)) ⟩
            suc (pred (lton1 t)) ≡⟨ refl ⟩
            suc (lton t) ≡⟨ cong suc eq1  ⟩
            suc n ∎  where open ≡-Reasoning

        lb07 : (x : List Bool) → pred (lton1 x ) ≡ suc n → lb+1 (true ∷ t) ≡ x
        lb07 x eq1 = lb=b (lb+1 (true ∷ t)) x (trans ( lb02 (true ∷ t) lb03 ) (sym eq1)) 
