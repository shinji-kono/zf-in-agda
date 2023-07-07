{-# OPTIONS --allow-unsolved-metas #-}

module bijection where


open import Level renaming ( zero to Zero ; suc to Suc )
open import Data.Nat
open import Data.Maybe
open import Data.List hiding ([_] ; sum )
open import Data.Nat.Properties
open import Relation.Nullary
open import Data.Empty
open import Data.Unit using ( tt ; ⊤ )
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

bi-inject← : {n m : Level} {R : Set n} {S : Set m} → (rs : Bijection R S) → {x y : S} → fun← rs x ≡ fun← rs y → x ≡ y
bi-inject← rs {x} {y} eq = subst₂ (λ j k → j ≡ k ) (fiso→  rs _) (fiso→ rs _) (cong (fun→ rs) eq)

bi-inject→ : {n m : Level} {R : Set n} {S : Set m} → (rs : Bijection R S) → {x y : R} → fun→ rs x ≡ fun→ rs y → x ≡ y
bi-inject→ rs {x} {y} eq = subst₂ (λ j k → j ≡ k ) (fiso←  rs _) (fiso← rs _) (cong (fun← rs) eq)

open import Relation.Binary.Structures

bijIsEquivalence : {n : Level } → IsEquivalence  (Bijection {n} {n})
bijIsEquivalence = record { refl = λ {R} → bid R ; sym = λ {R} {S} → bi-sym R S ; trans = λ {R} {S} {T} → bi-trans R S T }

--  ¬ A = A → ⊥
--
-- famous diagnostic function
--

--   1 1 0 1 0 ...
--   0 1 0 1 0 ...
--   1 0 0 1 0 ...
--   1 1 1 1 0 ...

--   0 0 1 0 1 ...  diag

diag : {S : Set }  (b : Bijection  ( S → Bool ) S) → S → Bool
diag b n = not (fun← b n n)

diagonal : { S : Set } → ¬ Bijection  ( S → Bool ) S
diagonal {S} b = diagn1 (fun→ b (λ n → diag b n) ) refl where
    diagn1 : (n : S ) → ¬ (fun→ b (λ n → diag b n) ≡ n )
    diagn1 n dn = ¬t=f (diag b n ) ( begin
           not (diag b n)
        ≡⟨⟩
           not (not (fun← b n n))
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
-- ℕ <=> ℕ + 1    (infinite hotel)
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

----
--    (0, 0) (0, 1)  (0, 2) ....
--    (1, 0) (1, 1)  (1, 2) ....
--    (2, 0) (2, 1)  (2, 2) ....
--      :      :      :
--      :      :      :
--

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
        lb04 (true ∷ t0 @ (_ ∷ _))  = begin
           suc (suc (lton1 t0 + lton1 t0)) ≡⟨ sym (add11 (lton1 t0)) ⟩
           suc (lton1 t0) + suc (lton1 t0) ≡⟨ cong (λ k → k + k ) (lb04 t0  ) ⟩
           lton1 (lb+1 t0) + lton1 (lb+1 t0) ∎  where
              open ≡-Reasoning

        lb02 : (t : List Bool) → lton t ≡ n → lton (lb+1 t) ≡ suc n
        lb02 [] refl = refl
        lb02 (t @ (_ ∷ _)) eq1 = begin
            lton (lb+1 t) ≡⟨ refl ⟩
            pred (lton1 (lb+1 t)) ≡⟨ cong pred (sym (lb04 t)) ⟩
            pred (suc (lton1 t))  ≡⟨ sym (sucprd (lton1>0 t)) ⟩
            suc (pred (lton1 t)) ≡⟨ refl ⟩
            suc (lton t) ≡⟨ cong suc eq1  ⟩
            suc n ∎  where open ≡-Reasoning

        lb07 : (x : List Bool) → pred (lton1 x ) ≡ suc n → lb+1 (true ∷ t) ≡ x
        lb07 x eq1 = lb=b (lb+1 (true ∷ t)) x (trans ( lb02 (true ∷ t) lb03 ) (sym eq1))

-- Bernstein is non constructive, so we cannot use this without some assumption
--   but in case of ℕ, we can construct it directly.

open import Data.List hiding ([_])
open import Data.List.Relation.Unary.Any

record InjectiveF (A B : Set) : Set where
   field
      f : A → B
      inject : {x y : A} → f x ≡ f y → x ≡ y

record Is (A C : Set) (f : A → C) (c : C) : Set where
   field
      a : A
      fa=c : f a ≡ c

Countable-Bernstein : (A B C : Set) → Bijection A ℕ → Bijection C ℕ
     → (fi : InjectiveF A  B ) → (gi : InjectiveF  B C )
     → (is-A : (c : C ) → Dec (Is A C (λ x → (InjectiveF.f gi (InjectiveF.f fi x))) c )) 
     → (is-B : (c : C ) → Dec (Is B C (InjectiveF.f gi) c)  )
     → Bijection B ℕ
Countable-Bernstein A B C an cn fi gi is-A is-B = record {
       fun→  = λ x → bton x
     ; fun←  = λ n → ntob n
     ; fiso→ = biso
     ; fiso← = biso1 
   } where
    --
    --     an     f     g     cn
    --   ℕ ↔   A  →  B  →  C  ↔   ℕ
    --            B = Image A f ∪ (B \ Image A f )
    -- 
    open Bijection
    f = InjectiveF.f fi
    g = InjectiveF.f gi

    --
    -- count number of valid A and B in C
    --     the count of B is the numner of B in Bijection B ℕ
    --     if we have a , number a of A is larger than the numner of B C, so we have the inverse
    --

    count-B : ℕ → ℕ
    count-B zero with is-B (fun← cn zero)
    ... | yes isb = 1
    ... | no nisb = 0
    count-B (suc n) with is-B (fun← cn (suc n))
    ... | yes isb = suc (count-B n)
    ... | no nisb = count-B n

    count-A : ℕ → ℕ
    count-A zero with is-A (fun← cn zero)
    ... | yes isb = 1
    ... | no nisb = 0
    count-A (suc n) with is-A (fun← cn (suc n))
    ... | yes isb = suc (count-A n)
    ... | no nisb = count-A n

    ¬isA∧isB : (y : C ) →  Is A C (λ x → g ( f x)) y → ¬ Is B C g y → ⊥
    ¬isA∧isB y isa nisb = ⊥-elim ( nisb record { a = f (Is.a isa) ; fa=c = lem } ) where
         lem : g (f (Is.a isa)) ≡ y
         lem = begin
           g (f (Is.a isa))  ≡⟨ Is.fa=c isa  ⟩
           y ∎ where
             open ≡-Reasoning

    ca≤cb0 : (n : ℕ) → count-A n ≤ count-B n
    ca≤cb0 zero with is-A (fun← cn zero) | is-B (fun← cn zero)
    ... | yes isA | yes isB = ≤-refl
    ... | yes isA | no nisB = ⊥-elim ( ¬isA∧isB _ isA nisB )
    ... | no nisA | yes isB = px≤x
    ... | no nisA | no nisB = ≤-refl
    ca≤cb0 (suc n) with is-A (fun← cn (suc n)) | is-B (fun← cn (suc n))
    ... | yes isA | yes isB = s≤s (ca≤cb0 n)
    ... | yes isA | no nisB = ⊥-elim ( ¬isA∧isB _ isA nisB )
    ... | no nisA | yes isB = ≤-trans (ca≤cb0 n) px≤x
    ... | no nisA | no nisB = ca≤cb0 n

    --  (c n)  is
    --     fun→ c, where c contains all "a" less than n
    --     (i n : ℕ) → i < suc n → fun→ cn (g (f (fun← an i))) < suc (c n)
    c : (n : ℕ) → ℕ
    c zero = fun→ cn (g (f (fun← an zero)))
    c (suc n) = max (fun→ cn (g (f (fun← an (suc n))))) (c n)

    c< : (i : ℕ) → fun→ cn (g (f (fun← an i))) ≤ c i
    c< zero = ≤-refl
    c< (suc i) = x≤max _ _

    c-mono1 : (i : ℕ) → c i ≤ c (suc i)
    c-mono1 i = y≤max _ _
    c-mono : (i j : ℕ ) → i ≤ j → c i ≤ c j
    c-mono i j i≤j with ≤-∨ i≤j
    ... | case1 refl = ≤-refl
    c-mono zero (suc j) z≤n | case2 lt = ≤-trans (c-mono zero j z≤n ) (c-mono1 j) 
    c-mono (suc i) (suc j) (s≤s i≤j) | case2 (s≤s lt) = ≤-trans (c-mono (suc i) j lt ) (c-mono1 j)

    inject-cgf : {i j : ℕ} → fun→ cn (g (f (fun← an i))) ≡ fun→ cn (g (f (fun← an j))) → i ≡ j
    inject-cgf {i} {j} eq = bi-inject← an (InjectiveF.inject fi (InjectiveF.inject gi ( bi-inject→ cn eq )))

    ani : (i : ℕ) → ℕ
    ani i = fun→ cn (g (f (fun← an i)))

    ncfi = λ n → (fun→ cn (g (f (fun← an n) )))
    cfi = λ n → (g (f (fun← an n) ))

    clist : (n : ℕ) → List C
    clist 0 = fun← cn 0 ∷ []
    clist (suc n) = fun← cn (suc n) ∷ clist n

    clist-more : {i j : ℕ} → i ≤ j → {c : C} →  Any (_≡_ c) (clist i) →  Any (_≡_ c) (clist j)
    clist-more {zero} {zero} z≤n a = a
    clist-more {zero} {suc n} i≤n a = there (clist-more {zero} {n} z≤n a)
    clist-more {suc i} {suc n} (s≤s le) {c} (there a) = there (clist-more {i} {n} le a)
    clist-more {suc i} {suc n} (s≤s le) {c} (here px) with ≤-∨ le
    ... | case1 refl = here px
    ... | case2 lt = there (clist-more {suc i} {n} lt {c} (here px) )

    clist-any : (n i : ℕ) → i ≤ n → Any (_≡_ (g (f (fun← an i)))) (clist (c n))
    clist-any n i i≤n = clist-more (c-mono _ _ i≤n) (lem00 (c i) (c< i))   where
        lem00 : (j : ℕ ) → fun→ cn (g (f (fun← an i))) ≤ j → Any (_≡_ (g (f (fun← an i)))) (clist j)
        lem00 0 f≤j with  ≤-∨ f≤j
        ... | case1 eq = here ( trans (sym (fiso← cn _)) ( cong (fun← cn) eq ))
        ... | case2 le = ⊥-elim (nat-≤> z≤n le )
        lem00 (suc j) f≤j with  ≤-∨ f≤j
        ... | case1 eq = here ( trans (sym (fiso← cn _)) ( cong (fun← cn) eq ))
        ... | case2 (s≤s le) = there (lem00 j le)

    ca-list : List C → ℕ
    ca-list [] = 0
    ca-list (h ∷ t) with is-A h
    ... | yes _ = suc (ca-list t)
    ... | no _ = ca-list t

    ca-list=count-A : (n : ℕ) → ca-list (clist n) ≡ count-A n
    ca-list=count-A n = lem02 n (clist n) refl  where
        lem02 : (n : ℕ) → (cl : List C) → cl ≡ clist n → ca-list cl ≡ count-A n
        lem02 zero [] ()
        lem02 zero (h ∷ t) refl with is-A (fun← cn zero)
        ... | yes _ = refl
        ... | no _ = refl
        lem02 (suc n) (h ∷ t) refl with is-A (fun← cn (suc n)) 
        ... | yes _ = cong suc (lem02 n t refl)
        ... | no _ = lem02 n t refl

    --  remove (ani i) from clist (c n)
    --
    a-list : (i : ℕ) → (cl : List C) → Any (_≡_ (g (f (fun← an i)))) cl → List C
    a-list i (_ ∷ t) (here px) = t
    a-list i (h ∷ t) (there a) = h ∷ ( a-list i t a )

    --  count of a in a-list is one step reduced
    --
    a-list-ca : (i : ℕ) → (cl : List C) → (a : Any (_≡_ (g (f (fun← an i)))) cl ) 
        → suc (ca-list (a-list i cl a)) ≡ ca-list cl
    a-list-ca i cl a = lem03 i cl _ a refl where
         lem03 : (i : ℕ) → (cl cal : List C) → (a : Any (_≡_ (g (f (fun← an i)))) cl )  → cal ≡  (a-list i cl a) → suc (ca-list cal)  ≡ ca-list cl
         lem03 i (h ∷ t) (h1 ∷ t1) (here px) refl with is-A h
         ... | yes _ = refl
         ... | no nisa = ⊥-elim ( nisa record { a = _ ; fa=c = px } )
         lem03 i (h ∷ t) (h ∷ t1) (there ah) refl with is-A h
         ... | yes y = cong suc (lem03 i t t1 ah refl)
         ... | no _ = lem03 i t t1 ah refl
         lem03 i (x ∷ []) [] (here px) refl with is-A x
         ... | yes y = refl
         ... | no nisa = ⊥-elim ( nisa record { a = _ ; fa=c = px } )

    --  reduced list still have all ani j < i
    --
    a-list-any : (i : ℕ) → (cl : List C) → (a : Any (_≡_ (g (f (fun← an i)))) cl ) 
         → (j : ℕ) → j < i  → Any (_≡_ (g (f (fun← an j)))) cl  → Any (_≡_ (g (f (fun← an j)))) (a-list i cl a) 
    a-list-any i cl a j j<i b = lem03 i cl _ a refl j j<i b where
         lem03 : (i : ℕ) → (cl cal : List C) → (a : Any (_≡_ (g (f (fun← an i)))) cl )  
             → cal ≡  (a-list i cl a) 
             → (j : ℕ) → j < i  → Any (_≡_ (g (f (fun← an j)))) cl  → Any (_≡_ (g (f (fun← an j)))) cal
         lem03 i (h ∷ t) cal (here px) eq j j<i (here px₁) = ⊥-elim ( nat-≡< 
             (  bi-inject← an (InjectiveF.inject fi (InjectiveF.inject gi (trans px₁ (sym px))))) j<i )
         lem03 i (h ∷ t) cal (here px) eq j j<i (there b) = subst (λ k → Any (_≡_ (g (f (fun← an j)))) k) (sym eq) b
         lem03 i (h ∷ t) cal (there a) eq j j<i (here px) = subst (λ k → Any (_≡_ (g (f (fun← an j)))) k) (sym eq) (here px)
         lem03 i (h ∷ t) (h1 ∷ cal) (there a) refl j j<i (there b) = there (lem03 i t cal a refl j j<i b)

    any-cl : (i : ℕ) → (cl : List C) → Set
    any-cl i cl = (j : ℕ) → j ≤ i → Any (_≡_ (g (f (fun← an j)))) cl

    n<ca-list : (n : ℕ) → n < ca-list (clist (c n))
    n<ca-list n = lem30 n (clist (c n)) ≤-refl (λ j le  → clist-any n j le ) where
         --
         --  we have ANY i on i ≤ n, so we can remove n element from clist (c n)
         --  induction on n is no good, because (ani (suc n)) may happen in clist (c n)
         --  so we cannot recurse on n<ca-list itself.
         --

         del : (i : ℕ) → (cl : List C) → any-cl i cl → List C   -- del 0 contains ani 0
         del i cl a = a-list i cl (a i ≤-refl)  
         del-any : (i : ℕ) → (cl : List C) → (a : any-cl (suc i) cl)  → any-cl i (del (suc i) cl a )
         del-any i cl a j le = lem41 cl (del (suc i) cl a ) (a (suc i) ≤-refl ) (a j (≤-trans le a≤sa) ) refl where
            lem41 : (cl dl : List C) 
                 → (ai : Any (_≡_ (g (f (fun← an (suc i))))) cl)
                 → (aj : Any (_≡_ (g (f (fun← an j)))) cl) 
                 → dl ≡ a-list (suc i) cl ai →   Any (_≡_ (g (f (fun← an j)))) dl
            lem41 (h ∷ t) y (here px) (here px₁) eq = ⊥-elim ( nat-≡< 
                 (  bi-inject← an (InjectiveF.inject fi (InjectiveF.inject gi (trans px₁ (sym px))))) (x≤y→x<sy le) )
            lem41 (h ∷ t) y (here px) (there b0) eq = subst (λ k →  Any (_≡_ (g (f (fun← an j)))) k) (sym eq) b0
            lem41 (h ∷ t) y (there a0) (here px) refl = here px
            lem41 (h ∷ t) (x ∷ y) (there a0) (there b0) refl = there (lem41 t (a-list (suc i) t a0) a0 b0 refl)

         del-ca : (i : ℕ) → (cl : List C) → (a : any-cl i cl  )
              → suc (ca-list (del i cl a)) ≡ ca-list cl
         del-ca i cl a = a-list-ca i cl (a i ≤-refl) 

         lem30 : (i : ℕ) → (cl : List C) → (i≤n : i ≤ n) → (a : any-cl i cl) → i < ca-list cl
         lem30 0 cl i≤n a = begin
             1 ≤⟨ s≤s z≤n ⟩ 
             suc (ca-list (del 0 cl a) )  ≡⟨ del-ca 0 cl a ⟩
             ca-list cl ∎ where
                open ≤-Reasoning
         lem30 (suc i) cl i≤n a = begin
            suc (suc i)   ≤⟨ s≤s (lem30 i _ (≤-trans a≤sa i≤n) (del-any i cl a) ) ⟩ 
            suc (ca-list (del (suc i) cl a))  ≡⟨ del-ca (suc i) cl a ⟩ 
            ca-list cl ∎ where
                open ≤-Reasoning

    record maxAC (n : ℕ) : Set where
       field
           ac : ℕ
           n<ca : n < count-A ac

    lem02 : (n : ℕ) → maxAC n
    lem02 n = record { ac = c n ; n<ca = subst (λ k → n < k) (ca-list=count-A (c n)) (n<ca-list n ) }

    --
    -- countB record create ℕ → B and its injection
    --
    record CountB (n : ℕ) : Set where
       field
          b : B
          cb : ℕ
          b=cn : fun← cn cb ≡ g b
          cb=n : count-B cb ≡ suc n
          cb-inject : (cb1 : ℕ) → Is B C g (fun← cn cb1) → count-B cb ≡ count-B cb1 → cb ≡ cb1

    count-B-mono : {i j : ℕ} → i ≤ j → count-B i ≤ count-B j
    count-B-mono {i} {j} i≤j with ≤-∨ i≤j
    ... | case1 refl = ≤-refl
    ... | case2 i<j = lem00 _ _ i<j where
         lem00 : (i j : ℕ) → i < j → count-B i ≤ count-B j
         lem00 i (suc j) (s≤s i<j) = ≤-trans (count-B-mono i<j) (lem01 j) where
             lem01 : (j : ℕ) → count-B j ≤ count-B (suc j)
             lem01 zero with is-B (fun← cn (suc zero))
             ... | yes isb = refl-≤s
             ... | no nisb = ≤-refl
             lem01 (suc n) with is-B (fun← cn (suc (suc n)))
             ... | yes isb = refl-≤s
             ... | no nisb = ≤-refl

    lem01 : (n i : ℕ) → suc n ≤ count-B i → CountB n
    lem01 n i le = lem09 i (count-B i) le refl where
        -- injection of count-B
        ---
        lem06 : (i j : ℕ ) → Is B C g (fun← cn i) → Is B C g (fun← cn j) → count-B i ≡ count-B j → i ≡ j
        lem06 i j bi bj eq = lem08  where
            lem20 : (i j : ℕ) → i < j →  Is B C g (fun← cn i) → Is B C g (fun← cn j) → count-B j ≡ count-B i → ⊥
            lem20 zero (suc j) i<j bi bj le with  is-B (fun← cn 0) | inspect count-B 0 | is-B (fun← cn (suc j)) | inspect count-B (suc j)
            ... | no nisc  | _ | _ | _ = ⊥-elim (nisc bi)
            ... |  yes _ | _ | no nisc | _  = ⊥-elim (nisc bj)
            ... | yes _ | record { eq = eq1 } | yes _ | record { eq = eq2 } = ⊥-elim ( nat-≤> lem25 a<sa) where
                 lem22 : 1 ≡ count-B 0
                 lem22 with is-B (fun← cn 0) | inspect count-B 0
                 ... | yes _ | record { eq = eq1 } = refl
                 ... | no nisa | _ = ⊥-elim ( nisa bi )
                 lem24 : count-B j ≡ 0
                 lem24 = cong pred le
                 lem25 : 1 ≤ 0
                 lem25 = begin
                    1 ≡⟨ lem22 ⟩
                    count-B 0 ≤⟨ count-B-mono {0} {j} z≤n ⟩
                    count-B j ≡⟨ lem24 ⟩
                    0 ∎ where open ≤-Reasoning
            lem20 (suc i) zero () bi bj le
            lem20 (suc i) (suc j) (s≤s i<j) bi bj le = ⊥-elim ( nat-≡< lem24 lem21 ) where
                 --
                 --                    i  <     suc i  ≤    j
                 --    cb i <  suc (cb i) < cb (suc i) ≤ cb j
                 --    suc (cb i) ≡ suc (cb j) → cb i ≡ cb j
                 lem22 : suc (count-B i) ≡ count-B (suc i)
                 lem22 with is-B (fun← cn (suc i)) | inspect count-B (suc i)
                 ... | yes _ | record { eq = eq1 } = refl
                 ... | no nisa | _ = ⊥-elim ( nisa bi )
                 lem23 : suc (count-B j) ≡ count-B (suc j)
                 lem23 with is-B (fun← cn (suc j)) | inspect count-B (suc j)
                 ... | yes _ | record { eq = eq1 } = refl
                 ... | no nisa | _ = ⊥-elim ( nisa bj )
                 lem24 : count-B i ≡ count-B j
                 lem24 with  is-B (fun← cn (suc i)) | inspect count-B (suc i) | is-B (fun← cn (suc j)) | inspect count-B (suc j)
                 ... | no nisc  | _ | _ | _ = ⊥-elim (nisc bi)
                 ... |  yes _ | _ | no nisc | _  = ⊥-elim (nisc bj)
                 ... | yes _ | record { eq = eq1 } | yes _ | record { eq = eq2 } = sym (cong pred le)
                 lem21 : suc (count-B i) ≤ count-B j
                 lem21 = begin
                     suc (count-B i) ≡⟨ lem22 ⟩
                     count-B (suc i) ≤⟨ count-B-mono i<j ⟩
                     count-B j ∎ where
                        open ≤-Reasoning
            lem08 : i ≡ j
            lem08 with <-cmp i j
            ... | tri< a ¬b ¬c = ⊥-elim ( lem20 i j a bi bj (sym eq) )
            ... | tri≈ ¬a b ¬c = b
            ... | tri> ¬a ¬b c₁ = ⊥-elim ( lem20 j i c₁ bj bi eq )

        lem07 : (n i : ℕ) → count-B i ≡ suc n → CountB n
        lem07 n 0 eq with is-B (fun← cn 0) | inspect count-B 0
        ... | yes isb | record { eq = eq1 } = record { b = Is.a isb ; cb = 0 ; b=cn = sym (Is.fa=c isb) ; cb=n = trans eq1 eq 
                ; cb-inject = λ cb1 iscb1 cb1eq → lem12 cb1 iscb1 (subst (λ k → k ≡ count-B cb1) eq1 cb1eq)   } where
            lem12 : (cb1 : ℕ) →  Is B C g (fun← cn cb1)  → 1 ≡ count-B cb1 → 0 ≡ cb1
            lem12 cb1 iscb1 cbeq = lem06 0 cb1 isb iscb1 (trans eq1 cbeq) 
        ... | no nisb | record { eq = eq1 } = ⊥-elim ( nat-≡< eq (s≤s z≤n ) )
        lem07 n (suc i) eq with is-B (fun← cn (suc i)) | inspect count-B (suc i)
        ... | yes isb | record { eq = eq1 } = record { b = Is.a isb ; cb = suc i ; b=cn = sym (Is.fa=c isb) ; cb=n = trans eq1 eq
                 ; cb-inject = λ cb1 iscb1 cb1eq → lem12 cb1 iscb1 (subst (λ k → k ≡ count-B cb1) eq1 cb1eq)   } where
            lem12 : (cb1 : ℕ) → Is B C g (fun← cn cb1) → suc (count-B i)  ≡ count-B cb1 → suc i ≡ cb1
            lem12 cb1 iscb1 cbeq = lem06 (suc i) cb1 isb iscb1 (trans eq1 cbeq)
        ... | no nisb | record { eq = eq1 } = lem07 n i  eq

        -- starting from 0, if count B i ≡ suc n, this is it

        lem09 : (i j : ℕ) → suc n ≤ j → j ≡ count-B i →  CountB n
        lem09 0 (suc j) (s≤s le) eq with ≤-∨ (s≤s le)
        ... | case1 eq1 = lem07 n 0 (sym (trans eq1 eq ))
        ... | case2 (s≤s lt) with is-B (fun← cn 0) | inspect count-B 0
        ... | yes isb | record { eq = eq1 } = ⊥-elim ( nat-≤> (≤-trans (s≤s lt) (refl-≤≡ eq) ) (s≤s (s≤s z≤n)) )
        ... | no nisb | record { eq = eq1 } = ⊥-elim (nat-≡< (sym eq) (s≤s z≤n))
        lem09 (suc i) (suc j) (s≤s le) eq with ≤-∨ (s≤s le)
        ... | case1 eq1 = lem07 n (suc i) (sym (trans eq1 eq ))
        ... | case2 (s≤s lt) with is-B (fun← cn (suc i)) | inspect count-B (suc i)
        ... | yes isb | record { eq = eq1 } = lem09 i j lt (cong pred eq)
        ... | no nisb | record { eq = eq1 } = lem09 i (suc j) (≤-trans lt a≤sa) eq

    bton : B → ℕ
    bton b = pred (count-B (fun→ cn (g b)))

    ntob : (n : ℕ) → B
    ntob n = CountB.b (lem01 n (maxAC.ac (lem02 n)) (≤-trans (maxAC.n<ca (lem02 n)) (ca≤cb0 (maxAC.ac (lem02 n))) ))

    biso : (n : ℕ) → bton (ntob n) ≡ n
    biso n = begin  
        bton (ntob n) ≡⟨ refl ⟩
        pred (count-B (fun→ cn (g (CountB.b CB)))) ≡⟨ sym ( cong (λ k → pred (count-B (fun→ cn k))) ( CountB.b=cn CB)) ⟩
        pred (count-B (fun→ cn (fun← cn (CountB.cb CB)))) ≡⟨ cong (λ k → pred (count-B k)) (fiso→ cn _) ⟩
        pred (count-B (CountB.cb CB)) ≡⟨ cong pred (CountB.cb=n CB) ⟩
        pred (suc n) ≡⟨ refl ⟩
        n ∎ where
           open ≡-Reasoning
           CB  = lem01 n (maxAC.ac (lem02 n)) (≤-trans (maxAC.n<ca (lem02 n)) (ca≤cb0 (maxAC.ac (lem02 n))) )

    --
    -- uniqueness of ntob is proved by injection
    --
    biso1 : (b : B) → ntob (bton b) ≡ b
    biso1 b with count-B (fun→ cn (g b)) | inspect count-B (fun→ cn (g b)) 
    ... | zero  | record { eq = eq1 } = ⊥-elim ( nat-≡< (sym lem20) (lem21 _ refl) ) where
        lem20 : count-B (fun→ cn (InjectiveF.f gi b)) ≡ zero
        lem20 = eq1
        lem21 : (i : ℕ) → i ≡ fun→ cn (InjectiveF.f gi b) → 0 < count-B  i
        lem21 0 eq with is-B (fun← cn 0) | inspect count-B 0
        ... | yes isb | record { eq = eq1 } = ≤-refl
        ... | no nisb | record{ eq = eq1 } = ⊥-elim ( nisb record { a = b ; fa=c = trans (sym (fiso← cn _)) (cong (fun← cn) (sym eq)) } )
        lem21 (suc i) eq with is-B (fun← cn (suc i)) | inspect count-B (suc i)
        ... | yes isb | record{ eq = eq2 } = s≤s z≤n
        ... | no nisb | record{ eq = eq2 } = ⊥-elim ( nisb record { a = b ; fa=c = trans (sym (fiso← cn _)) (cong (fun← cn) (sym eq)) } )
    ... | suc n | record { eq = eq1 } = begin 
           CountB.b CB  ≡⟨ InjectiveF.inject gi (bi-inject→ cn (begin
              fun→ cn (g (CountB.b CB)) ≡⟨ cong (fun→ cn) (sym (CountB.b=cn CB)) ⟩
              fun→ cn (fun← cn (CountB.cb CB)) ≡⟨ fiso→ cn _ ⟩
              CountB.cb CB  ≡⟨ CountB.cb-inject CB _ record { a = b ; fa=c = sym (fiso← cn _) }  (trans (CountB.cb=n CB) (sym eq1)) ⟩
              fun→ cn (InjectiveF.f gi b) ∎ ))  ⟩
           b  ∎  where
           open ≡-Reasoning
           CB  = lem01 n (maxAC.ac (lem02 n)) (≤-trans (maxAC.n<ca (lem02 n)) (ca≤cb0 (maxAC.ac (lem02 n))) )

bi-∧ : {A B C D : Set} → Bijection A B → Bijection C D → Bijection (A ∧ C) (B ∧ D)
bi-∧ {A} {B} {C} {D} ab cd = record {
       fun←  = λ x → ⟪ fun←  ab (proj1 x) , fun←  cd (proj2 x) ⟫
     ; fun→  = λ n → ⟪ fun→  ab (proj1 n) , fun→  cd (proj2 n) ⟫
     ; fiso← = lem0
     ; fiso→ = lem1
  } where
      open Bijection
      lem0 : (x : A ∧ C) → ⟪ fun← ab (fun→ ab (proj1 x)) , fun← cd (fun→ cd (proj2 x)) ⟫ ≡ x
      lem0 ⟪ x , y ⟫ = cong₂ ⟪_,_⟫ (fiso← ab x) (fiso← cd y)
      lem1 : (x : B ∧ D) → ⟪ fun→ ab (fun← ab (proj1 x)) , fun→ cd (fun← cd (proj2 x)) ⟫ ≡ x
      lem1 ⟪ x , y ⟫ = cong₂ ⟪_,_⟫ (fiso→ ab x) (fiso→ cd y)


LM1 : (A : Set ) → Bijection (List A ) ℕ → Bijection (List A ∧ List Bool) ℕ
LM1 A Ln = bi-trans (List A ∧ List Bool) (ℕ ∧ ℕ)  ℕ (bi-∧ Ln (bi-sym _ _ LBℕ) ) (bi-sym _ _ nxn)

open import Data.List.Properties
open import Data.Maybe.Properties

---   ℕ ⊆ List A ⊆ List (Maybe A) ⊆ List A ∧ List Bool ⊆ ℕ

LMℕ : (A : Set ) → Bijection (List A) ℕ → Bijection (List (Maybe A)) ℕ
LMℕ A Ln = Countable-Bernstein (List A) (List (Maybe A)) (List A ∧ List Bool) Ln (LM1 A Ln)  fi gi dec0 dec1 where
   f : List A → List (Maybe A)
   f [] = []
   f (x ∷ t) = just x ∷ f t
   f-inject : {x y : List A} → f x ≡ f y → x ≡ y
   f-inject {[]} {[]} refl = refl
   f-inject {x ∷ xt} {y ∷ yt} eq = cong₂ (λ j k → j ∷ k ) (just-injective (∷-injectiveˡ eq)) (f-inject (∷-injectiveʳ eq) )
   g : List (Maybe A) → List A ∧ List Bool
   g [] = ⟪ [] , [] ⟫
   g (just h ∷ t)  = ⟪ h ∷ proj1 (g t) , true  ∷ proj2 (g t) ⟫
   g (nothing ∷ t) = ⟪     proj1 (g t) , false ∷ proj2 (g t) ⟫
   g⁻¹ :  List A ∧ List Bool → List (Maybe A)
   g⁻¹ ⟪ [] , [] ⟫ = []
   g⁻¹ ⟪ x ∷ xt , [] ⟫ = just x ∷  g⁻¹ ⟪ xt , [] ⟫
   g⁻¹ ⟪ [] , true ∷ y ⟫ = []
   g⁻¹ ⟪ x ∷ xt , true ∷ yt ⟫ = just x ∷ g⁻¹ ⟪ xt , yt ⟫
   g⁻¹ ⟪ [] , false ∷ y ⟫ = nothing ∷ g⁻¹ ⟪ [] , y ⟫
   g⁻¹ ⟪ x ∷ x₁ , false ∷ y ⟫ = nothing ∷ g⁻¹ ⟪ x ∷ x₁ , y ⟫
   g-iso : {x : List (Maybe A)} → g⁻¹ (g x) ≡ x
   g-iso {[]} = refl
   g-iso {just x ∷ xt} = cong ( λ k → just x ∷ k) ( g-iso )
   g-iso {nothing ∷ []} = refl
   g-iso {nothing ∷ just x ∷ xt} = cong (λ k → nothing ∷ k ) ( g-iso {_} )
   g-iso {nothing ∷ nothing ∷ xt} with g-iso {nothing ∷ xt}
   ... | t = trans (lemma01 (proj1 (g xt)) (proj2 (g xt)) ) ( cong (λ k → nothing ∷ k ) t ) where
         lemma01 : (x : List A) (y : List Bool ) →  g⁻¹ ⟪ x , false ∷ false ∷ y ⟫ ≡ nothing ∷ g⁻¹ ⟪ x , false ∷ y ⟫
         lemma01 [] y = refl
         lemma01 (x ∷ x₁) y = refl
   g-inject : {x y : List (Maybe A)} → g x ≡ g y → x ≡ y
   g-inject {x} {y} eq = subst₂ (λ j k → j ≡ k ) g-iso g-iso (cong g⁻¹ eq )
   fi : InjectiveF (List A) (List (Maybe A))
   fi = record { f = f ; inject = f-inject  }
   gi : InjectiveF (List (Maybe A)) (List A ∧ List Bool )
   gi = record { f = g ; inject = g-inject }
   dec0 : (c : List A ∧ List Bool) → Dec (Is (List A) (List A ∧ List Bool) (λ x → g (f x)) c)
   dec0 ⟪ [] , [] ⟫ = yes record { a = [] ; fa=c = refl }
   dec0 ⟪ h ∷ t , [] ⟫ = no ( lem00 ) where
        lem00 : Is (List A) (List A ∧ List Bool) (λ x → g (f x)) ⟪ h ∷ t , [] ⟫ → ⊥
        lem00 record { a = [] ; fa=c = () }
        lem00 record { a = (x ∷ a) ; fa=c = () }
   dec0 ⟪ [] , true ∷ bt ⟫ = no lem00 where
        lem00 : Is (List A) (List A ∧ List Bool) (λ x → g (f x)) ⟪ [] , true ∷ bt ⟫ → ⊥
        lem00 record { a = [] ; fa=c = () }
   dec0 ⟪ [] , false ∷ bt ⟫ = no lem00 where
        lem00 : Is (List A) (List A ∧ List Bool) (λ x → g (f x)) ⟪ [] , false ∷ bt ⟫ → ⊥
        lem00 record { a = [] ; fa=c = () }
   dec0 ⟪ h ∷ t , (true ∷ bt) ⟫ with dec0 ⟪ t , bt ⟫
   ... | yes y = yes record { a = h ∷ Is.a y ; fa=c = cong₂ (λ j k → ⟪ h ∷ j , true ∷ k ⟫ ) (cong proj1 (Is.fa=c y)) (cong proj2 (Is.fa=c y))  }
   ... | no n = no lem00  where
        lem00 : ¬ Is (List A) (List A ∧ List Bool) (λ x → g (f x)) ⟪ h ∷ t , true ∷ bt ⟫
        lem00 record { a = (x ∷ a) ; fa=c = refl } = ⊥-elim ( n record { a = a ; fa=c = refl } )
   dec0 ⟪ (h ∷ t) , (false ∷ bt) ⟫ = no lem00 where
        lem00 :  ¬ Is (List A) (List A ∧ List Bool) (λ x → g (f x)) ⟪ h ∷ t , false ∷ bt ⟫
        lem00 record { a = [] ; fa=c = () }
        lem00 record { a = (x ∷ a) ; fa=c = () }
   dec1 : (c : List A ∧ List Bool) → Dec (Is (List (Maybe A)) (List A ∧ List Bool) g c)
   dec1 ⟪ [] , [] ⟫ = yes record { a = [] ; fa=c = refl }
   dec1 ⟪ h ∷ t , [] ⟫ = no lem00 where
        lem00 :  ¬ Is (List (Maybe A)) (List A ∧ List Bool) g ⟪ h ∷ t , [] ⟫
        lem00 record { a = (just x ∷ a) ; fa=c = () }
        lem00 record { a = (nothing ∷ a) ; fa=c = () }
   dec1 ⟪ [] , true ∷ bt ⟫ = no lem00 where
        lem00 : ¬ Is (List (Maybe A)) (List A ∧ List Bool) g ⟪ [] , true ∷ bt ⟫
        lem00 record { a = (just x ∷ a) ; fa=c = () }
        lem00 record { a = (nothing ∷ a) ; fa=c = () }
   dec1 ⟪ [] , false ∷ bt ⟫ with dec1 ⟪ [] , bt ⟫
   ... | yes record { a = a ; fa=c = fa=c } = yes record { a = nothing ∷ a ; fa=c = cong₂ (λ j k → ⟪ j , false ∷ k ⟫) (cong proj1 fa=c) (cong proj2 fa=c) }
   ... | no n = no lem00 where
        lem00 : ¬ Is (List (Maybe A)) (List A ∧ List Bool) g ⟪ [] , false ∷ bt ⟫
        lem00 record { a = (nothing ∷ a) ; fa=c = eq } = n record { a = a ; fa=c = cong₂ (λ j k → ⟪ j , k ⟫) (cong proj1 eq) lem01 } where
            lem01 : proj2 (g a) ≡ bt
            lem01 with cong proj2 eq
            ... | refl = refl
   dec1 ⟪ h ∷ t , true ∷ bt ⟫ with dec1 ⟪ t , bt ⟫
   ... | yes y = yes record { a = just h ∷ Is.a y ; fa=c = cong₂ (λ j k → ⟪ h ∷ j , true ∷ k ⟫ ) (cong proj1 (Is.fa=c y)) (cong proj2 (Is.fa=c y))   }
   ... | no n = no lem00 where
        lem00 : ¬ Is (List (Maybe A)) (List A ∧ List Bool) g ⟪ h ∷ t , true ∷ bt ⟫
        lem00 record { a = (just x ∷ a) ; fa=c = refl } = n record { a = a ; fa=c = refl } 
   dec1 ⟪ h ∷ t , false ∷ bt ⟫  with dec1 ⟪ h ∷ t , bt ⟫
   ... | yes record { a = a ; fa=c = fa=c } = yes record { a = nothing ∷ a ; fa=c = cong₂ (λ j k → ⟪ j , false ∷ k ⟫) (cong proj1 fa=c) (cong proj2 fa=c) }
   ... | no n = no lem00 where
        lem00 : ¬ Is (List (Maybe A)) (List A ∧ List Bool) g ⟪ h ∷ t , false ∷ bt ⟫
        lem00 record { a = (nothing ∷ a) ; fa=c = eq } = n record { a = a ; fa=c = cong₂ (λ j k → ⟪ j , k ⟫) (cong proj1 eq) lem01 } where
            lem01 : proj2 (g a) ≡ bt
            lem01 with cong proj2 eq
            ... | refl = refl

--
--  (     Bool ∷      Bool ∷ [] )    (      Bool ∷      Bool ∷ []   )  (      Bool ∷ [] )
--        true ∷      true ∷ false ∷        true ∷      true ∷ false ∷        true ∷ []

-- LMℕ A Ln = Countable-Bernstein (List A) (List (Maybe A)) (List A ∧ List Bool) Ln (LM1 A Ln)  fi gi dec0 dec1 where
--    someday ...

LBBℕ : Bijection (List (List Bool)) ℕ
LBBℕ = Countable-Bernstein (List Bool ∧ List Bool) (List (List Bool)) (List Bool ∧ List Bool ) (LM1 Bool (bi-sym _ _ LBℕ)) (LM1 Bool (bi-sym _ _ LBℕ))  
        ? ? ? ? where

    atob : List (List Bool) →  List Bool ∧ List Bool 
    atob [] = ⟪ [] , [] ⟫
    atob ( [] ∷  t ) = ⟪ false  ∷ proj1 ( atob t ) , false ∷ proj2 ( atob t ) ⟫
    atob ( (h ∷ t1) ∷ t ) = ⟪ h ∷ proj1 ( atob t ) , true  ∷ proj2 ( atob t ) ⟫

    btoa : List Bool ∧ List Bool → List (List Bool) 
    btoa ⟪ [] , _ ⟫ = []
    btoa ⟪ _ ∷ _  , [] ⟫ = []
    btoa ⟪ _ ∷ t0 ,  false ∷ t1  ⟫ = [] ∷ btoa ⟪ t0 , t1 ⟫ 
    btoa ⟪ h ∷ t0 ,  true  ∷ t1  ⟫ with btoa ⟪ t0 , t1 ⟫
    ... | [] = ( h ∷ [] ) ∷ []
    ... | x ∷ y = (h ∷ x ) ∷ y

Lℕ=ℕ : Bijection (List ℕ) ℕ
Lℕ=ℕ = record {
       fun→  = λ x → ?
     ; fun←  = λ n → ?
     ; fiso→ = ?
     ; fiso← = ?
     }
