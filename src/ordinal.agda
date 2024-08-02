{-# OPTIONS --cubical-compatible --safe #-}

open import Level renaming ( zero to Zero ; suc to Suc ; _⊔_ to _n⊔_ )
module ordinal where

open import logic
open import nat
open import Data.Nat
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Definitions
open import Data.Nat.Properties as NP
open import Relation.Nullary
open import Relation.Binary.Core

----
--
-- Countable Ordinals
--

record Ordinal : Set where
   constructor ordinal
   field
     lv : ℕ
     ord : ℕ

open Ordinal
open  _∧_

o∅ :  Ordinal
o∅  = record { lv = zero ; ord = zero }

osuc : ( x : Ordinal ) → Ordinal
osuc record { lv = lx ; ord = ox } = record { lv = lx ; ord = suc ox }

_o<_ : Ordinal  → Ordinal → Set
_o<_ x y =  (lv x < lv y) ∨  ((lv x ≡ lv y) ∧ (ord x < ord y))

<-osuc : { x : Ordinal  } → x o< osuc x
<-osuc {x} = case2 ⟪ refl , a<sa ⟫

o<¬≡ : { ox oy : Ordinal } → ox ≡ oy  → ox o< oy  → ⊥
o<¬≡ {ox} {.ox} refl (case1 lt) = ⊥-elim ( nat-<≡  lt )
o<¬≡ {ox} {.ox} refl (case2 x) = ⊥-elim ( nat-<≡  (proj2 x) )

¬x<0 : { x  : Ordinal } → ¬ ( x o< o∅  )
¬x<0 {x} (case1 s) = nat-≤> z≤n s
¬x<0 {x} (case2 s) = nat-≤> z≤n (proj2  s)

trio< :  Trichotomous  _≡_  _o<_
trio< a b with <-cmp (lv a) (lv b)
... | tri< a₁ ¬b ¬c = tri<  (case1 a₁)  (λ eq → ¬b (cong lv eq) )  tr00 where
   tr00 : ¬ (suc (lv b) ≤ lv a) ∨ ((lv b ≡ lv a) ∧ (suc (ord b) ≤ ord a))
   tr00 (case1 x) = ¬c x
   tr00 (case2 x) = ¬b (sym (proj1 x))
... | tri> ¬a ¬b c = tri>  tr00 (λ eq → ¬b (cong lv eq) ) (case1 c)  where
   tr00 : ¬ (suc (lv a) ≤ lv b) ∨ ((lv a ≡ lv b) ∧ (suc (ord a) ≤ ord b))
   tr00 (case1 x) = ¬a x
   tr00 (case2 x) = ¬b ((proj1 x))
... | tri≈ ¬a refl ¬c with <-cmp (ord a) (ord b)
... | tri< a₁ ¬b ¬c₁ = tri<  (case2 ⟪ refl , a₁ ⟫)  (λ eq → ¬b (cong ord eq) )  tr00 where
   tr00 : ¬ (suc (lv b) ≤ lv b) ∨ ((lv b ≡ lv b) ∧ (suc (ord b) ≤ (ord a) ))
   tr00 (case1 x) = ⊥-elim ( ¬a≤a {lv b} x )
   tr00 (case2 ⟪ eq , lt ⟫) = nat-<> lt a₁
... | tri≈ ¬a₁ refl ¬c₁ = tri≈  tr00 refl tr01  where
   tr00 :  ¬ (suc (lv b) ≤ lv b) ∨ ((lv b ≡ lv b) ∧ (suc (ord b) ≤ ord b))
   tr00 (case1 x) = ¬a x
   tr00 (case2 x) = ¬a₁ (proj2 x)
   tr01 : ¬ (suc (lv b) ≤ lv b) ∨ ((lv b ≡ lv b) ∧ (suc (ord b) ≤ ord b))
   tr01 (case1 x) = ¬c x
   tr01 (case2 x) = ¬c₁ (proj2 x)
... | tri> ¬a₁ ¬b c = tri>  tr00 (λ eq → ¬b (cong ord eq) ) (case2 ⟪ refl , c ⟫ )  where
   tr00 : ¬ (suc (lv a) ≤ lv b) ∨ ((lv a ≡ lv b) ∧ (suc (ord a) ≤ ord b))
   tr00 (case1 x) = ¬c x
   tr00 (case2 x) = ¬a₁ (proj2 x)

ordtrans : {x y z : Ordinal  }   → x o< y → y o< z → x o< z
ordtrans {x} {y} {z} (case1 x₁) (case1 x₂) = case1 (<-trans x₁ x₂)
ordtrans {x} {y} {z} (case1 x₁) (case2 x₂) = case1 ( subst (λ k → lv x < k ) (proj1 x₂) x₁ )
ordtrans {x} {y} {z} (case2 x₁) (case1 x₂) = case1 ( subst (λ k → k < lv z ) (sym (proj1 x₁)) x₂ )
ordtrans {x} {y} {z} (case2 x₁) (case2 x₂) = case2 ⟪ trans (proj1 x₁) (proj1 x₂) , <-trans (proj2 x₁) (proj2 x₂) ⟫

o<> : {x y : Ordinal  }  →  y o< x → x o< y → ⊥
o<> {x} {y} y<x x<y with trio< x y
... | tri< a ¬b ¬c = ⊥-elim ( ¬c y<x )
... | tri≈ ¬a b ¬c = ⊥-elim ( ¬c y<x )
... | tri> ¬a ¬b c = ⊥-elim ( ¬a x<y )

osuc-≡< : { a x : Ordinal  } → x o< osuc a  →  (x ≡ a ) ∨ (x o< a)
osuc-≡< {a} {x} (case1 x₁) = case2 (case1 x₁)
osuc-≡< {a} {x} (case2 ⟪ eq , lt ⟫) with <-cmp (ord x) (ord a)
... | tri< a₁ ¬b ¬c = case2 (case2 ⟪ eq , a₁ ⟫)
osuc-≡< {a} {ordinal .(lv a) .(ord a)} (case2 ⟪ refl , lt ⟫) | tri≈ ¬a refl ¬c = case1 refl
... | tri> ¬a ¬b c = ⊥-elim ( nat-≤> c lt )


-- we don't use this
OrdIrr :  {x y : Ordinal  } (lt lt1 : x o< y) → lt ≡ lt1
OrdIrr {x} {y} (case1 x₁) (case1 x₂) = cong case1 (<-irrelevant _ _)
OrdIrr {x} {y} (case1 x₁) (case2 x₂) = ⊥-elim ( nat-≡< (proj1 x₂) x₁  )
OrdIrr {x} {y} (case2 x₁) (case1 x₂) = ⊥-elim ( nat-≡< (proj1 x₁) x₂  )
OrdIrr {x} {y} (case2 x₁) (case2 x₂) with (≡-irrelevant (proj1 x₁) (proj1 x₂)) | (<-irrelevant (proj2 x₁) (proj2 x₂))
... | refl | refl = refl

TransFinite : {m : Level} → { ψ : Ordinal  → Set m }
  → ( (x : Ordinal)  → ( (y : Ordinal  ) → y o< x → ψ y ) → ψ x )
  →  ∀ (x : Ordinal)  → ψ x
TransFinite  {m} {ψ} ind x = proj1 (TransFinite1 (lv x) (ord x) ) where
  caseΦ : (lx : ℕ) → ((x₁ : Ordinal) → x₁ o< ordinal lx zero → ψ x₁) →
        ψ (record { lv = lx ; ord = zero })
  caseΦ lx prev = ind (ordinal lx zero ) prev
  caseOSuc :  (lx : ℕ) (x₁ : ℕ) → ((y : Ordinal) → y o< ordinal lx (suc x₁) → ψ y) →
        ψ (record { lv = lx ; ord = suc x₁ })
  caseOSuc lx ox prev = ind (ordinal lx (suc ox)) prev 
  TransFinite1 : (lx : ℕ) (ox : ℕ ) → ψ (ordinal lx ox) ∧ ( ( (x : Ordinal  ) → x o< ordinal lx ox  → ψ x ) )
  TransFinite1 zero zero = ⟪  caseΦ zero lemma , lemma1 ⟫ where
      lemma : (x : Ordinal) → x o< ordinal zero zero → ψ x
      lemma x (case1 s) = ⊥-elim ( nat-≤> z≤n s )
      lemma x (case2 s) = ⊥-elim (nat-≤> z≤n (proj2  s))
      lemma1 : (x : Ordinal) → x o< ordinal zero zero → ψ x
      lemma1 x (case1 s) = ⊥-elim ( nat-≤> z≤n s )
      lemma1 x (case2 s) = ⊥-elim (nat-≤> z≤n (proj2  s))
  TransFinite1 (suc lx) zero = ⟪ caseΦ (suc lx) (λ x → lemma (lv x) (ord x)) , (λ x → lemma (lv x) (ord x)) ⟫ where
      lemma0 : (ly : ℕ) (oy : ℕ ) → ordinal ly oy  o< ordinal lx zero → ψ (ordinal ly oy)
      lemma0 ly oy lt = proj2 ( TransFinite1 lx zero ) (ordinal ly oy) lt
      lemma : (ly : ℕ) (oy : ℕ ) → ordinal ly oy  o< ordinal (suc lx) zero → ψ (ordinal ly oy)
      lemma lx1 ox1   (case2 lt) = ⊥-elim (nat-≤> z≤n (proj2  lt))
      lemma lx1 ox1   (case1 lt) with <-∨ lt
      lemma lx zero   (case1 lt) | case1 refl = proj1 ( TransFinite1 lx zero )
      lemma lx zero   (case1 lt) | case2 lt1 = lemma0  lx zero (case1 lt1)
      lemma lx (suc ox1)   (case1 lt) | case1 refl = caseOSuc lx ox1 lemma2 where
          lemma2 : (y : Ordinal) → (suc (lv y) ≤ lx) ∨ ((lv y ≡ lx) ∧ (suc (ord y) ≤ suc ox1)) → ψ y
          lemma2 y lt1 with osuc-≡< lt1
          ... | case1 refl = lemma lx ox1 (case1 a<sa)
          ... | case2 lt2 = proj2 (TransFinite1 lx ox1) y lt2
      lemma lx1 (suc ox1) (case1 lt) | case2 lt1 = caseOSuc lx1 ox1 lemma2 where
          lemma2 : (y : Ordinal) → (suc (lv y) ≤ lx1) ∨ ((lv y ≡ lx1) ∧ (suc (ord y) ≤ suc ox1)) → ψ y
          lemma2 y lt2 with osuc-≡< lt2
          ... | case1 refl = lemma lx1 ox1 (ordtrans lt2 (case1 lt))
          ... | case2 (case1 lt3) = proj2 (TransFinite1 lx zero) y (case1 (<-trans lt3 lt1 ))
          ... | case2 (case2 lt3) = proj2 (TransFinite1 lx zero) y (case1 lemma3) where
              lemma3 : lv y < lx
              lemma3 = begin
                 suc (lv y) ≡⟨ cong suc (proj1 lt3) ⟩
                 suc lx1 ≤⟨ lt1 ⟩
                 lx ∎ where open ≤-Reasoning
  TransFinite1 lx (suc ox)  = ⟪ caseOSuc lx ox lemma , lemma ⟫ where
      lemma : (y : Ordinal) → y o< ordinal lx (suc ox) → ψ y
      lemma y lt with osuc-≡< lt
      lemma y lt | case1 refl = proj1 ( TransFinite1 lx ox )
      lemma y lt | case2 lt1 = proj2 ( TransFinite1 lx ox ) y lt1


open import Induction.WellFounded

-- The accessibility predicate: x is accessible if everything which is
-- smaller than x is also accessible (inductively).
--
-- data Acc {A : Set a} (_<_ : Rel A ℓ) (x : A) : Set (a ⊔ ℓ) where
--   acc : (rs : (y : A ) → y < x → Acc _<_ x) → Acc _<_ x


ordWF : WellFounded _o<_
ordWF x = TransFinite {Zero} {λ y → Acc _o<_ y} (λ x ind → acc (λ rs → ind _ rs  ) )  x

TransFiniteWF : {m : Level} 
  → ( (x : Ordinal)  → ( (y : Ordinal  ) → y o< x → Acc _o<_ y ) → Acc _o<_ x )
  →  ∀ (x : Ordinal)  → Acc _o<_ x
TransFiniteWF  {m} ind x = proj1 (TransFinite1 (lv x) (ord x) ) where
  caseΦ : (lx : ℕ) → ((x₁ : Ordinal) → x₁ o< ordinal lx zero → Acc _o<_ x₁) →
        Acc _o<_ (record { lv = lx ; ord = zero })
  caseΦ lx prev = ind (ordinal lx zero ) prev
  caseOSuc :  (lx : ℕ) (x₁ : ℕ) → ((y : Ordinal) → y o< ordinal lx (suc x₁) → Acc _o<_ y) →
        Acc _o<_ (record { lv = lx ; ord = suc x₁ })
  caseOSuc lx ox prev = ind (ordinal lx (suc ox)) prev 
  TransFinite1 : (lx : ℕ) (ox : ℕ ) → Acc _o<_ (ordinal lx ox) ∧ ( ( (x : Ordinal  ) → x o< ordinal lx ox  → Acc _o<_ x ) )
  TransFinite1 zero zero = ⟪  caseΦ zero lemma , lemma1 ⟫ where
      lemma : (x : Ordinal) → x o< ordinal zero zero → Acc _o<_ x
      lemma x (case1 s) = ⊥-elim ( nat-≤> z≤n s )
      lemma x (case2 s) = ⊥-elim (nat-≤> z≤n (proj2  s))
      lemma1 : (x : Ordinal) → x o< ordinal zero zero → Acc _o<_ x
      lemma1 x (case1 s) = ⊥-elim ( nat-≤> z≤n s )
      lemma1 x (case2 s) = ⊥-elim (nat-≤> z≤n (proj2  s))
  TransFinite1 (suc lx) zero = ⟪ caseΦ (suc lx) (λ x → lemma (lv x) (ord x)) , (λ x → lemma (lv x) (ord x)) ⟫ where
      lemma0 : (ly : ℕ) (oy : ℕ ) → ordinal ly oy  o< ordinal lx zero → Acc _o<_ (ordinal ly oy)
      lemma0 ly oy lt = proj2 ( TransFinite1 lx zero ) (ordinal ly oy) lt
      lemma : (ly : ℕ) (oy : ℕ ) → ordinal ly oy  o< ordinal (suc lx) zero → Acc _o<_ (ordinal ly oy)
      lemma lx1 ox1   (case2 s) = ⊥-elim (nat-≤> z≤n (proj2  s))
      lemma lx1 ox1   (case1 lt) with <-∨ lt
      lemma lx zero   (case1 lt) | case1 refl = proj1 ( TransFinite1 lx zero )
      lemma lx zero   (case1 lt) | case2 lt1 = lemma0  lx zero (case1 lt1)
      lemma lx (suc ox1)   (case1 lt) | case1 refl = caseOSuc lx ox1 lemma2 where
          lemma2 : (y : Ordinal) → (suc (lv y) ≤ lx) ∨ ((lv y ≡ lx) ∧ (suc (ord y) ≤ suc ox1)) → Acc _o<_ y
          lemma2 y lt1 with osuc-≡< lt1
          ... | case1 refl = lemma lx ox1 (case1 a<sa)
          ... | case2 lt2 = proj2 (TransFinite1 lx ox1) y lt2
      lemma lx1 (suc ox1) (case1 lt) | case2 lt1 = caseOSuc lx1 ox1 lemma2 where
          lemma2 : (y : Ordinal) → (suc (lv y) ≤ lx1) ∨ ((lv y ≡ lx1) ∧ (suc (ord y) ≤ suc ox1)) → Acc _o<_ y
          lemma2 y lt2 with osuc-≡< lt2
          ... | case1 refl = lemma lx1 ox1 (ordtrans lt2 (case1 lt))
          ... | case2 (case1 lt3) = proj2 (TransFinite1 lx zero) y (case1 (<-trans lt3 lt1 ))
          ... | case2 (case2 lt3) = proj2 (TransFinite1 lx zero) y (case1 lemma3) where
              lemma3 : lv y < lx
              lemma3 = begin
                 suc (lv y) ≡⟨ cong suc (proj1 lt3) ⟩
                 suc lx1 ≤⟨ lt1 ⟩
                 lx ∎ where open ≤-Reasoning
  TransFinite1 lx (suc ox)  = ⟪ caseOSuc lx ox lemma , lemma ⟫ where
      lemma : (y : Ordinal) → y o< ordinal lx (suc ox) → Acc _o<_ y
      lemma y lt with osuc-≡< lt
      lemma y lt | case1 refl = proj1 ( TransFinite1 lx ox )
      lemma y lt | case2 lt1 = proj2 ( TransFinite1 lx ox ) y lt1

open import Ordinals

C-Ordinal :  Ordinals {Zero}
C-Ordinal  = record {
     Ordinal = Ordinal
   ; o∅ = o∅
   ; osuc = osuc
   ; _o<_ = _o<_
   ; isOrdinal = record {
       ordtrans = ordtrans
     ; trio< = trio<
     ; ¬x<0 = ¬x<0
     ; <-osuc = <-osuc
     ; osuc-≡< = osuc-≡<
     ; TransFinite = TransFinite2
     ; Oprev-p  = Oprev-p
     ; o<-irr = OrdIrr _ _
   } --
   -- isNext = record {
   --     x<nx = x<nx
   --   ; osuc<nx = λ {x} {y} → osuc<nx {x} {y}
   --   -- ; ¬nx<nx = ¬nx<nx
   -- }
  } where
     next : Ordinal  → Ordinal
     next (ordinal lv ord) = ordinal (suc lv) zero
     x<nx :    { y : Ordinal } → (y o< next y )
     x<nx = case1 a<sa
     -- osuc<nx : { x y : Ordinal } → x o< next y → osuc x o< next y
     -- osuc<nx {x} {Y} (case2 lv<) = ?
     -- osuc<nx {x} {Y} (case1 lv<) = case1 lv<
     open Oprev
     Oprev-p  : (x : Ordinal) → Dec0 ( Oprev (Ordinal )  osuc x )
     Oprev-p (ordinal lv₁ zero) = no0 (λ ())
     Oprev-p (ordinal lv₁ (suc ord₁)) = yes0 (record { oprev = ordinal lv₁ ord₁  ; oprev=x = refl })
     ord1 : Set
     ord1 = Ordinal
     TransFinite2 : {m : Level } { ψ : ord1  → Set m }
          → ( (x : ord1)  → ( (y : ord1  ) → y o< x → ψ y ) → ψ x )
          →  ∀ (x : ord1)  → ψ x
     TransFinite2 {ψ} ind x = TransFinite ind x


-- H-Ordinal : {n : Level} → Ordinals {suc n} →  Ordinals {suc n}  →  Ordinals {suc n}
-- H-Ordinal {n} O1 O2 = record {
--      Ordinal = Ordinals.Ordinal O1 ∧ Ordinals.Ordinal O2
--   }
-- We may have an oridinal as proper subset  of an ordinal
--   then the internal ordinal become a set in the outer ordinal
