{-# OPTIONS --cubical-compatible --safe #-}
open import Level
open import logic
open import Relation.Binary hiding (_⇔_)
import Relation.Binary.Reasoning.Setoid as EqR

module BoolAlgebra  where

--
-- It is ok to use Boolean Algebra in stdlib...
--
record IsBooleanAlgebra {n m : Level} ( L : Set n)
       ( _≈_ : L → L → Set m )
       ( b1 : L )
       ( b0 : L )
       ( -_ : L → L  )
       ( _+_ : L → L → L )
       ( _x_ : L → L → L ) : Set (n ⊔ m) where
   field
       isEquivalence : IsEquivalence {n} {m} {L} _≈_
       +-assoc : {a b c : L } → (a + ( b + c )) ≈ ((a + b) + c)
       x-assoc : {a b c : L } → (a x ( b x c )) ≈ ((a x b) x c)
       +-sym : {a b : L } → (a + b) ≈ (b + a)
       x-sym : {a b : L } → (a x b)  ≈ (b x a)
       +-aab : {a b : L } → (a + ( a x b )) ≈ a
       x-aab : {a b : L } → (a x ( a + b )) ≈ a
       +-dist : {a b c : L } → (a + ( b x c )) ≈ (( a + b ) x ( a + c ))
       x-dist : {a b c : L } → (a x ( b + c )) ≈ (( a x b ) + ( a x c ))
       a+0 : {a : L } → (a + b0) ≈ a
       ax1 : {a : L } → (a x b1) ≈ a
       a+-a1 : {a : L } → (a + ( - a )) ≈ b1
       ax-a0 : {a : L } → (a x ( - a )) ≈ b0
       +-resp : {f g h i : L} → f ≈ g → h ≈ i → (h + f) ≈ (i + g)
       x-resp : {f g h i : L} → f ≈ g → h ≈ i → (h x f) ≈ (i x g)
       neg-resp : {f g : L} → f ≈ g → (- f) ≈ (- g)
   bSetoid : Setoid n m
   bSetoid = record { _≈_ = λ x y → x ≈ y ; Carrier = L ; isEquivalence = isEquivalence  }
   open EqR bSetoid
   brefl : {a : L } →  a ≈ a
   brefl = IsEquivalence.refl isEquivalence
   bsym : {a b : L } →  a ≈ b → b ≈ a
   bsym = IsEquivalence.sym isEquivalence
   btrans : {a b c : L } →  a ≈ b → b ≈ c → a ≈ c
   btrans = IsEquivalence.trans isEquivalence
   x-idem : {a : L} → (a x a) ≈ a
   x-idem {a} = begin
      (a x a) ≈⟨ x-resp (bsym a+0) brefl  ⟩
      (a x ( a + b0 )) ≈⟨ x-aab ⟩
      a ∎
   +-idem : {a : L} → (a + a) ≈ a
   +-idem {a} = begin
      (a + a) ≈⟨ +-resp (bsym ax1) brefl  ⟩
      (a + ( a x b1 )) ≈⟨ +-aab ⟩
      a ∎
   +-dist' : {a b c : L } → (( b x c ) + a) ≈ (( b + a ) x ( c + a ))
   +-dist' = btrans +-sym ( btrans +-dist (x-resp +-sym +-sym ) ) 
   x-dist' : {a b c : L } → (( b + c ) x a) ≈ (( b x a ) + ( c x a ))
   x-dist' = btrans x-sym ( btrans x-dist (+-resp x-sym x-sym ) ) 

open import Data.Product
open import logic
open import Relation.Nullary

record BooleanAlgebra {n m : Level} ( L : Set n) : Set (n ⊔ suc m) where
   field
       _≈_ : L → L → Set m
       b1 : L
       b0 : L
       -_ : L → L
       _+_ : L → L → L
       _x_ : L → L → L
       isBooleanAlgebra : IsBooleanAlgebra L _≈_ b1 b0 -_ _+_ _x_
   _≤_ : L → L → Set m
   a ≤ b = (a x b) ≈ a
   _<_ : L → L → Set m
   a < b = (¬ ( a ≈ b )) ∧ ((a x b) ≈ a)
   open EqR (IsBooleanAlgebra.bSetoid isBooleanAlgebra )
   open IsBooleanAlgebra isBooleanAlgebra
   open import Tactic.MonoidSolver using (solve; solve-macro)
   open import Algebra
   x-monoid : Monoid n m
   x-monoid = record {
        Carrier  = L
        ;    _≈_  =  _≈_
        ; _∙_  = _x_
        ; ε   = b1
        ; isMonoid = record { isSemigroup = record { isMagma = record {
            isEquivalence = record { refl = brefl ; sym = bsym ; trans = btrans } ; ∙-cong = λ e1 e2 → x-resp e2 e1 }
               ; assoc =  λ x y z → bsym (x-assoc {x} {y} {z}) } ; identity =  ( λ a → btrans x-sym ( ax1 {a}) ) ,  ( λ a → ax1 {a} ) }
      }
   +-monoid : Monoid n m
   +-monoid = record {
        Carrier  = L
        ;    _≈_  =  _≈_
        ; _∙_  = _+_
        ; ε   = b0
        ; isMonoid = record { isSemigroup = record { isMagma = record {
            isEquivalence = record { refl = brefl ; sym = bsym ; trans = btrans } ; ∙-cong = λ e1 e2 → +-resp e2 e1 }
               ; assoc =  λ x y z → bsym (+-assoc {x} {y} {z}) } ; identity =  ( λ a → btrans +-sym ( a+0 {a}) ) ,  ( λ a → a+0 {a} ) }
      }
   0≤a : (a : L ) → b0 ≤ a
   0≤a a = begin
       b0 x a ≈⟨ x-resp brefl (bsym ax-a0) ⟩
       (a x ( - a)) x a ≈⟨ x-resp brefl (x-resp (bsym x-idem) brefl)  ⟩
       (a x (( - a)x ( - a))) x a ≈⟨ solve x-monoid ⟩
       (a x ( - a)) x (( - a) x a) ≈⟨ x-resp (btrans x-sym ax-a0) ax-a0 ⟩
       b0 x b0 ≈⟨ x-idem ⟩
       b0 ∎
   +-monoʳ-< : {a b c : L } → a ≤ b → (a + c) ≤ (b + c)
   +-monoʳ-< {a} {b} {c} a≤b = begin
       (a + c ) x (b + c) ≈⟨ x-dist' ⟩
       (a x (b + c) ) + (c x ( b + c )) ≈⟨ +-resp x-dist  x-dist  ⟩
       ((a x b )+ (a x c))  + ((c x  b) + (c x c )) ≈⟨ +-resp (+-resp x-idem brefl ) (+-resp brefl a≤b )  ⟩
       (a + (a x c) )  + ((c x  b) + c) ≈⟨ +-resp +-sym +-aab  ⟩
       a  + (c + (c x  b) ) ≈⟨ +-resp  +-aab brefl ⟩
       a + c  ∎
   +-monoˡ-< : {a b c : L } → a ≤ b → (c + a)  ≤ (c + b)
   +-monoˡ-< {a} {b} {c} a≤b = begin
       (c + a ) x (c + b) ≈⟨ x-dist' ⟩
       (c x (c + b)) +  (a  x (c + b)) ≈⟨ +-resp x-dist x-dist ⟩
       ((c x c) + (c x b)) +  ((a  x c) + (a x b)) ≈⟨ +-resp (+-resp a≤b brefl ) (+-resp brefl x-idem ) ⟩
       (c + (c x b)) +  ((a  x c) + a) ≈⟨ +-resp (btrans +-sym +-aab ) +-aab  ⟩
       c + a  ∎
   x-monoʳ-< : {a b c : L } → a ≤ b → (a x c) ≤ (b x c)
   x-monoʳ-< {a} {b} {c} a≤b = begin
       (a x c ) x (b x c) ≈⟨ x-resp brefl x-sym ⟩ 
       (c x a ) x (b x c) ≈⟨ bsym x-assoc ⟩ 
       c x ( a  x (b x c)) ≈⟨ x-resp x-assoc brefl ⟩ 
       c x ( (a  x b ) x c) ≈⟨ x-resp (x-resp brefl a≤b) brefl ⟩ 
       c x ( a x c) ≈⟨ x-assoc ⟩ 
       (c x  a) x c ≈⟨ x-resp brefl x-sym ⟩ 
       (a x  c) x c ≈⟨ bsym x-assoc ⟩ 
       a x  (c x c) ≈⟨ x-resp x-idem brefl ⟩
       a x c  ∎
   x-monoˡ-< : {a b c : L } → a ≤ b → (c x a)  ≤ (c x b)
   x-monoˡ-< {a} {b} {c} a≤b = begin
       (c x a ) x (c x b) ≈⟨ bsym x-assoc ⟩
       c x ( a  x (c x b)) ≈⟨ x-resp (x-resp x-sym brefl ) brefl  ⟩
       c x ( a  x (b x c)) ≈⟨ x-resp x-assoc brefl ⟩
       c x ( (a  x b) x c) ≈⟨ x-resp (x-resp brefl a≤b)  brefl ⟩
       c x ( a x c) ≈⟨ x-resp x-sym brefl  ⟩
       c x ( c x a) ≈⟨ x-assoc ⟩
       (c x  c) x a ≈⟨ x-resp brefl x-idem   ⟩
       c x a  ∎
   lemma-aa : ∀ a b → (a x b) ≈ b0 → (a + b) ≈ b1 → (- a) ≈ b
   lemma-aa a b axb=b0 a+b=b1 = begin
        - a                ≈⟨ bsym ax1 ⟩
        (- a) x b1            ≈⟨ x-resp (bsym a+b=b1) brefl  ⟩ 
        (- a ) x (a + b)      ≈⟨ x-dist  ⟩ 
        ((- a) x a ) + ((- a) x b)  ≈⟨ +-resp brefl (btrans x-sym ax-a0)  ⟩ 
        b0 + ((- a) x b)        ≈⟨ +-resp brefl (bsym axb=b0) ⟩ 
        (a x b ) + ( (- a) x b )   ≈⟨ bsym x-dist' ⟩ 
        (a + (- a)) x b      ≈⟨  x-resp brefl  a+-a1 ⟩ 
        b1 x b              ≈⟨ btrans x-sym  ax1  ⟩ 
        b                  ∎
   double-negation : {a : L } → (- (- a)) ≈ a
   double-negation {a} = lemma-aa _ _ (btrans x-sym ax-a0)  (btrans +-sym a+-a1)
   x0=0 : {a : L} → (a x b0) ≈ b0
   x0=0 {a} =  begin
       a x b0 ≈⟨ x-resp brefl (bsym  a+0) ⟩
       (a + b0) x b0 ≈⟨ btrans x-sym (x-resp +-sym brefl )  ⟩
       b0 x (b0 + a) ≈⟨ x-aab  ⟩
       b0  ∎ 
   +1=1 : {a : L} → (a + b1) ≈ b1
   +1=1 {a} =  begin
       a + b1 ≈⟨ +-resp brefl (bsym   ax1 ) ⟩
       (a x b1) + b1 ≈⟨ btrans +-sym (+-resp x-sym brefl )  ⟩
       b1 + (b1 x a) ≈⟨ +-aab  ⟩
       b1  ∎ 
   demorgan0 : {a b  : L } → (- (a x b)) ≈ ((- a) + (- b) )
   demorgan0 {a} {b} = begin
       - (a x b)  ≈⟨ lemma-aa _ _ 
          (begin (a x b) x ((- a) + (- b))          ≈⟨  x-dist ⟩
            ((a x b) x (- a)) + ((a x b) x (- b))  ≈⟨ +-resp brefl (x-resp brefl x-sym )  ⟩
            ((b x a) x (- a)) + ((a x b) x (- b))  ≈⟨ +-resp (bsym x-assoc) (bsym x-assoc ) ⟩
            (b x (a x (- a))) + (a x (b x (- b)))  ≈⟨ +-resp (x-resp  ax-a0 brefl) (x-resp  ax-a0 brefl ) ⟩
            (b x b0) + (a x b0)              ≈⟨ +-resp x0=0 x0=0  ⟩
            b0 + b0                          ≈⟨ +-idem ⟩
          b0 ∎ ) 
          ( begin (a x b) + ((- a) + (- b))   ≈⟨ +-assoc ⟩
            ((a x b) + (- a)) + (- b)  ≈⟨ +-resp brefl ( begin 
                (a x b) + (- a)          ≈⟨  +-dist' ⟩
                (a + (- a)) x (b + (- a))  ≈⟨ x-resp brefl  a+-a1  ⟩
                b1 x (b + (- a))          ≈⟨ btrans x-sym ax1 ⟩
                b + (- a)                ≈⟨ +-sym ⟩
                (- a) + b       ∎ ) ⟩
            ((- a) + b) + (- b)        ≈⟨ bsym +-assoc ⟩
            (- a) + (b + (- b))        ≈⟨ +-resp  a+-a1  brefl  ⟩
            (- a) + b1                ≈⟨ +1=1 ⟩
          b1  ∎ )  ⟩
       (- a) + (- b)  ∎
   demorgan1 : {a b  : L } → (- (a + b)) ≈ ((- a) x (- b) )
   demorgan1 {a} {b} = begin
          - (a + b) ≈⟨ neg-resp ( +-resp (bsym  double-negation) (bsym  double-negation) ) ⟩
          - ((- ( - a)) + (- ( - b) )) ≈⟨ neg-resp ( bsym demorgan0)  ⟩
          - ( - ( ( - a) x ( - b))) ≈⟨  double-negation ⟩
          (- a) x (- b)   ∎ 
   neg-mono-≤ : {a b : L } → a ≤ b → (- b) ≤ (- a)
   neg-mono-≤ {a} {b} a≤b = begin  -- a x b ≈ a   -- ( -a ) + (- b) ≈ -a 
       ( - b ) x ( - a ) ≈⟨ x-resp (bsym (neg-resp a≤b)) brefl ⟩
       ( - b ) x ( - (a x b) ) ≈⟨ x-resp demorgan0 brefl ⟩
       ( - b ) x ( (- a) + ( - b) ) ≈⟨ x-resp +-sym  brefl ⟩
       ( - b ) x ( (- b) + ( - a) ) ≈⟨ x-aab  ⟩
       - b ∎
   ≤0→≈  : {a : L } → a ≤ b0 → a ≈ b0
   ≤0→≈ {a} eq  = btrans (bsym eq) (btrans x-sym (0≤a _))
   ≤-trans : {i j k : L} → i ≤ j → j ≤ k → i ≤ k
   ≤-trans {i} {j} {k} i≤j j≤k = begin
       i x k ≈⟨ x-resp brefl (bsym i≤j) ⟩
       (i x j) x k ≈⟨ bsym x-assoc ⟩
       i x (j x k) ≈⟨ x-resp j≤k brefl ⟩
       i x j ≈⟨ i≤j  ⟩
       i ∎
   resp-≤ : {i j k l : L} → i ≈ k → j ≈ l → i ≤ j → k ≤ l
   resp-≤ {i} {j} {k} {l} i=k j=l i≤j =  btrans (btrans (x-resp (bsym j=l ) (bsym i=k) ) i≤j   ) i=k 


record BPred {n m : Level} ( L : Set n) (BA : BooleanAlgebra {n} {m} L) : Set (n ⊔ suc m) where
   open BooleanAlgebra BA using (_≈_)
   field
       pred : L → Set m
       pcong : ( x y : L ) → x ≈ y → ( pred x ⇔ pred y )


record IsCompleteBooleanAlgebra {n m : Level} ( L : Set n) (BA : BooleanAlgebra {n} {m} L) : Set (n ⊔ suc m ) where
   open BooleanAlgebra BA using (_≤_)
   IsUpperBound : (s : BPred L BA) → L → Set (n ⊔ m )
   IsUpperBound s u = (x : L) → BPred.pred s x → x ≤ u
   field
       sup : BPred L BA  → L
       is-sup : (s : BPred L BA) → IsUpperBound s (sup s)
       is-minsup : (s : BPred L BA) → {x : L} → IsUpperBound s x → sup s ≤  x

open import Relation.Binary.Reasoning.Syntax

module BA≤-Reasoning {n m : Level} {L : Set n} (BA : BooleanAlgebra {n} {m} L)  where
   open BooleanAlgebra BA
   open _∧_
   open IsBooleanAlgebra isBooleanAlgebra

   open EqR bSetoid

   BAPreorder :   Preorder n m m
   BAPreorder  = record { Carrier = L
       ; _≈_  = _≈_
       ; _≲_ = _≤_  
       ; isPreorder   = record {
            isEquivalence = IsBooleanAlgebra.isEquivalence (isBooleanAlgebra) 
            ; reflexive     = λ eq →  btrans (x-resp (bsym eq) brefl ) x-idem 
            ; trans         = ≤-trans
         }
     }

   resp-< : _<_ Respects₂ _≈_
   resp-< =   record { fst =  λ {i} {j} {k} j=k i<j → ⟪ (λ i=k → proj1 i<j (btrans i=k (bsym j=k))  ) , btrans (x-resp (bsym j=k) brefl ) (proj2 i<j) ⟫  
       ; snd = λ {i} {j} {k} j=k i<j → ⟪ (λ i=k → proj1 i<j (btrans j=k i=k)  ) , btrans (x-resp brefl (bsym j=k) ) (btrans (proj2 i<j) j=k ) ⟫   }

   trans1 : {i j k : L} → i < j → j ≤ k → i < k
   trans1 {i} {j} {k} ⟪ ¬i=j , i≤j ⟫ j≤k = ⟪ (λ i=k → ¬i=j (btrans (bsym i≤j) (btrans x-sym (btrans (x-resp i=k brefl ) j≤k) ) )  ) , ≤-trans i≤j j≤k ⟫

   trans2 : {i j k : L} → i ≤ j → j <  k → i < k
   trans2 {i} {j} {k} i≤j ⟪ ¬j=k , j≤k ⟫ = ⟪ (λ i=k → ¬j=k (btrans (bsym j≤k) (btrans x-sym (btrans (btrans (x-resp brefl (bsym i=k) ) i≤j ) i=k ) ) )  ) , ≤-trans i≤j j≤k ⟫

   open import Relation.Binary.Reasoning.Base.Triple
        (Preorder.isPreorder BAPreorder)
        (λ {x} {y} x<y y<x → proj1 x<y (btrans (bsym (proj2 x<y)) (btrans x-sym (proj2 y<x) ) )  )
        (λ {i} {j} {k} i<j j<k → ⟪ (λ i=k → proj1 (i<j) (btrans (bsym (proj2 i<j)) (btrans (btrans x-sym (x-resp i=k brefl) ) (proj2 j<k)) ) )  , ≤-trans (proj2 i<j) (proj2 j<k) ⟫  )
        record { fst = λ {x} {y} {z} y=z x<y → ⟪ (λ x=z → proj1 x<y (btrans x=z (bsym y=z) )) , btrans (x-resp (bsym y=z) brefl) (proj2 x<y) ⟫  
               ; snd = λ {x} {y} {z} y=z x<y → ⟪ (λ z=x → proj1 x<y (btrans y=z z=x )) , btrans (btrans (x-resp brefl (bsym y=z) ) (proj2 x<y)) y=z ⟫ } 
        (λ x → proj2 x ) 
        trans1 
        trans2
        public
        hiding (step-≈; step-≈˘; step-≈-⟩; step-≈-⟨)

-- end
