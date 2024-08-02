{-# OPTIONS --cubical-compatible --safe #-}

module logic where

open import Level
open import Relation.Nullary
open import Relation.Binary hiding (_⇔_ )
open import Data.Empty


data Bool : Set where
    true : Bool
    false : Bool

record  _∧_  {n m : Level} (A  : Set n) ( B : Set m ) : Set (n ⊔ m) where
   constructor ⟪_,_⟫
   field
      proj1 : A
      proj2 : B

data  _∨_  {n m : Level} (A  : Set n) ( B : Set m ) : Set (n ⊔ m) where
   case1 : A → A ∨ B
   case2 : B → A ∨ B

_⇔_ : {n m : Level } → ( A : Set n ) ( B : Set m )  → Set (n ⊔ m)
_⇔_ A B =  ( A → B ) ∧ ( B → A )

contra-position : {n m : Level } {A : Set n} {B : Set m} → (A → B) → ¬ B → ¬ A
contra-position {n} {m} {A} {B}  f ¬b a = ¬b ( f a )

double-neg : {n  : Level } {A : Set n} → A → ¬ ¬ A
double-neg A notnot = notnot A

double-neg2 : {n  : Level } {A : Set n} → ¬ ¬ ¬ A → ¬ A
double-neg2 notnot A = notnot ( double-neg A )

de-morgan : {n  : Level } {A B : Set n} →  A ∧ B  → ¬ ( (¬ A ) ∨ (¬ B ) )
de-morgan {n} {A} {B} and (case1 ¬A) = ⊥-elim ( ¬A ( _∧_.proj1 and ))
de-morgan {n} {A} {B} and (case2 ¬B) = ⊥-elim ( ¬B ( _∧_.proj2 and ))

dont-or :　{n m : Level} {A  : Set n} { B : Set m } →  A ∨ B → ¬ A → B
dont-or {A} {B} (case1 a) ¬A = ⊥-elim ( ¬A a )
dont-or {A} {B} (case2 b) ¬A = b

dont-orb :　{n m : Level} {A  : Set n} { B : Set m } →  A ∨ B → ¬ B → A
dont-orb {A} {B} (case2 b) ¬B = ⊥-elim ( ¬B b )
dont-orb {A} {B} (case1 a) ¬B = a

infixr  130 _∧_
infixr  140 _∨_
infixr  150 _⇔_

_/\_ : Bool → Bool → Bool
true /\ true = true
_ /\ _ = false

_\/_ : Bool → Bool → Bool
false \/ false = false
_ \/ _ = true

not : Bool → Bool
not true = false
not false = true

_<=>_ : Bool → Bool → Bool
true <=> true = true
false <=> false = true
_ <=> _ = false

infixr  130 _\/_
infixr  140 _/\_

open import Relation.Binary.PropositionalEquality

record Bijection {n m : Level} (R : Set n) (S : Set m) : Set (n Level.⊔ m)  where
   field
       fun←  :  S → R
       fun→  :  R → S
       fiso← : (x : R)  → fun← ( fun→ x )  ≡ x
       fiso→ : (x : S ) → fun→ ( fun← x )  ≡ x

injection :  {n m : Level} (R : Set n) (S : Set m) (f : R → S ) → Set (n Level.⊔ m)
injection R S f = (x y : R) → f x ≡ f y → x ≡ y


-- Cubical Agda has trouble with std-lib's Dec
-- we sometimes use simpler version of Dec

data Dec0 {n : Level} (A : Set n) : Set n where
  yes0 : A → Dec0 A
  no0  : (A → ⊥) → Dec0 A

open _∧_ 
∧-injective : {n m : Level} {A : Set n} {B : Set m} → {a b : A ∧ B}  → proj1 a ≡ proj1 b → proj2 a ≡ proj2 b → a ≡ b
∧-injective refl refl = refl

not-not-bool : { b : Bool } → not (not b) ≡ b
not-not-bool {true} = refl
not-not-bool {false} = refl

¬t=f : (t : Bool ) → ¬ ( not t ≡ t)
¬t=f true ()
¬t=f false ()

≡-Bool-func : {A B : Bool } → ( A ≡ true → B ≡ true ) → ( B ≡ true → A ≡ true ) → A ≡ B
≡-Bool-func {true} {true} a→b b→a = refl
≡-Bool-func {false} {true} a→b b→a with b→a refl
... | ()
≡-Bool-func {true} {false} a→b b→a with a→b refl
... | ()
≡-Bool-func {false} {false} a→b b→a = refl

bool-≡-? : (a b : Bool) → Dec0 ( a ≡ b )
bool-≡-? true true = yes0 refl
bool-≡-? true false = no0 (λ ())
bool-≡-? false true = no0 (λ ())
bool-≡-? false false = yes0 refl

¬-bool-t : {a : Bool} →  ¬ ( a ≡ true ) → a ≡ false
¬-bool-t {true} ne = ⊥-elim ( ne refl )
¬-bool-t {false} ne = refl

¬-bool-f : {a : Bool} →  ¬ ( a ≡ false ) → a ≡ true
¬-bool-f {true} ne = refl
¬-bool-f {false} ne = ⊥-elim ( ne refl )

¬-bool : {a : Bool} →  a ≡ false  → a ≡ true → ⊥
¬-bool refl ()

lemma-∧-0 : {a b : Bool} → a /\ b ≡ true → a ≡ false → ⊥
lemma-∧-0 {true} {false} ()
lemma-∧-0 {false} {true} ()
lemma-∧-0 {false} {false} ()
lemma-∧-0 {true} {true} eq1 ()

lemma-∧-1 : {a b : Bool} → a /\ b ≡ true → b ≡ false → ⊥
lemma-∧-1 {true} {false} ()
lemma-∧-1 {false} {true} ()
lemma-∧-1 {false} {false} ()
lemma-∧-1 {true} {true} eq1 ()

bool-and-tt : {a b : Bool} → a ≡ true → b ≡ true → ( a /\ b ) ≡ true
bool-and-tt refl refl = refl

bool-∧→tt-0 : {a b : Bool} → ( a /\ b ) ≡ true → a ≡ true
bool-∧→tt-0 {true} {true} eq =  refl
bool-∧→tt-0 {false} {_} ()

bool-∧→tt-1 : {a b : Bool} → ( a /\ b ) ≡ true → b ≡ true
bool-∧→tt-1 {true} {true} eq = refl
bool-∧→tt-1 {true} {false} ()
bool-∧→tt-1 {false} {false} ()

bool-or-1 : {a b : Bool} → a ≡ false → ( a \/ b ) ≡ b
bool-or-1 {false} {true} eq = refl
bool-or-1 {false} {false} eq = refl
bool-or-2 : {a b : Bool} → b ≡ false → (a \/ b ) ≡ a
bool-or-2 {true} {false} eq = refl
bool-or-2 {false} {false} eq = refl

bool-or-3 : {a : Bool} → ( a \/ true ) ≡ true
bool-or-3 {true} = refl
bool-or-3 {false} = refl

bool-or-31 : {a b : Bool} → b ≡ true  → ( a \/ b ) ≡ true
bool-or-31 {true} {true} eq = refl
bool-or-31 {false} {true} eq = refl

bool-or-4 : {a : Bool} → ( true \/ a ) ≡ true
bool-or-4 {true} = refl
bool-or-4 {false} = refl

bool-or-41 : {a b : Bool} → a ≡ true  → ( a \/ b ) ≡ true
bool-or-41 {true} {b} eq = refl

bool-and-1 : {a b : Bool} →  a ≡ false → (a /\ b ) ≡ false
bool-and-1 {false} {b} eq = refl
bool-and-2 : {a b : Bool} →  b ≡ false → (a /\ b ) ≡ false
bool-and-2 {true} {false} eq = refl
bool-and-2 {false} {false} eq = refl
bool-and-2 {true} {true} ()
bool-and-2 {false} {true} ()


