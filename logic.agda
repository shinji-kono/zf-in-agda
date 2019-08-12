module logic where

open import Level
open import Relation.Nullary
open import Relation.Binary
open import Data.Empty


data Bool : Set where
   true : Bool
   false : Bool

record  _∧_  {n m : Level} (A  : Set n) ( B : Set m ) : Set (n ⊔ m) where
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

