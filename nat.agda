module nat where

open import Data.Nat renaming ( zero to Zero ; suc to Suc ;  ℕ to Nat ; _⊔_ to _n⊔_ ) 
open import Data.Empty
open import Relation.Nullary
open import  Relation.Binary.PropositionalEquality
open import  logic


nat-<> : { x y : Nat } → x < y → y < x → ⊥
nat-<>  (s≤s x<y) (s≤s y<x) = nat-<> x<y y<x

nat-<≡ : { x : Nat } → x < x → ⊥
nat-<≡  (s≤s lt) = nat-<≡ lt

nat-≡< : { x y : Nat } → x ≡ y → x < y → ⊥
nat-≡< refl lt = nat-<≡ lt

¬a≤a : {la : Nat} → Suc la ≤ la → ⊥
¬a≤a  (s≤s lt) = ¬a≤a  lt

a<sa : {la : Nat} → la < Suc la 
a<sa {Zero} = s≤s z≤n
a<sa {Suc la} = s≤s a<sa 

=→¬< : {x : Nat  } → ¬ ( x < x )
=→¬< {Zero} ()
=→¬< {Suc x} (s≤s lt) = =→¬< lt

>→¬< : {x y : Nat  } → (x < y ) → ¬ ( y < x )
>→¬< (s≤s x<y) (s≤s y<x) = >→¬< x<y y<x

<-∨ : { x y : Nat } → x < Suc y → ( (x ≡ y ) ∨ (x < y) )
<-∨ {Zero} {Zero} (s≤s z≤n) = case1 refl
<-∨ {Zero} {Suc y} (s≤s lt) = case2 (s≤s z≤n)
<-∨ {Suc x} {Zero} (s≤s ())
<-∨ {Suc x} {Suc y} (s≤s lt) with <-∨ {x} {y} lt
<-∨ {Suc x} {Suc y} (s≤s lt) | case1 eq = case1 (cong (λ k → Suc k ) eq)
<-∨ {Suc x} {Suc y} (s≤s lt) | case2 lt1 = case2 (s≤s lt1)

max : (x y : Nat) → Nat
max Zero Zero = Zero
max Zero (Suc x) = (Suc x)
max (Suc x) Zero = (Suc x)
max (Suc x) (Suc y) = Suc ( max x y )

