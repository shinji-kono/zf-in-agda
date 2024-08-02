{-# OPTIONS --cubical-compatible --safe #-}

module nat where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Empty
open import Relation.Nullary
open import  Relation.Binary.PropositionalEquality
open import  Relation.Binary.Core
open import  Relation.Binary.Definitions
open import  logic
open import Level hiding ( zero ; suc )

=→¬< : {x : ℕ  } → ¬ ( x < x )
=→¬< {x} x<x with <-cmp x x
... | tri< a ¬b ¬c = ⊥-elim ( ¬b refl )
... | tri≈ ¬a b ¬c = ⊥-elim ( ¬a x<x )
... | tri> ¬a ¬b c = ⊥-elim ( ¬b refl )

>→¬< : {x y : ℕ  } → (x < y ) → ¬ ( y < x )
>→¬< {x} {y} x<y y<x with <-cmp x y
... | tri< a ¬b ¬c = ⊥-elim ( ¬c y<x )
... | tri≈ ¬a b ¬c = ⊥-elim ( ¬c y<x )
... | tri> ¬a ¬b c = ⊥-elim ( ¬a x<y )

nat-<> : { x y : ℕ } → x < y → y < x → ⊥
nat-<> {x} {y} x<y y<x with <-cmp x y
... | tri< a ¬b ¬c = ⊥-elim ( ¬c y<x )
... | tri≈ ¬a b ¬c = ⊥-elim ( ¬c y<x )
... | tri> ¬a ¬b c = ⊥-elim ( ¬a x<y )

a<sa : {la : ℕ} → la < suc la
a<sa {zero} = s≤s z≤n
a<sa {suc la} = s≤s a<sa

refl-≤s : {x : ℕ } → x ≤ suc x
refl-≤s {zero} = z≤n
refl-≤s {suc x} = s≤s (refl-≤s {x})

a≤sa : {x : ℕ } → x ≤ suc x
a≤sa = refl-≤s

nat-<≡ : { x : ℕ } → x < x → ⊥
nat-<≡ {x} x<x with <-cmp x x
... | tri< a ¬b ¬c = ⊥-elim ( ¬b refl )
... | tri≈ ¬a b ¬c = ⊥-elim ( ¬a x<x )
... | tri> ¬a ¬b c = ⊥-elim ( ¬a x<x )

nat-≡< : { x y : ℕ } → x ≡ y → x < y → ⊥
nat-≡< refl lt = nat-<≡ lt

nat-≤> : { x y : ℕ } → x ≤ y → y < x → ⊥
nat-≤>  {x} {y} x≤y y<x with <-cmp x y
... | tri< a ¬b ¬c = ⊥-elim ( ¬c y<x )
... | tri≈ ¬a b ¬c = ⊥-elim ( ¬c y<x )
... | tri> ¬a ¬b c = ⊥-elim (nat-<≡ (≤-trans c x≤y))

≤-∨ : { x y : ℕ } → x ≤ y → ( (x ≡ y ) ∨ (x < y) )
≤-∨ {x} {y} x≤y with <-cmp x y
... | tri< a ¬b ¬c = case2 a
... | tri≈ ¬a b ¬c = case1 b
... | tri> ¬a ¬b c = ⊥-elim ( nat-<≡ (≤-trans c x≤y))

<-∨ : { x y : ℕ } → x < suc y → ( (x ≡ y ) ∨ (x < y) )
<-∨ {x} {y} x<sy with <-cmp x y
... | tri< a ¬b ¬c = case2 a
... | tri≈ ¬a b ¬c = case1 b
... | tri> ¬a ¬b c = ⊥-elim ( nat-<≡ (≤-trans x<sy c ))

¬a≤a : {la : ℕ} → suc la ≤ la → ⊥
¬a≤a {x} sx≤x = ⊥-elim ( nat-≤> sx≤x a<sa )

max : (x y : ℕ) → ℕ
max zero zero = zero
max zero (suc x) = (suc x)
max (suc x) zero = (suc x)
max (suc x) (suc y) = suc ( max x y )

x≤max : (x y : ℕ) → x ≤ max x y
x≤max zero zero = ≤-refl
x≤max zero (suc x) = z≤n
x≤max (suc x) zero = ≤-refl
x≤max (suc x) (suc y) = s≤s( x≤max x y )

y≤max : (x y : ℕ) → y ≤ max x y
y≤max zero zero = ≤-refl
y≤max zero (suc x) = ≤-refl
y≤max (suc x) zero = z≤n
y≤max (suc x) (suc y) = s≤s( y≤max x y )

x≤y→max=y : (x y : ℕ) → x ≤ y → max x y ≡ y
x≤y→max=y zero zero x≤y = refl
x≤y→max=y zero (suc y) x≤y = refl
x≤y→max=y (suc x) (suc y) lt with <-cmp x y
... | tri< a ¬b ¬c = cong suc (x≤y→max=y x y (≤-trans a≤sa a))
... | tri≈ ¬a refl ¬c = cong suc (x≤y→max=y x y ≤-refl )
... | tri> ¬a ¬b c = ⊥-elim ( nat-≤> c lt )

y≤x→max=x : (x y : ℕ) → y ≤ x → max x y ≡ x
y≤x→max=x zero zero y≤x = refl
y≤x→max=x zero (suc y) ()
y≤x→max=x (suc x) zero lt = refl
y≤x→max=x (suc x) (suc y) lt with <-cmp y x
... | tri< a ¬b ¬c = cong suc (y≤x→max=x x y (≤-trans a≤sa a))
... | tri≈ ¬a refl ¬c = cong suc (y≤x→max=x x y ≤-refl )
... | tri> ¬a ¬b c = ⊥-elim ( nat-≤> c lt )


-- _*_ : ℕ → ℕ → ℕ
-- _*_ zero _ = zero
-- _*_ (suc n) m = m + ( n * m )

-- x ^ y
exp : ℕ → ℕ → ℕ
exp _ zero = 1
exp n (suc m) = n * ( exp n m )

div2 : ℕ → (ℕ ∧ Bool )
div2 zero =  ⟪ 0 , false ⟫
div2 (suc zero) =  ⟪ 0 , true ⟫
div2 (suc (suc n)) =  ⟪ suc (proj1 (div2 n)) , proj2 (div2 n) ⟫ where
    open _∧_

div2-rev : (ℕ ∧ Bool ) → ℕ
div2-rev ⟪ x , true ⟫ = suc (x + x)
div2-rev ⟪ x , false ⟫ = x + x

div2-eq : (x : ℕ ) → div2-rev ( div2 x ) ≡ x
div2-eq zero = refl
div2-eq (suc zero) = refl
div2-eq (suc (suc x)) with div2 x in eq1
... | ⟪ x1 , true ⟫ = begin -- eq1 : div2 x ≡ ⟪ x1 , true ⟫
     div2-rev ⟪ suc x1 , true ⟫ ≡⟨⟩
     suc (suc (x1 + suc x1)) ≡⟨ cong (λ k → suc (suc k )) (+-comm x1  _ ) ⟩
     suc (suc (suc (x1 + x1))) ≡⟨⟩
     suc (suc (div2-rev ⟪ x1 , true ⟫)) ≡⟨ cong (λ k → suc (suc (div2-rev k ))) (sym eq1) ⟩
     suc (suc (div2-rev (div2 x)))      ≡⟨ cong (λ k → suc (suc k)) (div2-eq x) ⟩
     suc (suc x) ∎  where open ≡-Reasoning
... | ⟪ x1 , false ⟫ = begin
     div2-rev ⟪ suc x1 , false ⟫ ≡⟨⟩
     suc (x1 + suc x1) ≡⟨ cong (λ k → (suc k )) (+-comm x1  _ ) ⟩
     suc (suc (x1 + x1)) ≡⟨⟩
     suc (suc (div2-rev ⟪ x1 , false ⟫)) ≡⟨ cong (λ k → suc (suc (div2-rev k ))) (sym eq1) ⟩
     suc (suc (div2-rev (div2 x)))      ≡⟨ cong (λ k → suc (suc k)) (div2-eq x) ⟩
     suc (suc x) ∎  where open ≡-Reasoning

sucprd : {i : ℕ } → 0 < i  → suc (pred i) ≡ i
sucprd {suc i} 0<i = refl

0<s : {x : ℕ } → zero < suc x
0<s {_} = s≤s z≤n

px<py : {x y : ℕ } → pred x  < pred y → x < y
px<py {zero} {suc y} lt = 0<s
px<py {suc x} {suc y} lt with <-cmp x y
... | tri< a ¬b ¬c = s≤s a
... | tri≈ ¬a b ¬c = ⊥-elim ( nat-≡< b lt )
... | tri> ¬a ¬b c = ⊥-elim ( nat-<> c lt )

minus : (a b : ℕ ) →  ℕ
minus a zero = a
minus zero (suc b) = zero
minus (suc a) (suc b) = minus a b

_-_ = minus

sn-m=sn-m : {m n : ℕ } →  m ≤ n → suc n - m ≡ suc ( n - m )
sn-m=sn-m {0} {n} m≤n = refl
sn-m=sn-m {suc m} {suc n} le with <-cmp m n
... | tri< a ¬b ¬c = sm00 where
    sm00 : suc n - m ≡ suc ( n - m )
    sm00 = sn-m=sn-m {m} {n} (≤-trans a≤sa a )
... | tri≈ ¬a refl ¬c = sn-m=sn-m {m} {n} ≤-refl
... | tri> ¬a ¬b c = ⊥-elim ( nat-≤> c le )

si-sn=i-n : {i n : ℕ } → n < i  → suc (i - suc n) ≡ (i - n)
si-sn=i-n {i} {n} n<i = begin
   suc (i - suc n) ≡⟨ sym (sn-m=sn-m n<i )  ⟩
   suc i - suc n ≡⟨⟩
   i - n
   ∎  where
      open ≡-Reasoning

n-m<n : (n m : ℕ ) →  n - m ≤ n
n-m<n zero zero = z≤n
n-m<n (suc n) zero = s≤s (n-m<n n zero)
n-m<n zero (suc m) = z≤n
n-m<n (suc n) (suc m) = ≤-trans (n-m<n n m ) refl-≤s

m-0=m : {m : ℕ } → m - zero ≡ m
m-0=m {zero} = refl
m-0=m {suc m} = cong suc (m-0=m {m})

m-m=0 : {m : ℕ } → m - m ≡ zero
m-m=0 {zero} = refl
m-m=0 {suc m} = m-m=0 {m}

refl-≤ : {x : ℕ } → x ≤ x
refl-≤ {zero} = z≤n
refl-≤ {suc x} = s≤s (refl-≤ {x})

refl-≤≡ : {x y : ℕ } → x ≡ y → x ≤ y
refl-≤≡ refl = refl-≤

px≤x : {x  : ℕ } → pred x ≤ x
px≤x {zero} = refl-≤
px≤x {suc x} = refl-≤s

px≤py : {x y : ℕ } → x ≤ y → pred x  ≤ pred y
px≤py {zero} {zero} x≤y = refl-≤
px≤py {suc x} {zero} ()
px≤py {zero} {suc y} le = z≤n
px≤py {suc x} {suc y} x≤y with <-cmp x y
... | tri< a ¬b ¬c = ≤-trans a≤sa a
... | tri≈ ¬a b ¬c = refl-≤≡ b
... | tri> ¬a ¬b c = ⊥-elim ( nat-≤> c x≤y )

n-n-m=m : {m n : ℕ } → m ≤ n  → m ≡ (n - (n - m))
n-n-m=m {0} {zero} le = refl
n-n-m=m {0} {suc n} lt = begin
    0 ≡⟨ sym (m-m=0 {suc n}) ⟩
    suc n - suc n
    ∎ where   open ≡-Reasoning
n-n-m=m {suc m} {suc n} le = begin
    suc m ≡⟨ cong suc ( n-n-m=m (px≤py le)) ⟩
    suc (n - (n - m)) ≡⟨ sym (sn-m=sn-m (n-m<n n m)) ⟩
    suc n - (n - m) ∎ where open ≡-Reasoning

m+= : {i j  m : ℕ } → m + i ≡ m + j → i ≡ j
m+= {i} {j} {zero} refl = refl
m+= {i} {j} {suc m} eq = m+= {i} {j} {m} ( cong (λ k → pred k ) eq )

+m= : {i j  m : ℕ } → i + m ≡ j + m → i ≡ j
+m= {i} {j} {m} eq = m+= ( subst₂ (λ j k → j ≡ k ) (+-comm i _ ) (+-comm j _ ) eq )

less-1 :  { n m : ℕ } → suc n < m → n < m
less-1 sn<m = <-trans a<sa sn<m

sa=b→a<b :  { n m : ℕ } → suc n ≡ m → n < m
sa=b→a<b {n} {m} sn=m = subst (λ k → n < k ) sn=m a<sa

minus+n : {x y : ℕ } → suc x > y  → minus x y + y ≡ x
minus+n {x} {zero} _ = trans (sym (+-comm zero  _ )) refl
minus+n {zero} {suc y} lt = ⊥-elim ( nat-≤> lt (≤-trans a<sa (s≤s (s≤s z≤n)) ))
minus+n {suc x} {suc y} y<sx with <-cmp y (suc x)
... | tri< a ¬b ¬c = begin
  minus (suc x) (suc y) + suc y ≡⟨ +-comm _ (suc y)    ⟩
  suc y + minus x y ≡⟨ cong ( λ k → suc k ) ( begin
     y + minus x y ≡⟨ +-comm y  _ ⟩
     minus x y + y ≡⟨ minus+n {x} {y} a  ⟩
     x ∎  ) ⟩
  suc x ∎  where open ≡-Reasoning
... | tri≈ ¬a b ¬c = ⊥-elim ( nat-≡< b (px≤py y<sx ))
... | tri> ¬a ¬b c = ⊥-elim ( nat-<> c (px≤py y<sx ))

+<-cong : {x y z : ℕ } → x < y →  z + x < z + y
+<-cong {x} {y} {zero} x<y = x<y
+<-cong {x} {y} {suc z} x<y = s≤s (+<-cong {x} {y} {z} x<y)

<-minus-0 : {x y z : ℕ } → z + x < z + y → x < y
<-minus-0 {x} {y} {z} x<y with <-cmp x y
... | tri< a ¬b ¬c = a
... | tri≈ ¬a b ¬c = ⊥-elim ( nat-≡< (cong (λ k → z + k ) b) x<y )
... | tri> ¬a ¬b c = ⊥-elim ( nat-<> x<y (+<-cong {y} {x} {z} c))

<-minus : {x y z : ℕ } → x + z < y + z → x < y
<-minus {x} {y} {z} lt = <-minus-0 ( subst₂ ( λ j k → j < k ) (+-comm x _) (+-comm y _ ) lt )

x≤x+y : {z y : ℕ } → z ≤ z + y
x≤x+y {zero} {y} = z≤n
x≤x+y {suc z} {y} = s≤s (x≤x+y {z} {y})

x≤y+x : {z y : ℕ } → z ≤ y + z
x≤y+x {z} {y} = subst (λ k → z ≤ k ) (+-comm _ y ) x≤x+y

x≤x+sy : {x y : ℕ} → x < x + suc y
x≤x+sy {x} {y} = begin
       suc x ≤⟨ x≤x+y ⟩
       suc x + y ≡⟨ cong (λ k → k + y) (+-comm 1 x ) ⟩
       (x + 1) + y ≡⟨ (+-assoc x 1 _) ⟩
       x + suc y ∎  where open ≤-Reasoning


<-plus-0 : {x y z : ℕ } → x < y → z + x < z + y
<-plus-0 = +<-cong

<-plus : {x y z : ℕ } → x < y → x + z < y + z
<-plus {x} {y} {z} x<y = subst₂ (λ j k → j < k ) (+-comm z x ) (+-comm z y ) ( <-plus-0 x<y )

≤-plus-0 : {x y z : ℕ } → x ≤ y → z + x ≤ z + y
≤-plus-0 {x} {y} {zero} lt = lt
≤-plus-0 {x} {y} {suc z} lt = s≤s ( ≤-plus-0 {x} {y} {z} lt )

≤-plus : {x y z : ℕ } → x ≤ y → x + z ≤ y + z
≤-plus {x} {y} {z} x≤y = subst₂ (λ j k → j ≤ k ) (+-comm z x ) (+-comm z y ) ( ≤-plus-0 x≤y )

x+y<z→x<z : {x y z : ℕ } → x + y < z → x < z
x+y<z→x<z {x} {zero} {z} xy<z = subst (λ k → k < z ) (+-comm x zero ) xy<z
x+y<z→x<z {x} {suc y} {z} xy<z = <-minus {x} {z} {suc y} (<-trans xy<z x≤x+sy )

*≤ : {x y z : ℕ } → x ≤ y → x * z ≤ y * z
*≤ lt = *-mono-≤ lt ≤-refl

<to≤ : {x y  : ℕ } → x < y → x ≤ y
<to≤ {x} {y} x<y with <-cmp x (suc y)
... | tri< a ¬b ¬c = px≤py a
... | tri≈ ¬a b ¬c = ⊥-elim ( nat-≡< b (≤-trans x<y a≤sa ))
... | tri> ¬a ¬b c = ⊥-elim ( nat-<> c (≤-trans x<y a≤sa ))

<sto≤ : {x y  : ℕ } → x < suc y → x ≤ y
<sto≤ {x} {y} x<sy with <-cmp x y
... | tri< a ¬b ¬c = <to≤ a
... | tri≈ ¬a refl ¬c = ≤-refl
... | tri> ¬a ¬b c = ⊥-elim ( nat-≤> c x<sy )

*< : {x y z : ℕ } → x < y → x * suc z < y * suc z
*< {x} {zero} {z} ()
*< {x} {suc y} {z} x<y = s≤s ( begin
   x * suc z ≤⟨ lem01 ⟩
   y * suc z  ≤⟨ x≤x+y ⟩
   y * suc z + z  ≡⟨ +-comm _ z  ⟩
   z + y * suc z ∎ ) where
      open ≤-Reasoning
      lem01 : x * suc z ≤ y * suc z
      lem01 = *-mono-≤ {x} {y} {suc z} (<sto≤ x<y)  ≤-refl

<to<s : {x y  : ℕ } → x < y → x < suc y
<to<s x<y = <-trans x<y a<sa

<tos<s : {x y  : ℕ } → x < y → suc x < suc y
<tos<s x<y = s≤s x<y

<∨≤ : ( x y : ℕ ) →  (x < y ) ∨ (y ≤ x)
<∨≤ x y with <-cmp x y
... | tri< a ¬b ¬c = case1 a
... | tri≈ ¬a refl ¬c = case2 ≤-refl
... | tri> ¬a ¬b c = case2 (<to≤ c)

x<y→≤ : {x y : ℕ } → x < y →  x ≤ suc y
x<y→≤ {x} {y} x<y with <-cmp x (suc y)
... | tri< a ¬b ¬c = <to≤ a
... | tri≈ ¬a b ¬c = refl-≤≡ b
... | tri> ¬a ¬b c = ⊥-elim ( ¬a ( ≤-trans x<y a≤sa ))

≤→= : {i j : ℕ} → i ≤ j → j ≤ i → i ≡ j
≤→= {i} {j} i≤j j≤i with <-cmp i j
... | tri< a ¬b ¬c = ⊥-elim ( nat-≤> j≤i a )
... | tri≈ ¬a b ¬c = b
... | tri> ¬a ¬b c = ⊥-elim ( nat-≤> i≤j c )

sx≤py→x≤y : {x y : ℕ } → suc x ≤ suc y → x  ≤ y
sx≤py→x≤y = px≤py

sx<py→x<y : {x y : ℕ } → suc x < suc y → x  < y
sx<py→x<y {x} {y} sx<sy with <-cmp x y
... | tri< a ¬b ¬c = a
... | tri≈ ¬a b ¬c = ⊥-elim ( nat-≡< (cong suc b) sx<sy )
... | tri> ¬a ¬b c = ⊥-elim ( nat-<> (s≤s c) sx<sy )

sx≤y→x≤y : {x y : ℕ } → suc x ≤ y → x  ≤ y
sx≤y→x≤y sx≤y = ≤-trans a≤sa sx≤y

x<sy→x≤y : {x y : ℕ } → x < suc y → x  ≤ y
x<sy→x≤y = <sto≤

x≤y→x<sy : {x y : ℕ } → x ≤ y → x < suc y
x≤y→x<sy {.zero} {y} z≤n = ≤-trans a<sa (s≤s z≤n)
x≤y→x<sy {.(suc _)} {.(suc _)} (s≤s le) = s≤s ( x≤y→x<sy le)

sx≤y→x<y : {x y : ℕ } → suc x ≤ y → x < y
sx≤y→x<y sx≤y = sx≤y

open import Data.Product

i-j=0→i=j : {i j  : ℕ } → j ≤ i  → i - j ≡ 0 → i ≡ j
i-j=0→i=j {i} {j} le j=0 = begin
    i  ≡⟨ sym (m-0=m) ⟩
    i - 0 ≡⟨ cong (λ k → i - k ) (sym j=0) ⟩
    i - (i - j ) ≡⟨ sym (n-n-m=m le) ⟩
    j ∎ where open ≡-Reasoning

m*n=0⇒m=0∨n=0 : {i j : ℕ} → i * j ≡ 0 → (i ≡ 0) ∨ ( j ≡ 0 )
m*n=0⇒m=0∨n=0 {zero} {j} eq = case1 refl
m*n=0⇒m=0∨n=0 {suc i} {zero} eq = case2 refl


minus+1 : {x y  : ℕ } → y ≤ x  → suc (minus x y)  ≡ minus (suc x) y
minus+1 {zero} {zero} y≤x = refl
minus+1 {suc x} {zero} y≤x = refl
minus+1 {suc x} {suc y} y≤x = minus+1 {x} {y} (sx≤py→x≤y y≤x)

minus+yz : {x y z : ℕ } → z ≤ y  → x + minus y z  ≡ minus (x + y) z
minus+yz {zero} {y} {z} _ = refl
minus+yz {suc x} {y} {z} z≤y = begin
         suc x + minus y z ≡⟨ cong suc ( minus+yz z≤y ) ⟩
         suc (minus (x + y) z) ≡⟨ minus+1 {x + y} {z} (≤-trans z≤y (subst (λ g → y ≤ g) (+-comm y x) x≤x+y) ) ⟩
         minus (suc x + y) z ∎  where open ≡-Reasoning

minus<=0 : {x y : ℕ } → x ≤ y → minus x y ≡ 0
minus<=0 {0} {zero} le = refl
minus<=0 {0} {suc y} le = refl
minus<=0 {suc x} {suc y} le = minus<=0 {x} {y} (sx≤py→x≤y le)

minus>0 : {x y : ℕ } → x < y → 0 < minus y x
minus>0 {zero} {suc _} lt = lt
minus>0 {suc x} {suc y} lt = minus>0 {x} {y} (sx<py→x<y lt)

minus>0→x<y : {x y : ℕ } → 0 < minus y x  → x < y
minus>0→x<y {x} {y} lt with <-cmp x y
... | tri< a ¬b ¬c = a
... | tri≈ ¬a refl ¬c = ⊥-elim ( nat-≡< (sym (minus<=0 {x} ≤-refl)) lt )
... | tri> ¬a ¬b c = ⊥-elim ( nat-≡< (sym (minus<=0 {y} (≤-trans refl-≤s c ))) lt )

minus+y-y : {x y : ℕ } → (x + y) - y  ≡ x
minus+y-y {zero} {y} = minus<=0 {zero + y} {y} ≤-refl
minus+y-y {suc x} {y} = begin
         (suc x + y) - y ≡⟨ sym (minus+1 {_} {y} x≤y+x) ⟩
         suc ((x + y) - y) ≡⟨ cong suc (minus+y-y {x} {y}) ⟩
         suc x ∎  where open ≡-Reasoning

minus+yx-yz : {x y z : ℕ } → (y + x) - (y + z)  ≡ x - z
minus+yx-yz {x} {zero} {z} = refl
minus+yx-yz {x} {suc y} {z} = minus+yx-yz {x} {y} {z}

minus+xy-zy : {x y z : ℕ } → (x + y) - (z + y)  ≡ x - z
minus+xy-zy {x} {y} {z} = subst₂ (λ j k → j - k ≡ x - z  ) (+-comm y x) (+-comm y z) (minus+yx-yz {x} {y} {z})

+cancel<l : (x z : ℕ ) {y : ℕ} → y + x < y + z → x < z
+cancel<l x z {zero} lt = lt
+cancel<l x z {suc y} lt = +cancel<l x z {y} (sx<py→x<y lt)

+cancel<r : (x z : ℕ ) {y : ℕ} → x + y < z + y → x < z
+cancel<r x z {y} lt = +cancel<l x z (subst₂ (λ j k → j < k ) (+-comm x _) (+-comm z _) lt )

minus<z : {x y z : ℕ } → x < y → z ≤ x → x - z < y - z
minus<z {x} {y} {z} x<y z≤x = +cancel<r _ _  ( begin
    suc ( (x - z) + z  ) ≡⟨ cong suc (minus+n (s≤s z≤x) )  ⟩
    suc x ≤⟨ x<y ⟩
    y ≡⟨ sym ( minus+n (<-trans (s≤s z≤x) (s≤s x<y) )) ⟩
    (y - z ) + z ∎ )  where open ≤-Reasoning


y-x<y : {x y : ℕ } → 0 < x → 0 < y  → y - x  <  y
y-x<y {x} {y} 0<x 0<y with <-cmp x (suc y)
... | tri< a ¬b ¬c = +cancel<r (y - x) _ ( begin
         suc ((y - x) + x) ≡⟨ cong suc (minus+n {y} {x} a ) ⟩
         suc y  ≡⟨ +-comm 1 _ ⟩
         y + suc 0  ≤⟨ +-mono-≤ ≤-refl 0<x ⟩
         y + x ∎ )  where open ≤-Reasoning
... | tri≈ ¬a refl ¬c = subst ( λ k → k < y ) (sym (minus<=0 {y} {x} refl-≤s )) 0<y
... | tri> ¬a ¬b c = subst ( λ k → k < y ) (sym (minus<=0 {y} {x} (≤-trans (≤-trans refl-≤s refl-≤s) c))) 0<y -- suc (suc y) ≤ x → y ≤ x

open import Relation.Binary.Definitions

distr-minus-* : {x y z : ℕ } → (minus x y) * z ≡ minus (x * z) (y * z)
distr-minus-* {x} {zero} {z} = refl
distr-minus-* {x} {suc y} {z} with <-cmp x y
distr-minus-* {x} {suc y} {z} | tri< a ¬b ¬c = begin
          minus x (suc y) * z
        ≡⟨ cong (λ k → k * z ) (minus<=0 {x} {suc y} (x<y→≤ a)) ⟩
           0 * z
        ≡⟨ sym (minus<=0 {x * z} {z + y * z} le ) ⟩
          minus (x * z) (z + y * z)
        ∎  where
            open ≡-Reasoning
            le : x * z ≤ z + y * z
            le  = ≤-trans lemma (subst (λ k → y * z ≤ k ) (+-comm _ z ) (x≤x+y {y * z} {z} ) ) where
               lemma : x * z ≤ y * z
               lemma = *≤ {x} {y} {z} (<to≤ a)
distr-minus-* {x} {suc y} {z} | tri≈ ¬a refl ¬c = begin
          minus x (suc y) * z
        ≡⟨ cong (λ k → k * z ) (minus<=0 {x} {suc y} refl-≤s ) ⟩
           0 * z
        ≡⟨ sym (minus<=0 {x * z} {z + y * z} (lt {x} {z} )) ⟩
          minus (x * z) (z + y * z)
        ∎  where
            open ≡-Reasoning
            lt : {x z : ℕ } →  x * z ≤ z + x * z
            lt {zero} {zero} = z≤n
            lt {suc x} {zero} = lt {x} {zero}
            lt {x} {suc z} = ≤-trans lemma refl-≤s where
               lemma : x * suc z ≤   z + x * suc z
               lemma = subst (λ k → x * suc z ≤ k ) (+-comm _ z) (x≤x+y {x * suc z} {z})
distr-minus-* {x} {suc y} {z} | tri> ¬a ¬b c = +m= {_} {_} {suc y * z} ( begin
           minus x (suc y) * z + suc y * z
        ≡⟨ sym (proj₂ *-distrib-+ z  (minus x (suc y) )  _) ⟩
           ( minus x (suc y) + suc y ) * z
        ≡⟨ cong (λ k → k * z) (minus+n {x} {suc y} (s≤s c))  ⟩
           x * z
        ≡⟨ sym (minus+n {x * z} {suc y * z} (s≤s (lt c))) ⟩
           minus (x * z) (suc y * z) + suc y * z
        ∎ ) where
            open ≡-Reasoning
            lt : {x y z : ℕ } → suc y ≤ x → z + y * z ≤ x * z
            lt {x} {y} {z} le = *≤ le

distr-minus-*' : {z x y : ℕ } → z * (minus x y)  ≡ minus (z * x) (z * y)
distr-minus-*' {z} {x} {y} = begin
        z * (minus x y) ≡⟨ *-comm _ (x - y) ⟩
        (minus x y) * z ≡⟨ distr-minus-* {x} {y} {z} ⟩
        minus (x * z) (y * z) ≡⟨ cong₂ (λ j k → j - k ) (*-comm x z ) (*-comm y z) ⟩
        minus (z * x) (z * y) ∎  where open ≡-Reasoning

minus- : {x y z : ℕ } → suc x > z + y → minus (minus x y) z ≡ minus x (y + z)
minus- {x} {y} {z} gt = +m= {_} {_} {z} ( begin
           minus (minus x y) z + z
        ≡⟨ minus+n {_} {z} lemma ⟩
           minus x y
        ≡⟨ +m= {_} {_} {y} ( begin
              minus x y + y
           ≡⟨ minus+n {_} {y} lemma1 ⟩
              x
           ≡⟨ sym ( minus+n {_} {z + y} gt ) ⟩
              minus x (z + y) + (z + y)
           ≡⟨ sym ( +-assoc (minus x (z + y)) _  _ ) ⟩
              minus x (z + y) + z + y
           ∎ ) ⟩
           minus x (z + y) + z
        ≡⟨ cong (λ k → minus x k + z ) (+-comm _ y )  ⟩
           minus x (y + z) + z
        ∎  ) where
             open ≡-Reasoning
             lemma1 : suc x > y
             lemma1 = x+y<z→x<z (subst (λ k → k < suc x ) (+-comm z _ ) gt )
             lemma : suc (minus x y) > z
             lemma = <-minus {_} {_} {y} ( subst ( λ x → z + y < suc x ) (sym (minus+n {x} {y}  lemma1 ))  gt )

sn≤1→n=0 : {n : ℕ } → suc n ≤ 1 → n ≡ 0
sn≤1→n=0 {n} sn≤1 with <-cmp n 0
... | tri≈ ¬a b ¬c = b
... | tri> ¬a ¬b c = ⊥-elim ( nat-≤> c sn≤1 )

minus-* : {M k n : ℕ } → n < k  → minus k (suc n) * M ≡ minus (minus k n * M ) M
minus-* {zero} {k} {n} lt = begin
           minus k (suc n) * zero
        ≡⟨ *-comm (minus k (suc n)) zero ⟩
           zero * minus k (suc n)
        ≡⟨⟩
           0 * minus k n
        ≡⟨ *-comm 0 (minus k n) ⟩
           minus (minus k n * 0 ) 0
        ∎  where
        open ≡-Reasoning
minus-* {suc m} {k} {n} lt with <-cmp k 1
minus-* {suc m} {k} {n} lt | tri< a ¬b ¬c = ⊥-elim ( nat-≤> (sx≤py→x≤y a) (≤-trans  (s≤s z≤n) lt) )
minus-* {suc m} {k} {n} lt | tri≈ ¬a refl ¬c =  subst (λ k → minus 0 k * suc m ≡ minus (minus 1 k * suc m) (suc m)) (sym n=0) lem  where
    n=0 : n ≡ 0
    n=0 = sn≤1→n=0 lt
    lem : minus 0 0 * suc m ≡ minus (minus 1 0 * suc m) (suc m)
    lem = begin
        minus 0 0 * suc m ≡⟨⟩
        0 ≡⟨ sym ( minus<=0 {suc m} {suc m} ≤-refl ) ⟩
        minus (suc m) (suc m) ≡⟨ cong (λ k → minus k (suc m)) (+-comm 0 (suc m) ) ⟩
        minus (suc m + 0) (suc m) ≡⟨⟩
        minus (minus 1 0 * suc m) (suc m) ∎ where open ≡-Reasoning
minus-* {suc m} {k} {n} lt | tri> ¬a ¬b c = begin
           minus k (suc n) * M
        ≡⟨ distr-minus-* {k} {suc n} {M}  ⟩
           minus (k * M ) ((suc n) * M)
        ≡⟨⟩
           minus (k * M ) (M + n * M  )
        ≡⟨ cong (λ x → minus (k * M) x) (+-comm M _ ) ⟩
           minus (k * M ) ((n * M) + M )
        ≡⟨ sym ( minus- {k * M} {n * M} (lemma lt) ) ⟩
           minus (minus (k * M ) (n * M)) M
        ≡⟨ cong (λ x → minus x M ) ( sym ( distr-minus-* {k} {n} )) ⟩
           minus (minus k n * M ) M
        ∎  where
             M = suc m
             lemma : {n k m : ℕ } → n < k  → suc (k * suc m) > suc m + n * suc m
             lemma {n} {k} {m} lt = ≤-plus-0 {_} {_} {1} (*≤ lt ) 
             open ≡-Reasoning

x=y+z→x-z=y : {x y z : ℕ } → x ≡ y + z → x - z ≡ y
x=y+z→x-z=y {x} {zero} {.x} refl = minus<=0 {x} {x} refl-≤ -- x ≡ suc (y + z) → (x ≡ y + z → x - z ≡ y)   → (x - z) ≡ suc y
x=y+z→x-z=y {suc x} {suc y} {zero} eq = begin -- suc x ≡ suc (y + zero) → (suc x - zero) ≡ suc y
       suc x - zero ≡⟨ refl ⟩
       suc x  ≡⟨ eq ⟩
       suc y + zero ≡⟨ +-comm _ zero ⟩
       suc y ∎  where open ≡-Reasoning
x=y+z→x-z=y {suc x} {suc y} {suc z} eq = x=y+z→x-z=y {x} {suc y} {z} ( begin
       x ≡⟨ cong pred eq ⟩
       pred (suc y + suc z) ≡⟨ +-comm _ (suc z)  ⟩
       suc z + y ≡⟨ cong suc ( +-comm _ y ) ⟩
       suc y + z ∎  ) where open ≡-Reasoning

m*1=m : {m : ℕ } → m * 1 ≡ m
m*1=m {zero} = refl
m*1=m {suc m} = cong suc m*1=m

+-cancel-1 : (x y z : ℕ ) → x + y  ≡ x + z  → y ≡ z
+-cancel-1 zero y z eq = eq
+-cancel-1 (suc x) y z eq = +-cancel-1 x y z (cong pred eq )

+-cancel-0 : (x y z : ℕ ) → y + x ≡ z + x → y ≡ z
+-cancel-0 x y z eq = +-cancel-1 x y z (trans (+-comm x y) (trans eq (sym (+-comm x z)) ))

*-cancel-left : {x y z : ℕ } → x > 0 → x * y ≡ x * z → y ≡ z
*-cancel-left {suc x} {zero} {zero} lt eq = refl
*-cancel-left {suc x} {zero} {suc z} lt eq = ⊥-elim ( nat-≡< eq (s≤s (begin
  x * zero  ≡⟨ *-comm x _ ⟩
  zero  ≤⟨ z≤n ⟩
  z + x * suc z ∎ ))) where open ≤-Reasoning
*-cancel-left {suc x} {suc y} {zero} lt eq = ⊥-elim ( nat-≡< (sym eq) (s≤s (begin
  x * zero  ≡⟨ *-comm x _ ⟩
  zero  ≤⟨ z≤n ⟩
  _ ∎ ))) where open ≤-Reasoning
*-cancel-left {suc x} {suc y} {suc z} lt eq with cong pred eq
... | eq1 =  cong suc (*-cancel-left {suc x} {y} {z} lt (+-cancel-0 x _ _ (begin
   y + x * y + x ≡⟨ +-assoc y _ _ ⟩
   y + (x * y + x) ≡⟨ cong (λ k → y + (k + x)) (*-comm x _)  ⟩
   y + (y * x + x) ≡⟨ cong (_+_ y) (+-comm _ x) ⟩
   y + (x + y * x ) ≡⟨ refl ⟩
   y + suc y * x ≡⟨ cong (_+_ y) (*-comm (suc y) _)  ⟩
   y + x * suc y ≡⟨ eq1 ⟩
   z + x * suc z ≡⟨ refl ⟩
   _ ≡⟨ sym ( cong (_+_ z) (*-comm (suc z) _) ) ⟩
   _ ≡⟨ sym ( cong (_+_ z) (+-comm _ x)) ⟩
   z + (z * x + x) ≡⟨ sym ( cong (λ k → z + (k + x)) (*-comm x _) ) ⟩
   z + (x * z + x) ≡⟨ sym ( +-assoc z _ _) ⟩
   z + x * z + x  ∎ ))) where open ≡-Reasoning

record Finduction {n m : Level} (P : Set n ) (Q : P → Set m ) (f : P → ℕ) : Set  (n Level.⊔ m) where
  field
    fzero   : {p : P} → f p ≡ zero → Q p
    pnext : (p : P ) → P
    decline : {p : P} → 0 < f p  → f (pnext p) < f p
    ind : {p : P} → Q (pnext p) → Q p

y<sx→y≤x : {x y : ℕ} → y < suc x → y ≤ x
y<sx→y≤x = x<sy→x≤y

fi0 : (x : ℕ) → x ≤ zero → x ≡ zero
fi0 .0 z≤n = refl

f-induction : {n m : Level} {P : Set n } → {Q : P → Set m }
  → (f : P → ℕ)
  → Finduction P Q f
  → (p : P ) → Q p
f-induction {n} {m} {P} {Q} f I p with <-cmp 0 (f p)
... | tri> ¬a ¬b ()
... | tri≈ ¬a b ¬c = Finduction.fzero I (sym b)
... | tri< lt _ _ = f-induction0 p (f p) (<to≤ (Finduction.decline I lt)) where
   f-induction0 : (p : P) → (x : ℕ) → (f (Finduction.pnext I p)) ≤ x → Q p
   f-induction0 p zero le = Finduction.ind I (Finduction.fzero I (fi0 _ le))
   f-induction0 p (suc x) le with <-cmp (f (Finduction.pnext I p)) (suc x)
   ... | tri< a ¬b ¬c = f-induction0 p x (px≤py a)
   ... | tri≈ ¬a b ¬c = Finduction.ind I (f-induction0 (Finduction.pnext I p) x (y<sx→y≤x f1)) where
       f1 : f (Finduction.pnext I (Finduction.pnext I p)) < suc x
       f1 = subst (λ k → f (Finduction.pnext I (Finduction.pnext I p)) < k ) b ( Finduction.decline I {Finduction.pnext I p}
         (subst (λ k → 0 < k ) (sym b) (s≤s z≤n ) ))
   ... | tri> ¬a ¬b c = ⊥-elim ( nat-≤> le c )
 

record Ninduction {n m : Level} (P : Set n ) (Q : P → Set m ) (f : P → ℕ) : Set  (n Level.⊔ m) where
  field
    pnext : (p : P ) → P
    fzero   : {p : P} → f (pnext p) ≡ zero → Q p
    decline : {p : P} → 0 < f p  → f (pnext p) < f p
    ind : {p : P} → Q (pnext p) → Q p

s≤s→≤ : { i j : ℕ} → suc i ≤ suc j → i ≤ j
s≤s→≤ = sx≤py→x≤y

n-induction : {n m : Level} {P : Set n } → {Q : P → Set m }
  → (f : P → ℕ)
  → Ninduction P Q f
  → (p : P ) → Q p
n-induction {n} {m} {P} {Q} f I p  = f-induction0 p (f (Ninduction.pnext I p)) ≤-refl where
   f-induction0 : (p : P) → (x : ℕ) → (f (Ninduction.pnext I p)) ≤ x  →  Q p
   f-induction0 p zero lt = Ninduction.fzero I {p} (fi0 _ lt)
   f-induction0 p (suc x) le with <-cmp (f (Ninduction.pnext I p)) (suc x)
   ... | tri< a  ¬b ¬c = f-induction0 p x (px≤py a)
   ... | tri≈ ¬a b ¬c = Ninduction.ind I (f-induction0 (Ninduction.pnext I p) x (s≤s→≤ nle) ) where
      f>0 :  0 < f (Ninduction.pnext I p)
      f>0 = subst (λ k → 0 < k ) (sym b) ( s≤s z≤n )
      nle : suc (f (Ninduction.pnext I (Ninduction.pnext I p))) ≤ suc x
      nle = subst (λ k → suc (f (Ninduction.pnext I (Ninduction.pnext I p))) ≤ k) b (Ninduction.decline I {Ninduction.pnext I p} f>0 )
   ... | tri> ¬a ¬b c = ⊥-elim ( nat-≤> le c )
 

record Factor (n m : ℕ ) : Set where
   field
      factor : ℕ
      remain : ℕ
      is-factor : factor * n + remain ≡ m

record Factor< (n m : ℕ ) : Set where
   field
      factor : ℕ
      remain : ℕ
      is-factor : factor * n + remain ≡ m
      remain<n : remain < n

record Dividable (n m : ℕ ) : Set where
   field
      factor : ℕ
      is-factor : factor * n + 0 ≡ m

open Factor

DtoF : {n m : ℕ} → Dividable n m → Factor n m
DtoF {n} {m} record { factor = f ; is-factor = fa } = record { factor = f ; remain = 0 ; is-factor = fa }

FtoD : {n m : ℕ} → (fc : Factor n m) → remain fc ≡ 0 → Dividable n m
FtoD {n} {m} record { factor = f ; remain = r ; is-factor = fa } refl = record { factor = f ; is-factor = fa }

--divdable^2 : ( n k : ℕ ) → Dividable k ( n * n ) → Dividable k n
--divdable^2 n k dn2 = {!!}

decf : { n k : ℕ } → ( x : Factor k (suc n) ) → Factor k n
decf {n} {k} record { factor = f ; remain = r ; is-factor = fa } =
 decf1 {n} {k} f r fa where
  decf1 : { n k : ℕ } → (f r : ℕ) → (f * k + r ≡ suc n)  → Factor k n
  decf1 {n} {k} f (suc r) fa  =  -- this case must be the first
     record { factor = f ; remain = r ; is-factor = ( begin -- fa : f * k + suc r ≡ suc n
        f * k + r ≡⟨ cong pred ( begin
          suc ( f * k + r ) ≡⟨ +-comm _ r ⟩
          r + suc (f * k)  ≡⟨ sym (+-assoc r 1 _) ⟩
          (r + 1) + f * k ≡⟨ cong (λ t → t + f * k ) (+-comm r 1) ⟩
          (suc r ) + f * k ≡⟨ +-comm (suc r) _ ⟩
          f * k + suc r  ≡⟨ fa ⟩
          suc n ∎ ) ⟩
        n ∎ ) }  where open ≡-Reasoning
  decf1 {n} {zero} (suc f) zero fa  = ⊥-elim ( nat-≡< fa (
        begin suc (suc f * zero + zero) ≡⟨ cong suc (+-comm _ zero)  ⟩
        suc (f * 0) ≡⟨ cong suc (*-comm f zero)  ⟩
        suc zero ≤⟨ s≤s z≤n ⟩
        suc n ∎ )) where open ≤-Reasoning
  decf1 {n} {suc k} (suc f) zero fa  =
     record { factor = f ; remain = k ; is-factor = ( begin -- fa : suc (k + f * suc k + zero) ≡ suc n
        f * suc k + k ≡⟨ +-comm _ k ⟩
        k + f * suc k ≡⟨ +-comm zero _ ⟩
        (k + f * suc k) + zero  ≡⟨ cong pred fa ⟩
        n ∎ ) }  where open ≡-Reasoning

div0 :  {k : ℕ} → Dividable k 0
div0 {k} = record { factor = 0; is-factor = refl }

div= :  {k : ℕ} → Dividable k k
div= {k} = record { factor = 1; is-factor = ( begin
        k + 0 * k + 0  ≡⟨ trans ( +-comm _ 0) ( +-comm _ 0) ⟩
        k ∎ ) }  where open ≡-Reasoning

div1 : { k : ℕ } → k > 1 →  ¬  Dividable k 1
div1 {k} k>1 record { factor = f1 ; is-factor = fa } = ⊥-elim ( nat-≡< (sym fa) ( begin
     2 ≤⟨ k>1 ⟩
     k ≡⟨ +-comm 0 _ ⟩
     k + 0 ≡⟨ refl  ⟩
     1 * k ≤⟨ *-mono-≤ {1} {f1} (lem1 _ fa) ≤-refl ⟩
     f1 * k ≡⟨ +-comm 0 _ ⟩
     f1 * k + 0 ∎  )) where 
        open ≤-Reasoning
        lem1 :  (f1 : ℕ) → f1 * k + 0 ≡ 1 → 1 ≤ f1
        lem1 zero ()
        lem1 (suc f1) eq = s≤s z≤n
  
div+div : { i j k : ℕ } →  Dividable k i →  Dividable k j → Dividable k (i + j) ∧ Dividable k (j + i)
div+div {i} {j} {k} di dj = ⟪ div+div1 , subst (λ g → Dividable k g) (+-comm i j) div+div1 ⟫ where
      fki = Dividable.factor di
      fkj = Dividable.factor dj
      div+div1 : Dividable k (i + j)
      div+div1 = record { factor = fki + fkj  ; is-factor = ( begin
          (fki + fkj) * k + 0 ≡⟨ +-comm _ 0 ⟩
          (fki + fkj) * k  ≡⟨ *-distribʳ-+ k fki _ ⟩
          fki * k + fkj * k  ≡⟨ cong₂ ( λ i j → i + j ) (+-comm 0 (fki * k)) (+-comm 0 (fkj * k)) ⟩
          (fki * k + 0) + (fkj * k + 0) ≡⟨ cong₂ ( λ i j → i + j ) (Dividable.is-factor di) (Dividable.is-factor dj) ⟩
          i + j  ∎ ) } where
             open ≡-Reasoning

div-div : { i j k : ℕ } → k > 1 →  Dividable k i →  Dividable k j → Dividable k (i - j) ∧ Dividable k (j - i)
div-div {i} {j} {k} k>1 di dj = ⟪ div-div1 di dj , div-div1 dj di ⟫ where
      div-div1 : {i j : ℕ } → Dividable k i →  Dividable k j → Dividable k (i - j)
      div-div1 {i} {j} di dj = record { factor = fki - fkj  ; is-factor = ( begin
          (fki - fkj) * k + 0 ≡⟨ +-comm _ 0 ⟩
          (fki - fkj) * k  ≡⟨ distr-minus-* {fki} {fkj}  ⟩
          (fki * k) - (fkj * k)  ≡⟨ cong₂ ( λ i j → i - j ) (+-comm 0 (fki * k)) (+-comm 0 (fkj * k)) ⟩
          (fki * k + 0) - (fkj * k + 0) ≡⟨ cong₂ ( λ i j → i - j ) (Dividable.is-factor di) (Dividable.is-factor dj) ⟩
          i - j  ∎ ) } where
             open ≡-Reasoning
             fki = Dividable.factor di
             fkj = Dividable.factor dj

open _∧_

div+1 : { i k : ℕ } → k > 1 →  Dividable k i →  ¬ Dividable k (suc i)
div+1 {i} {k} k>1 d d1 = div1 k>1 div+11 where
   div+11 : Dividable k 1
   div+11 = subst (λ g → Dividable k g) (minus+y-y {1} {i} ) ( proj2 (div-div k>1 d d1  ) )

div<k : { m k : ℕ } → k > 1 → m > 0 →  m < k →  ¬ Dividable k m
div<k {m} {k} k>1 m>0 m<k d = ⊥-elim ( nat-≤> (div<k1 (Dividable.factor d) (Dividable.is-factor d)) m<k ) where
    div<k1 : (f : ℕ ) → f * k + 0 ≡ m → k ≤ m
    div<k1 zero eq = ⊥-elim (nat-≡< eq m>0 )
    div<k1 (suc f) eq = begin
          k ≤⟨ x≤x+y ⟩
          k + (f * k + 0) ≡⟨ sym (+-assoc k _ _) ⟩
          k + f * k + 0 ≡⟨ eq ⟩
          m ∎  where open ≤-Reasoning

0<factor : { m k : ℕ } → k > 0 → m > 0 →  (d :  Dividable k m ) → Dividable.factor d > 0
0<factor {m} {k} k>0 m>0 d with Dividable.factor d in eq1
... | zero = ⊥-elim ( nat-≡< ff1 m>0 ) where
    ff1 : 0 ≡ m
    ff1 = begin
          0 ≡⟨⟩
          0 * k + 0 ≡⟨ cong  (λ j → j * k + 0) (sym eq1) ⟩
          Dividable.factor d * k + 0 ≡⟨ Dividable.is-factor d  ⟩
          m ∎  where open ≡-Reasoning
... | suc t = s≤s z≤n

div→k≤m : { m k : ℕ } → k > 1 → m > 0 →  Dividable k m → m ≥ k
div→k≤m {m} {k} k>1 m>0 d with <-cmp m k
... | tri< a ¬b ¬c = ⊥-elim ( div<k k>1 m>0 a d )
... | tri≈ ¬a refl ¬c = ≤-refl
... | tri> ¬a ¬b c = <to≤ c

div1*k+0=k : {k : ℕ } → 1 * k + 0 ≡ k
div1*k+0=k {k} =  begin
   1 * k + 0 ≡⟨ cong (λ g → g + 0) (+-comm _ 0) ⟩
   k + 0 ≡⟨ +-comm _ 0 ⟩
   k  ∎ where open ≡-Reasoning


factor< : {k m : ℕ} → k > 1 → Factor< k m
factor< {k} {m} k>1 = n-induction {_} {_} {ℕ} {λ m → Factor< k m} F I m where
    F : ℕ → ℕ 
    F m = m
    F0 : ( m : ℕ ) → F (m - k) ≡ 0 → Factor< k m
    F0 0 eq = record { factor = 0 ; remain = 0 ; is-factor = refl ; remain<n = <-trans a<sa k>1 }
    F0 (suc m) eq with <-cmp k (suc m)
    ... | tri< a ¬b ¬c = record { factor = 1 ; remain = 0 ; is-factor = lem00 ; remain<n = <-trans a<sa k>1 } where
         lem00 :  k + zero + 0 ≡ suc m
         lem00 = begin  -- minus (suc m) k ≡ 0
            k + zero + 0 ≡⟨ +-comm (k + 0) _  ⟩
            k + 0 ≡⟨ +-comm k _  ⟩
            k ≡⟨ sym ( i-j=0→i=j (≤-trans a≤sa a) eq ) ⟩
            suc m ∎ where open ≡-Reasoning
    ... | tri≈ ¬a b ¬c = record { factor = 1 ; remain = 0 ; is-factor = trans (trans (+-comm (k + 0) _) (+-comm k 0)) b ; remain<n = <-trans a<sa k>1 }
    ... | tri> ¬a ¬b c = record { factor = 0 ; remain = suc m ; is-factor = refl ; remain<n = c } 
    ind : {m : ℕ} → Factor< k (m - k) → Factor< k m
    ind {m} record { factor = f ; remain = r ; is-factor = isf ; remain<n = r<n } with <-cmp k (suc m)
    ... | tri≈ ¬a b ¬c = record { factor = 0 ; remain = m ; is-factor = refl ; remain<n = subst (λ j → m < j) (sym b) a<sa } 
    ... | tri> ¬a ¬b c = record { factor = 0 ; remain = m ; is-factor = refl ; remain<n = <-trans a<sa c } 
    ... | tri< a ¬b ¬c = record { factor = suc f ; remain = r ; is-factor = lem00 ; remain<n = r<n } where
          k<sm : k < suc m
          k<sm = a
          lem00 : k + f * k + r ≡ m
          lem00 = begin
             k + f * k + r  ≡⟨ +-assoc k _ _  ⟩
             k + (f * k + r)  ≡⟨ +-comm k _  ⟩
             (f * k + r) + k  ≡⟨ cong (λ i → i + k ) isf ⟩
             (m - k) + k  ≡⟨ minus+n k<sm  ⟩
             m ∎ where open ≡-Reasoning
    decl : {m  : ℕ } → 0 < m → m - k < m
    decl {m} 0<m = y-x<y (<-trans a<sa k>1 ) 0<m 
    I : Ninduction ℕ  _  F
    I = record {
              pnext = λ p → p - k
            ; fzero = λ {m} eq → F0 m eq
            ; decline = λ {m} lt → decl lt
            ; ind = λ {p} prev → ind prev
       } 

Factor<→¬k≤m : {k m : ℕ} → k ≤ m  → (x : Factor< k m ) → Factor<.factor x > 0
Factor<→¬k≤m {k} {m} k≤m x with Factor<.factor x in eqx
... | zero = ⊥-elim ( nat-≤> k≤m (begin
     suc m  ≡⟨ cong suc (sym (Factor<.is-factor x)) ⟩
     suc (Factor<.factor x * k + Factor<.remain x)  ≡⟨ cong (λ j → suc (j * k + _)) eqx ⟩
     suc (0 * k + Factor<.remain x)  ≡⟨ refl ⟩
     suc (Factor<.remain x)  ≤⟨ Factor<.remain<n x ⟩
     k ∎ ) ) where open ≤-Reasoning
... | suc fa = s≤s z≤n

Factor<-inject : {k m : ℕ} → k > 1 → (x y : Factor< k m) → (Factor<.factor x ≡ Factor<.factor y ) ∧ (Factor<.remain x ≡ Factor<.remain y ) 
Factor<-inject {k} {m} k>1 x y = n-induction {_} {_} {ℕ} 
      {λ m → (x y : Factor< k m) → (Factor<.factor x ≡ Factor<.factor y ) ∧ (Factor<.remain x ≡ Factor<.remain y ) } F I m x y where
    F : ℕ → ℕ 
    F m = m
    f00 : (m : ℕ ) → ( k ≡ suc m ) → (x y : Factor< k (suc m)) → (Factor<.factor x ≡ Factor<.factor y ) ∧ (Factor<.remain x ≡ Factor<.remain y )  
    f00 m lem00 x y = ⟪ trans (lem02 x) (sym (lem02 y)) , trans (lem01 x) (sym (lem01 y)) ⟫ where
         lem02 :  (f : Factor< k (suc m)) → Factor<.factor f ≡ 1
         lem02 f with <-cmp (Factor<.factor f) 1
         ... | tri< a ¬b ¬c = ⊥-elim ( nat-≡< (Factor<.is-factor f) (begin
             suc (Factor<.factor f * k + Factor<.remain f)  ≤⟨ s≤s (≤-plus {_} {_} {Factor<.remain f} (*≤ (px≤py a)) ) ⟩
             suc (0 * k + Factor<.remain f)  ≡⟨⟩
             suc (0 + Factor<.remain f)  ≡⟨⟩
             suc (Factor<.remain f)  ≤⟨ Factor<.remain<n f ⟩
             k  ≡⟨ lem00 ⟩
             suc m ∎ )) where open ≤-Reasoning
         ... | tri≈ ¬a b ¬c = b
         ... | tri> ¬a ¬b c = ⊥-elim ( nat-≡< (sym (Factor<.is-factor f)) (begin -- 1 < Factor<. factor f, fa * k + r > k ≡ suc m
             suc (suc m) ≡⟨ cong suc (sym lem00) ⟩
             suc k ≡⟨ sym (+-comm k 1) ⟩
             k + 1 <⟨ <-plus-0 k>1  ⟩
             k + k  ≡⟨ cong (λ j → k + j) (+-comm 0 _ ) ⟩
             k + (k + 0)  ≡⟨⟩
             k + (k + 0 * k)  ≡⟨ refl ⟩
             2 * k ≤⟨ *≤ c ⟩ 
             Factor<.factor f * k ≤⟨ x≤x+y   ⟩ 
             Factor<.factor f * k + Factor<.remain f ∎ ) ) where open ≤-Reasoning
         lem03 : k ≡ 1 * k
         lem03 = +-comm 0 k 
         lem01 :  (f : Factor< k (suc m)) → Factor<.remain f ≡ 0
         lem01 f = +-cancel-1 _ _ _ ( begin
             Factor<.factor f * k + Factor<.remain f  ≡⟨ Factor<.is-factor f ⟩
             suc m  ≡⟨ sym lem00 ⟩
             k  ≡⟨ +-comm 0 k ⟩
             k + 0  ≡⟨ cong (λ j → j + 0) lem03  ⟩
             1 * k + 0  ≡⟨ cong (λ j → j * k + 0) (sym (lem02 f))  ⟩
             Factor<.factor f * k + 0  ∎ ) where open ≡-Reasoning
    F0 : ( m : ℕ ) → F (m - k) ≡ 0 → (x y : Factor< k m) → (Factor<.factor x ≡ Factor<.factor y ) ∧ (Factor<.remain x ≡ Factor<.remain y )  
    F0 0 eq x y = ⟪ trans (lem00 x) (sym (lem00 y)) , trans (lem01 x) (sym (lem01 y)) ⟫ where
         lem01 : (f : Factor< k 0) → Factor<.remain f ≡ 0
         lem01 f with Factor<.remain f in eq1
         ... | zero = refl
         ... | suc n = ⊥-elim ( nat-≡< (sym (Factor<.is-factor f)) (begin
             suc 0 ≤⟨ s≤s z≤n ⟩
             suc n ≡⟨ sym eq1 ⟩
             Factor<.remain f ≡⟨ refl ⟩
             0 + Factor<.remain f ≤⟨ x≤y+x ⟩
             Factor<.factor f * k + Factor<.remain f  ∎ ) ) where open ≤-Reasoning
         lem00 : (f : Factor< k 0) → Factor<.factor f ≡ 0
         lem00 f with m*n=0⇒m=0∨n=0 {Factor<.factor f} {k} (trans (+-comm 0 (Factor<.factor f * k) ) (subst (λ j → _ + j ≡ 0) (lem01 f) (Factor<.is-factor f))) 
         ... | case1 fa=0 = fa=0
         ... | case2 k=0 = ⊥-elim (nat-≡< (sym k=0) (<-trans a<sa k>1) )
    F0 (suc m) eq x y with <-cmp k (suc m)
    ... | tri< a ¬b ¬c = ⊥-elim ( ¬b lem00 ) where 
         lem00 :  k ≡ suc m
         lem00 = begin  
            k ≡⟨ sym ( i-j=0→i=j (≤-trans a≤sa a) eq ) ⟩
            suc m ∎ where open ≡-Reasoning
    ... | tri≈ ¬a b ¬c = f00 m b x y
    ... | tri> ¬a ¬b c = ⟪ trans ( lem00 x ) (sym (lem00 y)) , trans (lem01 x) (sym (lem01 y)) ⟫ where
         lem00 : (f : Factor< k (suc m)) → Factor<.factor f ≡ 0
         lem00 f with Factor<.factor f in eq1
         ... | zero = refl
         ... | suc fa = ⊥-elim ( nat-≡< (sym (Factor<.is-factor f)) (begin
             suc (suc m) ≤⟨ c ⟩
             k  ≤⟨  x≤x+y ⟩
             k + Factor<.remain f  ≡⟨ cong (λ j → j + _) (+-comm 0 k)  ⟩
             suc 0 * k + Factor<.remain f  ≤⟨ ≤-plus {_} {_} {Factor<.remain f} (*≤ {suc 0} {suc fa} {k} (s≤s z≤n)) ⟩
             suc fa * k + Factor<.remain f  ≡⟨ cong (λ j → j * k + Factor<.remain f) (sym eq1)   ⟩
             Factor<.factor f * k + Factor<.remain f  ∎ ) ) where open ≤-Reasoning
         lem01 : (f : Factor< k (suc m)) → Factor<.remain f ≡ (suc m)
         lem01 f = begin 
             Factor<.remain f ≡⟨ refl ⟩
             0 * k + Factor<.remain f ≡⟨ cong (λ j → j * k + Factor<.remain f) (sym (lem00 f))  ⟩
             Factor<.factor f * k + Factor<.remain f ≡⟨ Factor<.is-factor f ⟩
             suc m ∎ where open ≡-Reasoning
    ind : {m : ℕ} 
        → ( (x y : Factor< k (m - k)) → (Factor<.factor x ≡ Factor<.factor y ) ∧ (Factor<.remain x ≡ Factor<.remain y ) )
        → (x y : Factor< k m) → (Factor<.factor x ≡ Factor<.factor y ) ∧ (Factor<.remain x ≡ Factor<.remain y )
    ind {m} prev x y with <∨≤ m k
    ... | case1 m<k = ⟪ trans (lem00 x) (sym (lem00 y)) , trans (lem01 x) (sym (lem01 y)) ⟫ where
         lem00 : (x : Factor< k m ) → Factor<.factor x ≡ 0    
         lem00 x with Factor<.factor x in eqx
         ... | zero = refl
         ... | suc fa = ⊥-elim ( nat-≤> (begin
             k ≤⟨ x≤x+y  ⟩ 
             k +  (fa * k + Factor<.remain x) ≡⟨ sym (+-assoc k _ _) ⟩
             ( k +  fa * k )  + Factor<.remain x ≡⟨ refl ⟩
             suc fa * k  + Factor<.remain x ≡⟨ cong (λ j → j * k + Factor<.remain x) (sym eqx) ⟩
             Factor<.factor x * k  + Factor<.remain x ≡⟨ Factor<.is-factor x ⟩
             m ∎  )
           m<k ) where open ≤-Reasoning
         lem01 : (f : Factor< k m) → Factor<.remain f ≡ m
         lem01 f = begin 
             Factor<.remain f ≡⟨ refl ⟩
             0 * k + Factor<.remain f ≡⟨ cong (λ j → j * k + Factor<.remain f) (sym (lem00 f))  ⟩
             Factor<.factor f * k + Factor<.remain f ≡⟨ Factor<.is-factor f ⟩
             m ∎ where open ≡-Reasoning
    ... | case2 k≤m = px=py x y k≤m where
         lem07 : (x : Factor< k m ) → {fa : ℕ } → suc fa ≡ Factor<.factor x →  fa *  k + Factor<.remain x ≡ m - k
         lem07 x {fa} eq1 = begin
              fa * k + Factor<.remain x ≡⟨ sym (minus+y-y {_} {k} ) ⟩
              (fa * k + Factor<.remain x + k ) - k ≡⟨ cong (λ j → j - k) ( begin 
                  fa * k + Factor<.remain x + k ≡⟨ +-assoc (fa * k) _ _ ⟩
                  fa * k + (Factor<.remain x + k)   ≡⟨ cong (λ j → fa * k + j) (+-comm _ k) ⟩
                  fa * k + (k + Factor<.remain x )   ≡⟨ sym (+-assoc (fa * k) k _ ) ⟩
                  (fa * k + k) + Factor<.remain x    ≡⟨ cong (λ j → j + Factor<.remain x ) (+-comm (fa * k) k) ⟩
                  suc fa * k + Factor<.remain x   ≡⟨ cong (λ j → j * k + _) (eq1) ⟩ 
                  Factor<.factor x * k + Factor<.remain x ∎ ) ⟩
              (Factor<.factor x * k + Factor<.remain x) - k  ≡⟨ cong (λ j → j - k ) (Factor<.is-factor x) ⟩
              m - k ∎ where open ≡-Reasoning
         px=py : (x y : Factor< k m) → k ≤ m → (Factor<.factor x ≡ Factor<.factor y ) ∧ (Factor<.remain x ≡ Factor<.remain y ) 
         px=py x y k≤m with Factor<.factor x in eqx | Factor<.factor y in eqy
         ... | zero | _ = ⊥-elim ( nat-≡< (sym eqx) (Factor<→¬k≤m k≤m x) )
         ... | _ | zero = ⊥-elim ( nat-≡< (sym eqy) (Factor<→¬k≤m k≤m y) )
         ... | suc fx | suc fy with  prev 
             record { factor = fx ; remain = Factor<.remain x ; is-factor = lem07 x (sym eqx) ; remain<n = Factor<.remain<n x }
             record { factor = fy ; remain = Factor<.remain y ; is-factor = lem07 y (sym eqy) ; remain<n = Factor<.remain<n y }
         ... | ⟪ eqf , eqr ⟫ = ⟪ cong suc eqf , eqr ⟫
    decl : {m  : ℕ } → 0 < m → m - k < m
    decl {m} 0<m = y-x<y (<-trans a<sa k>1 ) 0<m 
    I : Ninduction ℕ  _  F
    I = record {
              pnext = λ p → p - k
            ; fzero = λ {m} eq → F0 m eq
            ; decline = λ {m} lt → decl lt
            ; ind = λ {p} prev → ind prev
       } 

F<toD : {n m : ℕ} → (fc : Factor< n m) → Factor<.remain fc ≡ 0 → Dividable n m
F<toD {n} {m} record { factor = f ; remain = r ; is-factor = fa ; remain<n = _ } refl 
    = record { factor = f ; is-factor = fa }

DtoF< : {n m : ℕ} → Dividable n m → 0 < n → Factor< n m
DtoF< {n} {m} record { factor = f ; is-factor = fa } 0<n = record { factor = f ; is-factor = fa  ; remain = 0 ; remain<n = 0<n }

F<to¬D : {n m nx : ℕ} → (fc : Factor< n m) → 1 < n → Factor<.remain fc ≡ suc nx → ¬ Dividable n m
F<to¬D {n} {m} fc 1<n eq div = ⊥-elim ( nat-≡< (sym (proj2 ( Factor<-inject {n} {m} 1<n  fc (DtoF< div (<-trans a<sa 1<n) )))) 0<r  ) where
      0<r : 0 < Factor<.remain fc 
      0<r = subst ( λ k → 0 < k ) (sym eq) (s≤s z≤n)

--
-- we can use factor<  and check Factor.remain ≡ 0
--     Factor.remain ≡ 0   →   Dividable k m
--     ¬ Factor.remain ≡ 0 → ¬ Dividable k m
--
decD : {k m : ℕ} → k > 1 → Dec0 (Dividable k m )
decD {k} {m} k>1 = dec0 (factor< {k} {m} k>1) where
    dec0 : Factor< k m → Dec0 (Dividable k m)
    dec0 fc with Factor<.remain fc in eq1
    ... | zero = yes0 record { factor = Factor<.factor fc ; is-factor = trans (cong (λ j → Factor<.factor fc * k + j) (sym eq1))  (Factor<.is-factor fc)  }
    ... | suc t = no0 ( λ dv → F<to¬D fc k>1 eq1 dv )



