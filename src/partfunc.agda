{-# OPTIONS --cubical-compatible --safe #-}
open import Level
open import Ordinals
open import logic
open import Relation.Nullary

open import Level
open import Ordinals
import HODBase
import OD
open import Relation.Nullary
module partfunc {n : Level } (O : Ordinals {n} ) (HODAxiom : HODBase.ODAxiom O)  (ho< : OD.ODAxiom-ho< O HODAxiom ) where

open import  Relation.Binary.PropositionalEquality hiding ( [_] )
open import Data.Empty

import OrdUtil

open Ordinals.Ordinals  O
open Ordinals.IsOrdinals isOrdinal
import ODUtil

open import logic
open import nat

open OrdUtil O
open ODUtil O HODAxiom  ho<

open _∧_
open _∨_
open Bool

open  HODBase._==_

open HODBase.ODAxiom HODAxiom  
open OD O HODAxiom

open HODBase.HOD


open import Relation.Nullary
open import Relation.Binary
open import Data.Empty
open import Relation.Binary
open import Relation.Binary.Core
open import  Relation.Binary.PropositionalEquality
open import Data.Nat renaming ( zero to Zero ; suc to Suc ;  ℕ to Nat ; _⊔_ to _n⊔_ )

open import Data.Empty 
open import Data.Unit using ( ⊤ ; tt )
open import Data.List hiding (filter ; find)
open import Data.Maybe  

open _∧_
open _∨_
open Bool

data Two : Set where
  i0 : Two
  i1 : Two

----
--
-- Partial Function without ZF
--

record PFunc {n m l : Level } (Dom : Set n) (Cod : Set m) : Set (suc  (n ⊔ m ⊔ l)) where
   field
      dom : Dom → Set l
      pmap : (x : Dom ) → dom x → Cod
      meq : {x : Dom } → { p q : dom x } → pmap x p ≡ pmap x q

----
--
-- PFunc (Lift n Nat) Cod is equivalent to List (Maybe Cod)
--

data Findp {n : Level} {Cod : Set n} : List (Maybe Cod) → (x : Nat) → Set (suc n) where
   v0 : {f : List (Maybe Cod)} → ( v : Cod ) → Findp ( just v  ∷ f ) Zero
   vn : {f : List (Maybe Cod)} {d : Maybe Cod} → {x : Nat} → Findp f x → Findp (d ∷ f) (Suc x) 

open PFunc

find : {n : Level} {Cod : Set n} → (f : List (Maybe Cod) ) → (x : Nat) → Findp f x → Cod
find (just v ∷ _) 0 (v0 v) = v
find (_ ∷ n) (Suc i) (vn p) = find n i p

findpeq : {n : Level} {Cod : Set n} → (f : List (Maybe Cod)) → {x : Nat} {p q : Findp f x } → find f x p ≡ find f x q
findpeq n {0} {v0 _} {v0 _} = refl
findpeq [] {Suc x} {()}
findpeq (just x₁ ∷ n) {Suc x} {vn p} {vn q} = findpeq n {x} {p} {q}
findpeq (nothing ∷ n) {Suc x} {vn p} {vn q} = findpeq n {x} {p} {q}

List→PFunc : {Cod : Set (suc n)} → List (Maybe Cod) → PFunc (Lift n Nat) Cod
List→PFunc fp = record { dom = λ x → Lift zero (Findp fp (lower x))
                       ; pmap = λ x y → find fp (lower x) (lower y)
                       ; meq = λ {x} {p} {q} →  findpeq fp {lower x} {lower p} {lower q}
                       }
----
--
-- to List (Maybe Two) is a Latice
--

_3⊆b_ : (f g : List (Maybe Two)) → Bool
[] 3⊆b [] = true
[] 3⊆b (nothing ∷ g) = [] 3⊆b g
[] 3⊆b (_ ∷ g) = true
(nothing ∷ f) 3⊆b [] = f 3⊆b []
(nothing ∷ f) 3⊆b (_ ∷ g)  = f 3⊆b g
(just i0 ∷ f) 3⊆b (just i0 ∷ g) = f 3⊆b g
(just i1 ∷ f) 3⊆b (just i1 ∷ g) = f 3⊆b g
_ 3⊆b _ = false 

_3⊆_ : (f g : List (Maybe Two)) → Set
f 3⊆ g  = (f 3⊆b g) ≡ true

_3∩_ : (f g : List (Maybe Two)) → List (Maybe Two)
[] 3∩ (nothing ∷ g) = nothing ∷ ([] 3∩ g)
[] 3∩ g  = []
(nothing ∷ f) 3∩ [] = nothing ∷ f 3∩ []
f 3∩ [] = []
(just i0 ∷ f) 3∩ (just i0 ∷ g) = just i0 ∷ (  f 3∩ g )
(just i1 ∷ f) 3∩ (just i1 ∷ g) = just i1 ∷ (  f 3∩ g )
(_ ∷ f) 3∩ (_ ∷ g)   = nothing  ∷ ( f 3∩ g )

3∩⊆f : { f g : List (Maybe Two) } → (f 3∩ g ) 3⊆ f
3∩⊆f {[]} {[]} = refl
3∩⊆f {[]} {just _ ∷ g} = refl
3∩⊆f {[]} {nothing ∷ g} = 3∩⊆f {[]} {g} 
3∩⊆f {just _ ∷ f} {[]} = refl
3∩⊆f {nothing ∷ f} {[]} = 3∩⊆f {f} {[]}
3∩⊆f {just i0 ∷ f} {just i0 ∷ g} = 3∩⊆f {f} {g}
3∩⊆f {just i1 ∷ f} {just i1 ∷ g} =  3∩⊆f {f} {g}
3∩⊆f {just i0 ∷ f} {just i1 ∷ g} =   3∩⊆f {f} {g}
3∩⊆f {just i1 ∷ f} {just i0 ∷ g} =    3∩⊆f {f} {g}
3∩⊆f {nothing ∷ f} {just _ ∷ g} = 3∩⊆f {f} {g}
3∩⊆f {just i0  ∷ f} {nothing ∷ g} = 3∩⊆f {f} {g} 
3∩⊆f {just i1 ∷ f} {nothing ∷ g} =  3∩⊆f {f} {g} 
3∩⊆f {nothing ∷ f} {nothing ∷ g} = 3∩⊆f {f} {g}

3∩sym : { f g : List (Maybe Two) } → (f 3∩ g ) ≡ (g 3∩ f )
3∩sym {[]} {[]} = refl
3∩sym {[]} {just _ ∷ g} = refl
3∩sym {[]} {nothing ∷ g} = cong (λ k → nothing ∷ k) (3∩sym {[]} {g})
3∩sym {just _ ∷ f} {[]} = refl
3∩sym {nothing ∷ f} {[]} = cong (λ k → nothing ∷ k) (3∩sym {f} {[]})
3∩sym {just i0 ∷ f} {just i0 ∷ g} = cong (λ k → just i0 ∷ k) (3∩sym {f} {g})
3∩sym {just i0 ∷ f} {just i1 ∷ g} =  cong (λ k → nothing ∷ k) (3∩sym {f} {g})
3∩sym {just i1 ∷ f} {just i0 ∷ g} =  cong (λ k → nothing ∷ k) (3∩sym {f} {g})
3∩sym {just i1 ∷ f} {just i1 ∷ g} =  cong (λ k → just i1 ∷ k) (3∩sym {f} {g})
3∩sym {just i0 ∷ f} {nothing ∷ g} =  cong (λ k → nothing ∷ k) (3∩sym {f} {g})
3∩sym {just i1 ∷ f} {nothing ∷ g} =  cong (λ k → nothing ∷ k) (3∩sym {f} {g})
3∩sym {nothing ∷ f} {just i0 ∷ g} = cong (λ k → nothing ∷ k) (3∩sym {f} {g})
3∩sym {nothing ∷ f} {just i1 ∷ g} =  cong (λ k → nothing ∷ k) (3∩sym {f} {g})
3∩sym {nothing ∷ f} {nothing ∷ g} = cong (λ k → nothing ∷ k) (3∩sym {f} {g})

3⊆-[] : { h : List (Maybe Two) } → [] 3⊆ h
3⊆-[] {[]} = refl
3⊆-[] {just _ ∷ h} = refl
3⊆-[] {nothing ∷ h} = 3⊆-[] {h}

3⊆trans : { f g h : List (Maybe Two) } → f 3⊆ g → g 3⊆ h → f 3⊆ h
3⊆trans {[]} {[]} {[]} f<g g<h = refl
3⊆trans {[]} {[]} {just _ ∷ h} f<g g<h = refl
3⊆trans {[]} {[]} {nothing ∷ h} f<g g<h = 3⊆trans {[]} {[]} {h} refl g<h
3⊆trans {[]} {nothing ∷ g} {[]} f<g g<h = refl
3⊆trans {[]} {just _ ∷ g} {just _ ∷ h} f<g g<h = refl
3⊆trans {[]} {nothing ∷ g} {just _ ∷ h} f<g g<h = refl
3⊆trans {[]} {nothing ∷ g} {nothing ∷ h} f<g g<h = 3⊆trans {[]} {g} {h} f<g g<h 
3⊆trans {nothing ∷ f} {[]} {[]} f<g g<h = f<g
3⊆trans {nothing ∷ f} {[]} {just _ ∷ h} f<g g<h = 3⊆trans {f} {[]} {h} f<g (3⊆-[] {h})
3⊆trans {nothing ∷ f} {[]} {nothing ∷ h} f<g g<h = 3⊆trans {f} {[]} {h} f<g g<h 
3⊆trans {nothing ∷ f} {nothing ∷ g} {[]} f<g g<h = 3⊆trans {f} {g} {[]} f<g g<h 
3⊆trans {nothing ∷ f} {nothing ∷ g} {just _ ∷ h} f<g g<h =  3⊆trans {f} {g} {h} f<g g<h 
3⊆trans {nothing ∷ f} {nothing ∷ g} {nothing ∷ h} f<g g<h =  3⊆trans {f} {g} {h} f<g g<h 
3⊆trans {[]} {just i0 ∷ g} {[]} f<g ()
3⊆trans {[]} {just i1 ∷ g} {[]} f<g ()
3⊆trans {[]} {just x ∷ g} {nothing ∷ h} f<g g<h = 3⊆-[] {h}
3⊆trans {just i0 ∷ f} {[]} {h} () g<h
3⊆trans {just i1 ∷ f} {[]} {h} () g<h
3⊆trans {just x ∷ f} {just i0 ∷ g} {[]} f<g ()
3⊆trans {just x ∷ f} {just i1 ∷ g} {[]} f<g ()
3⊆trans {just i0 ∷ f} {just i0 ∷ g} {just i0 ∷ h} f<g g<h = 3⊆trans {f} {g} {h} f<g g<h
3⊆trans {just i1 ∷ f} {just i1 ∷ g} {just i1 ∷ h} f<g g<h = 3⊆trans {f} {g} {h} f<g g<h
3⊆trans {just x ∷ f} {just i0 ∷ g} {nothing ∷ h} f<g ()
3⊆trans {just x ∷ f} {just i1 ∷ g} {nothing ∷ h} f<g ()
3⊆trans {just i0 ∷ f} {nothing ∷ g} {_} () g<h
3⊆trans {just i1 ∷ f} {nothing ∷ g} {_} () g<h
3⊆trans {nothing ∷ f} {just i0 ∷ g} {[]} f<g ()
3⊆trans {nothing ∷ f} {just i1 ∷ g} {[]} f<g ()
3⊆trans {nothing ∷ f} {just i0 ∷ g} {just i0 ∷ h} f<g g<h =  3⊆trans {f} {g} {h} f<g g<h
3⊆trans {nothing ∷ f} {just i1 ∷ g} {just i1 ∷ h} f<g g<h =  3⊆trans {f} {g} {h} f<g g<h
3⊆trans {nothing ∷ f} {just i0 ∷ g} {nothing ∷ h} f<g ()
3⊆trans {nothing ∷ f} {just i1 ∷ g} {nothing ∷ h} f<g ()

3⊆∩f : { f g h : List (Maybe Two) }  → f 3⊆ g → f 3⊆ h → f 3⊆  (g 3∩ h ) 
3⊆∩f {[]} {[]} {[]} f<g f<h = refl
3⊆∩f {[]} {[]} {x ∷ h} f<g f<h = 3⊆-[] {[] 3∩ (x ∷ h)}
3⊆∩f {[]} {x ∷ g} {h} f<g f<h = 3⊆-[] {(x ∷ g) 3∩ h}
3⊆∩f {nothing ∷ f} {[]} {[]} f<g f<h = 3⊆∩f {f} {[]} {[]} f<g f<h 
3⊆∩f {nothing ∷ f} {[]} {just _ ∷ h} f<g f<h = f<g
3⊆∩f {nothing ∷ f} {[]} {nothing ∷ h} f<g f<h = 3⊆∩f {f} {[]} {h} f<g f<h 
3⊆∩f {just i0 ∷ f} {just i0 ∷ g} {just i0 ∷ h} f<g f<h =  3⊆∩f {f} {g} {h} f<g f<h 
3⊆∩f {just i1 ∷ f} {just i1 ∷ g} {just i1 ∷ h} f<g f<h =  3⊆∩f {f} {g} {h} f<g f<h 
3⊆∩f {nothing ∷ f} {just _ ∷ g} {[]} f<g f<h = f<h
3⊆∩f {nothing ∷ f} {just i0 ∷ g} {just i0 ∷ h} f<g f<h =  3⊆∩f {f} {g} {h} f<g f<h 
3⊆∩f {nothing ∷ f} {just i0 ∷ g} {just i1 ∷ h} f<g f<h =  3⊆∩f {f} {g} {h} f<g f<h 
3⊆∩f {nothing ∷ f} {just i1 ∷ g} {just i0 ∷ h} f<g f<h =  3⊆∩f {f} {g} {h} f<g f<h 
3⊆∩f {nothing ∷ f} {just i1 ∷ g} {just i1 ∷ h} f<g f<h =  3⊆∩f {f} {g} {h} f<g f<h 
3⊆∩f {nothing ∷ f} {just i0 ∷ g} {nothing ∷ h} f<g f<h =   3⊆∩f {f} {g} {h} f<g f<h 
3⊆∩f {nothing ∷ f} {just i1 ∷ g} {nothing ∷ h} f<g f<h =   3⊆∩f {f} {g} {h} f<g f<h 
3⊆∩f {nothing ∷ f} {nothing ∷ g} {[]} f<g f<h = 3⊆∩f {f} {g} {[]} f<g f<h  
3⊆∩f {nothing ∷ f} {nothing ∷ g} {just _ ∷ h} f<g f<h =  3⊆∩f {f} {g} {h} f<g f<h 
3⊆∩f {nothing ∷ f} {nothing ∷ g} {nothing ∷ h} f<g f<h =  3⊆∩f {f} {g} {h} f<g f<h 

3↑22 : (f : Nat → Two) (i j : Nat) → List (Maybe Two)
3↑22 f Zero j = []
3↑22 f (Suc i) j = just (f j) ∷ 3↑22 f i (Suc j)

_3↑_ : (Nat → Two) → Nat → List (Maybe Two)
_3↑_ f i = 3↑22 f i 0 

3↑< : {f : Nat → Two} → { x y : Nat } → x ≤ y → (_3↑_ f x)  3⊆ (_3↑_ f y)
3↑< {f} {x} {y} x<y = lemma x y 0 x<y where
     lemma : (x y i : Nat) → x ≤ y → (3↑22 f x i ) 3⊆ (3↑22 f y i )
     lemma 0 y i z≤n with f i
     lemma Zero Zero i z≤n | i0 = refl
     lemma Zero (Suc y) i z≤n | i0 = 3⊆-[]  {3↑22 f (Suc y) i}
     lemma Zero Zero i z≤n | i1 = refl
     lemma Zero (Suc y) i z≤n | i1 = 3⊆-[]  {3↑22 f (Suc y) i}
     lemma (Suc x) (Suc y) i (s≤s x<y) with f i  
     lemma (Suc x) (Suc y) i (s≤s x<y) | i0 = lemma x y (Suc i) x<y 
     lemma (Suc x) (Suc y) i (s≤s x<y) | i1 = lemma x y (Suc i) x<y 

Finite3b : (p : List (Maybe Two) ) → Bool 
Finite3b [] = true
Finite3b (just _ ∷ f) = Finite3b f
Finite3b (nothing ∷ f) = false

finite3cov : (p : List (Maybe Two) ) → List (Maybe Two)
finite3cov [] = []
finite3cov (just y ∷ x) = just y ∷ finite3cov x
finite3cov (nothing ∷ x) = just i0 ∷ finite3cov x

record F-Filter {n : Level} (L : Set n) (PL : (L → Set n) → Set n) ( _⊆_ : L  → L → Set n)  (_∩_ : L → L → L ) : Set (suc n) where
   field
       filter : L → Set n
       f⊆P :  PL filter 
       filter1 : { p q : L } → PL (λ x → q ⊆ x )  → filter p →  p ⊆ q  → filter q
       filter2 : { p q : L } → filter p →  filter q  → filter (p ∩ q)

record F-Dense {n : Level} (L : Set n) (PL : (L → Set n) → Set n) ( _⊆_ : L  → L → Set n)  (_∩_ : L → L → L ) : Set (suc n) where
   field
       dense : L → Set n
       d⊆P :  PL dense 
       dense-f : L → L 
       dense-d :  { p : L} → PL (λ x → p ⊆ x ) → dense ( dense-f p  )
       dense-p :  { p : L} → PL (λ x → p ⊆ x ) → p ⊆ (dense-f p) 


Dense-3 : F-Dense (List (Maybe Two) ) (λ x → ⊤ ) _3⊆_ _3∩_
Dense-3 = record {
       dense =  λ x → Finite3b x ≡ true
    ;  d⊆P = tt
    ;  dense-f = λ x → finite3cov x
    ;  dense-d = λ {p} d → lemma1 p
    ;  dense-p = λ {p} d → lemma2 p
  } where
      lemma1 : (p : List (Maybe Two) ) → Finite3b (finite3cov p) ≡ true
      lemma1 [] = refl
      lemma1 (just i0 ∷ p) = lemma1 p
      lemma1 (just i1 ∷ p) = lemma1 p
      lemma1 (nothing ∷ p) = lemma1 p
      lemma2 : (p : List (Maybe Two)) → p 3⊆ finite3cov p
      lemma2 [] = refl
      lemma2 (just i0 ∷ p) = lemma2 p
      lemma2 (just i1 ∷ p) = lemma2 p
      lemma2 (nothing ∷ p) = lemma2 p

-- min  = Data.Nat._⊓_
-- m≤m⊔n  = Data.Nat._⊔_
-- open import Data.Nat.Properties

