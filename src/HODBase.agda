{-# OPTIONS --cubical-compatible --safe #-}

open import Level
open import Ordinals
module HODBase {n : Level } (O : Ordinals {n} ) where

open import Data.Nat renaming ( zero to Zero ; suc to Suc ;  ℕ to Nat ; _⊔_ to _n⊔_ )
open import  Relation.Binary.PropositionalEquality hiding ( [_] )
open import Data.Nat.Properties
open import Data.Empty
open import Data.Unit
open import Relation.Nullary
open import Relation.Binary  hiding (_⇔_)
open import Relation.Binary.Core hiding (_⇔_)

open import logic
import OrdUtil
open import nat

open Ordinals.Ordinals  O
open Ordinals.IsOrdinals isOrdinal
-- open Ordinals.IsNext isNext
open OrdUtil O

-- Ordinal Definable Set

record OD : Set (suc n ) where
  field
    def : (x : Ordinal  ) → Set n

open OD

open _∧_
open _∨_
open Bool

record _==_  ( a b :  OD  ) : Set n where
  field
     eq→ : ∀ { x : Ordinal  } → def a x → def b x
     eq← : ∀ { x : Ordinal  } → def b x → def a x

==-refl :  {  x :  OD  } → x == x
==-refl  {x} = record { eq→ = λ x → x ; eq← = λ x → x }

open  _==_

==-trans : { x y z : OD } →  x == y →  y == z →  x ==  z
==-trans x=y y=z  = record { eq→ = λ {m} t → eq→ y=z (eq→ x=y t) ; eq← =  λ {m} t → eq← x=y (eq← y=z t) }

==-sym : { x y  : OD } →  x == y →  y == x
==-sym x=y = record { eq→ = λ {m} t → eq← x=y t ; eq← =  λ {m} t → eq→ x=y t }


⇔→== :  {  x y :  OD  } → ( {z : Ordinal } → (def x z ⇔  def y z)) → x == y
eq→ ( ⇔→==  {x} {y}  eq ) {z} m = proj1 eq m
eq← ( ⇔→==  {x} {y}  eq ) {z} m = proj2 eq m

--
--  OD is an equation on Ordinals, so it contains Ordinals. If these Ordinals have one-to-one
--  correspondence to the OD then the OD looks like a ZF Set.
--
--  If all ZF Set have supreme upper bound, the solutions of OD have to be bounded, i.e.
--  bbounded ODs are ZF Set. Unbounded ODs are classes.
--
--  In classical Set Theory, HOD is used, as a subset of OD,
--     HOD = { x | TC x ⊆ OD }
--  where TC x is a transitive clusure of x, i.e. Union of all elemnts of all subset of x.
--  This is not possible because we don't have V yet. So we assumes HODs are bounded OD.
--
--  We also assumes HODs are isomorphic to Ordinals, which is ususally proved by Goedel number tricks.
--  There two contraints on the HOD order, one is ∋, the other one is ⊂.
--  ODs have an ovbious maximum, but Ordinals are not, but HOD has no maximum because there is an aribtrary
--  bound on each HOD.
--
--  In classical Set Theory, sup is defined by Uion, since we are working on constructive logic,
--  we need explict assumption on sup for unrestricted Replacement.
--
--  ==→o≡ is necessary to prove axiom of extensionality.

-- Ordinals in OD , the maximum
Ords : OD
Ords = record { def = λ x → Lift n ⊤ }

record HOD : Set (suc n) where
  field
    od : OD
    odmax : Ordinal
    <odmax : {y : Ordinal} → def od y → y o< odmax

open HOD

record ODAxiom : Set (suc n) where
 field
  -- HOD is isomorphic to Ordinal (by means of Goedel number)
  & : HOD  → Ordinal
  * : Ordinal  → HOD
  c<→o<  :  {x y : HOD  }   → def (od y) ( & x ) → & x o< & y
  ⊆→o≤   :  {y z : HOD  }   → ({x : Ordinal} → def (od y) x → def (od z) x ) → & y o< osuc (& z)
  *iso   :  {x : HOD }      → od (* ( & x )) == od x
  &iso   :  {x : Ordinal }  → & ( * x ) ≡ x
  ==→o≡  :  {x y : HOD  }   → (od x == od y) → (& x) ≡ (& y)

==-Setoid : Setoid (suc n) n
==-Setoid = record { _≈_ = λ x y → od x == od y ; Carrier = HOD 
   ; isEquivalence = record { refl = ==-refl ; sym = ==-sym ; trans = ==-trans } }

-- use as open 
-- import Relation.Binary.Reasoning.Setoid as EqR
-- open EqR ==-Setoid




