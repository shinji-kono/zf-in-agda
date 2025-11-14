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
module ZEquiv {n : Level } (O : Ordinals {n} ) (HODAxiom : HODBase.ODAxiom O)  (ho< : OD.ODAxiom-ho< O HODAxiom ) where

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

record HODElement (A : HOD) : Set n where
   field
      elt : Ordinal
      A∋elt : odef A elt

module  EqHOD ( A : HOD) (_≐_ : Rel (HODElement A) n)    where

    record HODEquivalent (x : Ordinal) : Set n where
       field
          repl : HODElement A
          A∋x : odef A x
          x=repl : record { elt = x ; A∋elt = A∋x } ≐ repl

    record HODEquivalent1 (x : Ordinal) {y : Ordinal} (A∋y : odef A y) : Set n where
       field
          A∋x : odef A x
          x=repl : record { elt = x ; A∋elt = A∋x } ≐ record { elt = y ; A∋elt = A∋y }

    HODEquivalentSet :  HOD
    HODEquivalentSet  = record { od = record { def = λ x → HODEquivalent  x } ; odmax = & A ; <odmax = λ lt → odef< (HODEquivalent.A∋x lt) }

    HODQuotient : HOD
    HODQuotient  = record { od = record { def = λ x → x ≡ & HODEquivalentSet  } ; odmax = osuc (& A) ; <odmax = lem } where
        lem : {y : Ordinal} → y ≡ & HODEquivalentSet → y o< osuc (& A)
        lem {y} eq = subst (λ k → k o< _ ) &iso  ( ⊆→o≤ lem00 ) where
           lem00 :  {x : Ordinal} → HODBase.OD.def (od (* y)) x → HODBase.OD.def (od A) x
           lem00 {x} lt with eq→ *iso (subst (λ k → odef k x ) (cong (*) eq) lt)
           ... | record { repl = repl ; A∋x = A∋x ; x=repl = x=repl } = A∋x

    create : {x : Ordinal} → odef A x → HOD
    create {x} ax = record { od = record { def = λ y → HODEquivalent1 y ax } ; odmax = & A ; <odmax = λ lt → odef< (HODEquivalent1.A∋x lt ) }


-- end





