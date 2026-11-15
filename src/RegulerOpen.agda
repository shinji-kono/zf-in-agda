{-# OPTIONS --cubical-compatible --safe #-}
open import Level renaming ( suc to Suc ; zero to Zero ; _⊔_ to _n⊔_ )
open import Ordinals
open import logic
open import Relation.Nullary

--
-- 選択公理と数学　田中尚夫 203 page
--
--
--

import HODBase
import OD
open import Relation.Nullary
module RegulerOpen where

open import  Relation.Binary.PropositionalEquality hiding ( [_] )
open import Relation.Binary.Definitions -- hiding ( _⇔_ )
open import Data.Empty
import OrdUtil
import ODUtil
open import logic
open import nat

open import Ordinals
import filter

open import Relation.Nullary
-- open import Relation.Binary hiding ( _⇔_ )
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Data.Nat renaming ( _<_  to _n<_  ; _+_ to _n+_ ; _≤_ to _n≤_ )
open import Data.Nat.Properties
open import BoolAlgebra

import Relation.Binary.Reasoning.Setoid as EqHOD

module MBO {n : Level } (O : Ordinals {n} ) (HODAxiom : HODBase.ODAxiom O)  (ho< : OD.ODAxiom-ho< O HODAxiom )
           (AC : OD.AxiomOfChoice O HODAxiom ) where

    open Ordinals.Ordinals  O
    open Ordinals.IsOrdinals isOrdinal
    open HODBase.ODAxiom HODAxiom
    open OD O HODAxiom
    open import ODC O HODAxiom AC as ODC

    open AxiomOfChoice AC
    open OrdUtil O
    open ODUtil O HODAxiom  ho<
    open HODBase.HOD
    open _∧_
    open _∨_
    open Bool
    open  HODBase._==_
    open import ZProduct O HODAxiom ho<
    open import filter O HODAxiom ho< AC

    open import bijection hiding ( b1 )

    -- open HODBooleanAlgebra

    -- LDec : (L : HOD) (P : HOD) → P ⊆ L → (x : HOD) → Dec0 (x ∈ P)
    -- LDec L P _ x = ∋-p P x

    -- open import Data.Nat
    open import ZEquiv O HODAxiom ho<

    open HODElement
    import BAlgebra

    open Bijection
    -- B1 contains all Ordinals
    --
    --

    open import Relation.Binary hiding ( _⇔_ )
    open import Topology O HODAxiom ho< AC

    record OrderedHOD (P : HOD) : Set (Level.suc n) where
      field
         _p<_ : (x y : HODElement P) → Set n
         _=p=_ : (x y : HODElement P) → Set n
         PO : IsStrictPartialOrder {n} {n} _=p=_  _p<_
         p=resp : {x y w z : HODElement P } → elt x ≡ elt w → elt y ≡  elt z → x =p= y  → w =p= z
         p<-resp : {x y w z : HODElement P } → x =p= w → y =p= z → x p< y  → w p< z
      _p≤_ : (x y : HODElement P) → Set n
      x p≤ y = ( x =p= y ) ∨  ( x p< y )
      p-refl : {p : HODElement P} → p =p= p
      p-refl = IsEquivalence.refl (IsStrictPartialOrder.isEquivalence PO)
      p-refl1 : {p p' : HODElement P} → elt p ≡ elt p' → p =p= p'
      p-refl1 {p} refl = p=resp refl refl (p-refl {p})
      p-trans : {x y z : HODElement P} → x =p= y → y =p= z → x =p= z
      p-trans eq eq' = IsEquivalence.trans (IsStrictPartialOrder.isEquivalence PO) eq eq'
      p-sym : {x y : HODElement P} → x =p= y → y =p= x
      p-sym eq = IsEquivalence.sym (IsStrictPartialOrder.isEquivalence PO) eq
      p≤-resp : {x y w z : HODElement P } → x =p= w → y =p= z → x p≤ y  → w p≤ z
      p≤-resp {x} {y} {_} {_} x=w y=z (case1 eq) = case1 ( p=resp refl refl (p-trans (p-sym x=w) (p-trans eq y=z) ) )
      p≤-resp {x} {y} {_} {_} x=w y=z (case2 lt) = case2 ( p<-resp x=w y=z lt )
      p-sep : {x y : HODElement P} → (¬ (x p< y)) ∨ (¬ (y p< x) )
      p-sep {x} {y} with  p∨¬p (x p< y)
      ... | case2 lt = case1 lt
      ... | case1 x<y with  p∨¬p (y p< x)
      ... | case2 lt = case2 lt
      ... | case1 y<x = ⊥-elim ( IsStrictPartialOrder.asym PO x<y y<x )
      open IsStrictPartialOrder PO
      open import Data.Product
      p<-trans : {x y z : HODElement P} → x p< y → y p< z → x p< z
      p<-trans lt1 lt2 = IsStrictPartialOrder.trans PO lt1 lt2
      p≤-trans :  {x y z : HODElement P} → x p≤ y → y p≤ z → x p≤ z
      p≤-trans {x} {y} {z} (case1 eq) (case1 eq') = case1 (p-trans eq eq')
      p≤-trans {x} {y} {z} (case1 eq) (case2 lt) = case2 ( proj₂ <-resp-≈ (p-sym eq) lt )
      p≤-trans {x} {y} {z} (case2 lt) (case1 eq) = case2 ( proj₁ <-resp-≈ eq lt )
      p≤-trans {x} {y} {z} (case2 lt1) (case2 lt2) = case2 ( p<-trans lt1 lt2 )
      p≤> : {x y : HODElement P} → x p≤ y → ¬ (y p< x) 
      p≤> {x} {y} (case1 eq) = λ y<x → ⊥-elim ( IsStrictPartialOrder.irrefl PO (p-sym eq) y<x )
      p≤> {x} {y} (case2 le) = λ y<x → ⊥-elim ( IsStrictPartialOrder.asym PO le y<x )


    open import PFOD O HODAxiom  ho< AC

    --  u ⊆ P , ∀ x ∈ u → y ∈ P → y ≤ x → y ∈ u
    record OpenP (P : HOD) (OP : OrderedHOD P) (u : Ordinal) : Set n where
      field
         u⊆P : (* u) ⊆ P
         is-open : (x y : Ordinal) → (ux : odef (* u) x) → (py : odef P y )
            →  OrderedHOD._p≤_ OP record { elt = y ; A∋elt  = py } record { elt = x ; A∋elt = u⊆P ux }  → odef (* u) y

    OpenPHOD :  (P : HOD) (OP : OrderedHOD P) → HOD
    OpenPHOD P OP = record { od = record { def = λ u → OpenP P OP u } ; odmax = osuc (& P)
       ; <odmax = λ {u} lt → subst (  λ k → k o< _ ) &iso  (⊆→o≤  (OpenP.u⊆P lt) )  }

    record DownP (P : HOD) (OP : OrderedHOD P) (u : HODElement P) (x : Ordinal) : Set n where
      field
         px  : odef P x
         is-below :  OrderedHOD._p≤_ OP record { elt = x ; A∋elt  = px } u

    -- set of all elements below u in P
    downHOD : (P : HOD) (OP : OrderedHOD P) (u : HODElement P) → HOD
    downHOD P OP u = record { od = record { def = λ x → DownP P OP u x } ; odmax = & P
       ; <odmax = λ {u} lt → odef< (DownP.px lt)  }

    -- is open
    downHOD∈OS : (P : HOD) (OP : OrderedHOD P) (u : HODElement P) → OpenP P OP (& (downHOD P OP u))
    downHOD∈OS  P OP u = record { u⊆P = λ {x} px → DownP.px (eq→ *iso px) ; is-open = λ x y px py le → eq← *iso
       (lem00 _ _ le (eq→ *iso px) ) } where
       open OrderedHOD OP
       open IsStrictPartialOrder PO
       lem00 : (ex ey : HODElement P) → ey p≤ ex → DownP P OP u (elt ex)  → DownP P OP u (elt ey)
       lem00 ex ey y≤x dux = record { px = A∋elt ey ; is-below =  p≤-trans  y≤x (p≤-resp (p-refl1 refl) p-refl (DownP.is-below dux)) }

    record ROH-lem00 (P : HOD) (OP : OrderedHOD P) (u : HODElement (Power P)) (ou : OpenP P OP (elt u)) : Set n where
      field
         p : HODElement P
         dp⊆u : downHOD P OP p ⊆ (* (elt u))
         -- this means if u is open, it conains ∀ x p< ∃ p → x ∈ u
      open OrderedHOD OP
      open IsStrictPartialOrder PO
      p⊆u : {y : HODElement P } → y p≤ p → odef (* (elt p)) (elt y) → odef (* (elt u)) (elt y)
      p⊆u {y} y≤p py = dp⊆u (record { px = A∋elt y ; is-below = y≤p } )

    -- downHOD are open base
    --
    down-lem00 : (P : HOD) (OP : OrderedHOD P) (u : HODElement (Power P)) (ou : OpenP P OP (elt u))
        → {x : Ordinal} → (ux : odef (* (elt u)) x)
        → ROH-lem00 P OP u ou
    down-lem00 P OP u (ou @ record { u⊆P = u⊆P ; is-open = is-open }) {x} ux = lem00 where
       open OrderedHOD OP
       open IsStrictPartialOrder PO
       lem02 : HODElement P
       lem02 = record { elt = x ; A∋elt = A∋elt u _ ux }
       lem01 : {z : Ordinal} → odef (downHOD P OP lem02) z → odef (* (elt u)) z
       lem01 {z} d2 = OpenP.is-open ou _ _ ux (DownP.px d2) lem05  where
          lem05 : record { elt = z ; A∋elt = DownP.px d2 } p≤ record { elt = x ; A∋elt = u⊆P ux }
          lem05 = p≤-resp p-refl (p-refl1 refl) ( DownP.is-below d2 )
       lem00 : ROH-lem00 P OP u ou
       lem00 = record { p = lem02  ; dp⊆u = lem01 }

    down-lem02 : (P : HOD) (OP : OrderedHOD P) (u : HODElement (Power P)) (ou : OpenP P OP (elt u))
        → {x : Ordinal} → (ux : odef (* (elt u)) x)
        → odef ( downHOD P OP (ROH-lem00.p (down-lem00 P OP u ou ux  ) )  ) x
    down-lem02 P OP u ou {x} ux  = lem00 where
       open OrderedHOD OP
       open IsStrictPartialOrder PO
       lem01 :  odef P x
       lem01 = A∋elt u _ ux
       lem00 :  odef ( downHOD P OP (ROH-lem00.p (down-lem00 P OP u ou ux  ) )  ) x
       lem00 = record { px = lem01 ; is-below = case1 p-refl }

    record ROH-lem03 (P : HOD) (OP : OrderedHOD P) (u : HODElement (Power P)) (ou : OpenP P OP (elt u)) (y : Ordinal) : Set n where
      field
         x : Ordinal
         ux : odef (* (elt u)) x
         up : y ≡ (& ( downHOD P OP (ROH-lem00.p (down-lem00 P OP u ou {x} ux  ) ) ))
      y⊆P : (* y) ⊆  P
      y⊆P {z} lt = DownP.px ( eq→ (ord→== (trans &iso up) ) lt )
      y<P : y o< osuc (& P)
      y<P = subst (λ k → k o< _) &iso (⊆→o≤ y⊆P )

    ROH-lem05 : (P : HOD) (OP : OrderedHOD P) (u : HODElement (Power P)) (ou : OpenP P OP (elt u)) → HOD
    ROH-lem05 P OP u ou = record { od = record { def = λ x → ROH-lem03 P OP u ou x } ; odmax = osuc (& P) ; <odmax = λ {u} lt →  ROH-lem03.y<P lt }

    down-lem01 : (P : HOD) (OP : OrderedHOD P) (u : HODElement (Power P)) (ou : OpenP P OP (elt u))
        →  Union (ROH-lem05 P OP u ou)  =h= (* ( elt u)  )
    down-lem01 P OP u ou =  record { eq→ = λ {y} lt → lem05 lt ; eq← = λ {y} lt → lem06 lt } where
       open OrderedHOD OP
       lem05 : {y : Ordinal} → Own (ROH-lem05 P OP u ou ) y → odef (* (elt u)) y
       lem05 {y} record { owner = owner ; ao = ao ; ox = ox } = ROH-lem00.dp⊆u lem08 lem11  where
            lem09 : ROH-lem03 P OP u ou owner
            lem09 = ao
            lem07 : owner  ≡ & (downHOD P OP ( ROH-lem00.p (down-lem00 P OP u ou {ROH-lem03.x ao} (ROH-lem03.ux ao) ) ))
            lem07 = ROH-lem03.up ao
            lem08 : ROH-lem00 P OP u ou
            lem08 = down-lem00 P OP u ou {ROH-lem03.x ao} (ROH-lem03.ux ao)
            lem11 : odef (downHOD P OP (ROH-lem00.p (down-lem00 P OP u ou {ROH-lem03.x ao} (ROH-lem03.ux ao)  ) )) y
            lem11 = eq→ *iso ( eq→ (o≡→== (ROH-lem03.up ao) ) ox )
       lem06 : {y : Ordinal} → odef (* (elt u)) y → Own (ROH-lem05 P OP u ou) y
       lem06 {y} uy = record { owner = _ ; ao = record { x = _ ; ux = uy ; up = refl }  ; ox = eq← *iso record { px = A∋elt u _ uy ; is-below = case1 p-refl } }

    TOPP : (P : HOD) → OrderedHOD P → Topology P
    TOPP P OP = record { OS = OpenPHOD P OP  ;
         OS⊆PL = λ {y} op z px  → OpenP.u⊆P op px
       ; o∩ = λ {p} {q} op oq → record { u⊆P = λ {x} pqx → OpenP.u⊆P op (eq← *iso (proj1 (eq→ *iso pqx) ))
          ; is-open = λ x y ux py lt → eq←  *iso ⟪
               eq→ *iso (OpenP.is-open op _ _ (eq← *iso (proj1 (eq→  *iso ux))) py lt )
             , eq→ *iso (OpenP.is-open oq _ _ (eq← *iso (proj2 (eq→  *iso ux))) py
                  (OrderedHOD.p≤-resp OP (OrderedHOD.p-refl OP) (OrderedHOD.p-refl1 OP refl ) lt ) ) ⟫  }
       ; o∪  = lem00
       ; OS∋od∅ = subst ( λ k → OpenP P OP k) (trans Union-0 (sym ord-od∅ ) ) (lem00 {od∅} (λ lt → ⊥-elim (¬x<0  lt) ) ) } where
          lem00 : {U : HOD} → U ⊆ OpenPHOD P OP → OpenPHOD P OP ∋ Union U
          lem00 {U} u⊆op = record { u⊆P = λ {x} ux → OpenP.u⊆P ( u⊆op (Own.ao (eq→ *iso ux))) (Own.ox (eq→ *iso ux))
            ; is-open = λ x y ux py lt → eq← *iso record { owner = Own.owner (eq→ *iso ux) ; ao = Own.ao  (eq→ *iso ux)
              ; ox = OpenP.is-open (u⊆op (Own.ao (eq→ *iso ux))) _ _ (Own.ox (eq→ *iso ux)) py lt }   }

    record UpP (P : HOD) (OP : OrderedHOD P) (u : HODElement P) (x : Ordinal) : Set n where
      field
         px  : odef P x
         is-above :  OrderedHOD._p<_ OP u record { elt = x ; A∋elt  = px }

    -- set of an elements above u in P
    upHOD : (P : HOD) (OP : OrderedHOD P) (u : HODElement P) → HOD
    upHOD P OP u = record { od = record { def = λ x → UpP P OP u x } ; odmax = & P
       ; <odmax = λ {u} lt → odef< (UpP.px lt)  }
    -- is close
    upHOD∈CS : (P : HOD) (OP : OrderedHOD P) (u : HODElement P) → odef (Topology.CS (TOPP P OP)) (& (upHOD P OP u))
    upHOD∈CS P OP u = ⟪ (λ lt → UpP.px (eq→ *iso lt)) , record { u⊆P = λ lt → proj1 (eq→ *iso lt)  ; is-open = lem01 } ⟫ where
       open OrderedHOD OP
       open IsStrictPartialOrder PO
       lem01 : (x y : Ordinal) (ux : odef (* (& (P ＼ * (& (upHOD P OP u))))) x)
        (py : odef P y) → record { elt = y ; A∋elt = py } p≤ record { elt = x ; A∋elt = proj1 (eq→ *iso ux) } → odef (* (& (P ＼ * (& (upHOD P OP u))))) y
       lem01 x y ux py y≤x = eq← *iso ⟪ py , (λ lt → lem02 (eq→ *iso lt)) ⟫ where
          lem03 : odef (upHOD P OP u) x → ⊥
          lem03 record { px = px ; is-above = u<x } = proj2 (eq→ *iso ux) (eq← *iso record { px = px ; is-above = u<x } )
          lem04 : odef P x
          lem04 = proj1 (eq→ *iso ux)
          lem02 : odef (upHOD P OP u) y → ⊥
          lem02 record { px = py2 ; is-above = u<y } = proj2 (eq→ *iso ux) (eq← *iso record { px = lem04 ; is-above = lem05 y≤x } ) where
              lem05 : record { elt = y ; A∋elt = py } p≤ record { elt = x ; A∋elt = proj1 (eq→ *iso ux) } → u p< record { elt = x ; A∋elt = lem04 }
              lem05 (case1 eq) = p<-resp p-refl (p=resp refl refl eq) u<y
              lem05 (case2 lt) = p<-trans u<y (p<-resp (p-refl1 refl) (p-refl1 refl) lt )

    record  CSCond  (L : HOD) (OL : OrderedHOD L) (x : Ordinal )  : Set n where
        open Topology
        open OrderedHOD OL
        field
          lx : odef L x
          p :  HODElement L
          nle :  ¬ ( record { elt = x ; A∋elt = lx }  p≤ p )

    csHOD : (L : HOD) (OL : OrderedHOD L) → HOD
    csHOD L OL = record { od = record { def = λ x → CSCond L OL x } ; odmax = & L ; <odmax = λ {u} lt → odef< (CSCond.lx lt) }

    csc-lem00 : (L : HOD) (OL : OrderedHOD L)  → odef (Topology.CS (TOPP L OL)) (& (csHOD L OL ))
    csc-lem00 L OL = ⟪ (λ lt → CSCond.lx ( eq→ *iso lt) ) , record { u⊆P = λ lt → proj1 (eq→ *iso lt) ; is-open = lem02 }  ⟫ where
       open OrderedHOD OL
       open IsStrictPartialOrder PO
       lem02 : (x y : Ordinal) (ux : odef (* (& (L ＼ * (& (csHOD L OL))))) x) (py : odef L y)
           → record { elt = y ; A∋elt = py } p≤ record { elt = x ; A∋elt = proj1 (eq→ *iso ux) } → odef (* (& (L ＼ * (& (csHOD L OL))))) y
       lem02 x y ux py y≤x = eq← *iso ⟪ py , ( λ lt → lem03 (eq→ *iso lt) ) ⟫ where
          lem04 : odef (csHOD L OL) x → ⊥
          lem04 lt = proj2 ( eq→ *iso ux ) (eq← *iso lt)
          lem03 : odef (csHOD L OL) y → ⊥
          lem03 record { lx = ly ; p = p ; nle = nle } = lem04 record { lx = proj1 (eq→ *iso ux)  ; p = p
             ; nle = λ le → nle (p≤-trans ( p≤-resp (p-refl1 refl) (p-refl1 refl) y≤x) le) }

    record Separate (P : HOD) (TP : Topology P) (p q : Ordinal ) : Set n where
      field
         sep : Ordinal
         os  : odef (Topology.OS TP) sep
         sp  : ( odef (* sep) p ∧ ( ¬ (odef (* sep) q)) )  ∨ ( odef (* sep) q ∧ ( ¬ (odef (* sep) p)) )

    T0-Separate : (P : HOD) → Topology P → {p q : HODElement P} → Set n
    T0-Separate P TP {p} {q}  = (p≠q : ¬ (elt p ≡ elt q)) → Separate P TP (elt p) (elt q)

    TOPP-Separate : (L : HOD) → (OL : OrderedHOD L) → {p q : HODElement L}
       → (p≠q : ¬ ( OrderedHOD._=p=_ OL p q)) → Separate L (TOPP L OL) (elt p) (elt q)
    TOPP-Separate L OL {p} {q} ne = lem30 p-sep  where
       open Topology
       open OrderedHOD OL
       lem26 : (¬ (p p< q)) ∨ (¬ (q p< p) )
       lem26 = p-sep
       lem30 : (¬ (p p< q)) ∨ (¬ (q p< p) ) → Separate L (TOPP L OL) (elt p) (elt q)
       lem30 (case1 np<q ) = record { sep =  & ( downHOD L OL q) ; os =  downHOD∈OS L OL q ; sp = case2 ( ⟪ eq← *iso lem31 , lem32 ⟫ )  } where
           lem31 : DownP L OL q (elt q)
           lem31 = record { px = A∋elt q ;  is-below = case1 p-refl  }
           lem32 : odef (* (& (downHOD L OL q))) (elt p) → ⊥
           lem32 lt = ⊥-elim ( np<q lem33 ) where
              lem33 : p p< q
              lem33 with DownP.is-below (eq→ *iso lt)
              ... | case1 eq = ⊥-elim ( ne (p=resp refl refl eq ))
              ... | case2 lt = p<-resp (p-refl1 refl) p-refl lt
       lem30 (case2 nq<p ) = record { sep =  & ( downHOD L OL p) ; os =  downHOD∈OS L OL p ; sp =  case1 ( ⟪ eq← *iso lem31 , lem32 ⟫ ) } where
           lem31 : DownP L OL p (elt p)
           lem31 = record { px = A∋elt p ;  is-below = case1 p-refl  }
           lem32 : odef (* (& (downHOD L OL p))) (elt q) → ⊥
           lem32 lt = ⊥-elim ( nq<p lem33 ) where
              lem33 : q p< p
              lem33 with DownP.is-below (eq→ *iso lt)
              ... | case1 eq = ⊥-elim ( ne (p=resp refl refl (p-sym eq) ))
              ... | case2 lt = p<-resp (p-refl1 refl) p-refl lt

    -- we can create smaller element ( larger set ) from any element in u
    --   which is not in u
    --

    record  CCond  (L : HOD) (OL : OrderedHOD L)
         (u : HODElement (Power L) ) (ou : odef (Topology.OS (TOPP L OL)) (elt u) ) (q : HODElement L) (nuq : ¬ ( odef (* (elt u)) (elt q) ))
            : Set n where
        open Topology
        open OrderedHOD OL
        field
          r :  HODElement L
          r≤q :  r p≤ q
          prop : (s : HODElement L) → s p≤ r → ¬ ( odef (* (elt u)) (elt s) )

    CCond-lem01 : (L : HOD) (OL : OrderedHOD L)  (u : HODElement (Power L) ) (ou : odef (Topology.OS (TOPP L OL)) (elt u) )
        → Interior (TOPP L OL) (Cl (TOPP L OL) (* (elt u))) ⊆ (* (elt u))
        → (q : HODElement L) (nuq : ¬ ( odef (* (elt u)) (elt q) )) → CCond L OL u ou q nuq
    CCond-lem01 L OL u ou icu q nuq = record { r = r ; r≤q = r≤q ; prop = prop } where
        open Topology
        open OrderedHOD OL

        nIC : ¬ odef (Interior (TOPP L OL) (Cl (TOPP L OL) (* (elt u)))) (elt q)
        nIC iq = nuq (icu iq)

        ncl=cl : (L ＼ Union (OCl (TOPP L OL) (* (elt u))))  =h= Cl (TOPP L OL) (* (elt u))
        ncl=cl = cc00 (TOPP L OL) (* (elt u))

        lem02 : ¬ (downHOD L OL q ⊆ Cl (TOPP L OL) (* (elt u)))
        lem02 le = nIC lem03 where
           lem03 : odef (Interior (TOPP L OL) (Cl (TOPP L OL) (* (elt u)))) (elt q)
           lem03  = ⟪ A∋elt q , record { v = & (downHOD L OL q)  ; nv = record { u = & (downHOD L OL q) ; ou = downHOD∈OS L OL q
              ; ux = eq← *iso record { px = A∋elt q ; is-below = case1 p-refl }  ; v⊆P = λ lt → DownP.px (eq→ *iso lt)
              ; u⊆v = λ lt → lt } ; v⊆A = λ lt → lem06 (eq→ *iso lt) } ⟫ where
              lem06 :  {x : Ordinal} → odef (downHOD L OL q) x → odef (Cl (TOPP L OL) (* (elt u))) x
              lem06 = le

        lem03 : ¬ ((downHOD L OL q) =h= od∅ )
        lem03 eq = lem02 ( λ lt → ⊥-elim ((¬x<0  ( eq→ eq  lt ))))  -- q

        lem06 : ¬ ( ( downHOD L OL q ∩  (L ＼ (Cl (TOPP L OL) (* (elt u))))) =h= od∅  )
        lem06 eq = lem02 (lem11 eq) where
           lem12 : {A B : HOD} → A ⊆ L → ( A ∩  (L ＼ B)) =h= od∅  → A ⊆ B 
           lem12 {A} {B} al eq {x} ax with p∨¬p (odef B x)
           ... | case1 bx = bx
           ... | case2 nbx = ⊥-elim ( ¬x<0 (eq→ eq lem13) )  where
                lem13 : odef ( A ∩  (L ＼ B)) x
                lem13 = ⟪ ax , ⟪ al ax  , nbx ⟫ ⟫
           lem11 : ( downHOD L OL q ∩  (L ＼ (Cl (TOPP L OL) (* (elt u)))))=h= od∅  → (downHOD L OL q ⊆ Cl (TOPP L OL) (* (elt u))) 
           lem11 eq ax = lem12 {downHOD L OL q} {Cl (TOPP L OL) (* (elt u))} (λ dx → DownP.px dx) eq  ax

        DNCl : HOD
        DNCl = downHOD L OL q ∩  (L ＼ (Cl (TOPP L OL) (* (elt u))))

        r : HODElement L
        r = record { elt = & (minimal DNCl lem06 ) ; A∋elt = DownP.px (proj1 (x∋minimal DNCl lem06))  }

        lem04 : odef (downHOD L OL q) (elt r)
        lem04 = proj1 ( x∋minimal DNCl lem06 )

        r≤q : r p≤ q
        r≤q = p≤-resp (p-refl1 refl) (p-refl1 refl) (  DownP.is-below lem04 )

        nrCl : ¬ (odef (Cl (TOPP L OL) (* (elt u))) (elt r))
        nrCl = proj2 (proj2 ( x∋minimal DNCl lem06 ))

        prop :  (s : HODElement L) → s p≤ r → ¬ odef (* (elt u)) (elt s)
        prop s s≤r us = lem08 where
           lem07 : odef (L ＼ Union (OCl (TOPP L OL) (* (elt u)))) (elt r) → ⊥
           lem07 nocl = nrCl ( eq→ ncl=cl nocl )
           lem05 : odef (Union (OCl (TOPP L OL) (* (elt u)))) (elt r)
           lem05 with p∨¬p (odef (Union (OCl (TOPP L OL) (* (elt u)))) (elt r) )
           ... | case1 it = it
           ... | case2 ne = ⊥-elim ( lem07 ⟪ A∋elt r , ne ⟫ )
           lem08 : ⊥
           lem08 with lem05
           ... | record { owner = v ; ao = ao ; ox = ox } = proj2 (lem09 us ) sv where
              ov : odef (OS (TOPP L OL)) v
              ov = proj1 ao
              sv : odef (* v) (elt s)
              sv = OpenP.is-open ov (elt r) (elt s) ox (A∋elt s) (p≤-resp (p-refl1 refl) (p-refl1 refl) s≤r )
              lem09 : * (elt u) ⊆ (L ＼ * v)
              lem09 = proj2 ao

    CCond-lem00 : (L : HOD) (OL : OrderedHOD L)  (u : HODElement (Power L) ) (ou : odef (Topology.OS (TOPP L OL)) (elt u) )
        → (cc : (q : HODElement L) (nuq : ¬ ( odef (* (elt u)) (elt q) )) → CCond L OL u ou q nuq)
        → Interior (TOPP L OL) (Cl (TOPP L OL) (* (elt u))) ⊆ (* (elt u))
    CCond-lem00 L OL u ou cc {x} = lem11 where
        open Topology
        open OrderedHOD OL

        lem12 : {q : Ordinal} → ¬ ( odef (* (elt u)) q ) → ¬ ( odef (Interior (TOPP L OL) (Cl (TOPP L OL) (* (elt u)))) q )
        lem12 {q} nuq ⟪ lq , record { v = v ; nv = record { u = s ; ou = os ; ux = sq ; v⊆P = v⊆P ; u⊆v = u⊆v } ; v⊆A = v⊆A } ⟫ = lem25 lem24 where
            qe : HODElement L
            qe = record { elt = q ; A∋elt = lq }
            ccd : CCond L OL u ou qe nuq
            ccd = cc _ nuq
            cl : odef (Cl (TOPP L OL) (* (elt u))) q
            cl = v⊆A (u⊆v sq )
            ncl : HOD
            ncl = L ＼ Union (OCl (TOPP L OL) (* (elt u)))  
            ncl=cl : (L ＼ Union (OCl (TOPP L OL) (* (elt u))))  =h= Cl (TOPP L OL) (* (elt u))
            ncl=cl = cc00 (TOPP L OL) (* (elt u))
            lem03 : odef ncl q
            lem03 = eq← ncl=cl cl
            lem20 : odef (L ＼ (* (elt u))) q
            lem20 = ⟪ lq , nuq ⟫
            se : HODElement (Power L)
            se = record { elt = s ; A∋elt = OS⊆PL (TOPP L OL) os  }
            r : HODElement L
            r =  CCond.r ccd
            lem21 : (q : HODElement L) → odef (* s) (elt q) → r p≤ q → odef (* s) (elt r)
            lem21 q sq r≤q = OpenP.is-open os _ _ sq (A∋elt r) (p≤-resp (p-refl1 refl) (p-refl1 refl) r≤q )
            lem23 : (* s)  ⊆ Cl (TOPP L OL) (* (elt u))
            lem23 sx = v⊆A ( u⊆v sx )
            lem24 : odef (Cl (TOPP L OL) (* (elt u))) (elt r)
            lem24 = v⊆A ( u⊆v (lem21 qe sq (CCond.r≤q ccd )))
            lem25 : ¬  odef (Cl (TOPP L OL) (* (elt u))) (elt r)
            lem25 clr = proj2 lem27 lem26 where
                lem27 : odef ncl (elt r)
                lem27 = eq← ncl=cl clr
                lem28 : odef (OS (TOPP L OL)) (& (downHOD L OL r))
                lem28 = downHOD∈OS L OL r
                lem26 : odef (Union (OCl (TOPP L OL) (* (elt u)))) (elt r)
                lem26 = record { owner = _ ; ao = ⟪ lem28 , lem29 ⟫ ; ox = eq← *iso record { px = A∋elt r ; is-below = case1 p-refl  } }  where
                   lem29 : {x : Ordinal} → odef (* (elt u)) x → odef (L ＼ * (& (downHOD L OL r))) x
                   lem29 {x} ux = ⟪ lxe1 , (λ drx → lem31 (eq→ *iso drx) ux ) ⟫ where
                      lxe1 : odef L x
                      lxe1 = OS⊆PL (TOPP L OL) ou _ ux
                      xe1 : HODElement L
                      xe1 = record { elt = x ; A∋elt = lxe1 }
                      lem30 : odef (downHOD L OL r) x → xe1 p≤ r
                      lem30 drx = p≤-resp (p-refl1 refl) (p-refl1 refl) (DownP.is-below drx )
                      lem31 : odef (downHOD L OL r) x → ¬ ( odef (* (elt u)) x )
                      lem31 drx = CCond.prop ccd xe1 ( lem30 drx )

        lem11 : {x : Ordinal} → odef (Interior (TOPP L OL) (Cl (TOPP L OL) (* (elt u)))) x → odef (* (elt u)) x
        lem11 {x} = contra-position2 {odef (* (elt u)) x } {odef (Interior (TOPP L OL) (Cl (TOPP L OL) (* (elt u)))) x }  lem12

    --   H(ω x ω, 2)    finite function  ℕ → ℕ → Bool
    --   { P | Func p ∧ (dom p ⊆ ω x ω) ∧ (finite (dom p) ∧ ran p ⊆ 2) }
    --       is List (Maybe (List (Maybe Two)))
    --       it is ordered by p ≤ q iff q ⊆ p
    -- Partial Order is proved by set inclusion only
    --

    -- element of H(ω x ω, 2) is a finite set of (ω x w) x Bool
    -- Hw≤ : (a b : HODElement HODww2) → Set n
    -- Hw≤ a b = (* (elt a)) ⊆ (* (elt b)) 

    HwwOrder : OrderedHOD HODww2
    HwwOrder = record {
           _p<_ = λ x y → ((* (elt y)) ⊆  (* (elt x)) ) ∧ ( ¬  ((* (elt x)) =h=  (* (elt y)) ))
        ;  _=p=_ =  λ x y → (* (elt x)) =h=  (* (elt y))
        ; PO = record {  isEquivalence = record { refl = ==-refl ; sym = ==-sym ; trans = ==-trans   }
           ; irrefl = λ {x} {y} → lem00 {x} {y} ; trans = λ {i} {j} {k} → lem01  {i} {j} {k}
              ; <-resp-≈ =  and (λ {x} {y} eq x<y → subst ( λ k → ((* k) ⊆ (* (elt x))) ∧ (¬ ((* (elt x)) =h= (* k) ))) (*=h=*→≡  eq) x<y )
                 (λ {x} {y} eq x<y → subst (λ k → ((((* (elt x)) ⊆ (* k)) ) ∧ (¬ ((* k ) =h= (* (elt x)) )))) (*=h=*→≡  eq) x<y ) }
        ;  p=resp = λ {x} {y} {w} {z} x≡w y≡z x=y → ==-trans (o≡→== (sym x≡w) ) (==-trans x=y (o≡→== y≡z ) )
        ;  p<-resp = λ x=w y=z y<x → subst₂ ( λ j k → ((* k) ⊆ (* j)) ∧ (¬ ((* j) =h= (* k) ))) (*=h=*→≡ x=w) (*=h=*→≡ y=z) y<x
      } where
         open import Data.Product renaming ( _,_ to and )
         lem00 : {x y : HODElement HODww2} → * (elt x) =h= * (elt y)
             → ¬ ( * (elt y) ⊆ * (elt x) ∧ (¬ (* (elt x) =h= * (elt y))) )
         lem00 {x} {y} eq  ⟪ y≤x , ne ⟫ = ⊥-elim ( ne eq )
         lem01 : {i j k : HODElement HODww2} →
            * (elt j) ⊆ * (elt i) ∧ (¬ (* (elt i) =h= * (elt j))) →
            * (elt k) ⊆ * (elt j) ∧ (¬ (* (elt j) =h= * (elt k))) →
            * (elt k) ⊆ * (elt i) ∧ (¬ (* (elt i) =h= * (elt k)))
         lem01 {i} {j} {k} ⟪ i≤j , ne1 ⟫ ⟪ j≤k , ne2 ⟫ = ⟪ ( λ lt → i≤j (j≤k lt )) , ( λ i=k → ⊥-elim ( ne1 (==-sym
            ( ⊆→== {* (elt j)} {* (elt i)} i≤j (λ {x} ix → (j≤k (eq→ i=k ix) ) ) ))))  ⟫

    Hww-lem00 : { a b : HODElement HODww2 } → * (elt a) ⊆ * (elt b) →  OrderedHOD._p≤_ HwwOrder b a
    Hww-lem00 {a} {b} ab with trio< (elt a) (elt b)
    ... | tri< a₁ ¬b ¬c = case2 ⟪ ab , (λ eq → ¬b (sym (*=h=*→≡ eq) )) ⟫
    ... | tri≈ ¬a b₁ ¬c = case1 (o≡→== (sym b₁))
    ... | tri> ¬a ¬b c = ⊥-elim (o≤> lem01 (subst₂ (λ j k → j o< k ) (sym &iso) (sym &iso) c  )) where
        lem01 : & (* (elt a)) o< osuc (& (* (elt b)))
        lem01 = ⊆→o≤ ab

    TW : Topology HODww2
    TW = TOPP HODww2 HwwOrder

    Hww2isCC :  (u : HODElement (Power HODww2) ) (ou : odef (Topology.OS TW) (elt u) )
        → (q : HODElement HODww2) (nuq : ¬ ( odef (* (elt u)) (elt q) )) → CCond HODww2 HwwOrder u ou q nuq
    Hww2isCC u ou q nuq with trio< (elt u) o∅ 
    ... | tri< a ¬b ¬c = {! !}
    ... | tri≈ ¬a b ¬c = record { r = ? ; r≤q = ? ; prop = ? } 
    ... | tri> ¬a ¬b 0<u = record { r = ? ; r≤q = ? ; prop = ? } where
        open Topology
        open OrderedHOD HwwOrder
        -- first we prove on an open base
        lem30 : {a b : HOD } →  b ⊆ Union ( a  , b )
        lem30 {a} {b} bx = record { owner = _ ; ao = case2 refl ; ox = eq← *iso bx }
        a : HODElement HODww2
        a = ?
        lem32 : odef (* (elt u)) (elt a)
        lem32 = ?
        lem31 : ¬ ( (* (elt u)) ⊆ (* (elt q)) )
        lem31 uq = nuq ? 
        lem33 : ¬ ( (HODww2 ＼ (* (elt q))) =h= od∅ )
        lem33 = ?
        lem34 : HOD
        lem34 = minimal (HODww2 ＼ (* (elt q))) lem33
        r : HODElement HODww2
        r = record { elt = ? ; A∋elt = ? }  

        lem20 : {q : Ordinal} → (d : HODElement HODww2) → ¬ ( odef (downHOD HODww2 HwwOrder d)  q )
            → ¬ ( odef (Interior TW (Cl TW (downHOD HODww2 HwwOrder d) )) q )
        lem20 {q} d ndq ⟪ lq , record { v = v ; nv = record { u = w ; ou = ow ; ux = wq ; v⊆P = v⊆P ; u⊆v = u⊆v } ; v⊆A = v⊆A } ⟫ =
              lem40 se s≤r dds where
           -- dd is x p≤ d, it is open
           dd : HOD
           dd = downHOD HODww2 HwwOrder d
           -- q is not included in dd, (ndq), ¬ ( qe p≤ d )
           --  ¬ q p≤ d
           --    r p≤ q
           qe : HODElement HODww2
           qe = record { elt = q ; A∋elt = lq }
           --    with Hww2r.hww2 (A∋elt q ) generate compiler error
--          r : HODElement HODww2
--          r = record { elt = lem01 ; A∋elt = lem02 }  where
--              lem14 : ¬ (qe  p≤ d )   -- ¬ ( d ⊆ qe )  -- ¬ ( (d \ qe) ≡ od∅ )
--              lem14 q≤d = ⊥-elim ( ndq record { px = ? ; is-below = ? }  )
--              -- we invert the value of something isn (qe \ d), and create union with qe
--              -- that's lem01
--              lem01 : Ordinal
--              lem01 = & (Union ( < nat→ω (Hww2r.count (A∋elt qe))   , (* o∅)  > , * (elt qe) ) )
--              lem02 : Hww2r lem01
--              lem02  = record { count = suc ( Hww2r.count (A∋elt qe) ) ; hww2 = ?  } -- hj hφ ( Hww2r.hww2 (A∋elt qe) ) }
           r≤q : r p≤ qe
           r≤q = Hww-lem00 {qe} {r} (λ qx → eq← *iso (lem30 qx) )
           -- no extenstion of r is in dd because we inverted the value
           lem40 : (se  : HODElement HODww2 ) → se p≤ r → ¬ ( odef (downHOD HODww2 HwwOrder d) (elt se)  )
           lem40 = ?
           -- so we have to find (se  : HODElement HODww2 ) ∧ se p≤ r → ( odef (downHOD HODww2 HwwOrder d) (elt se)  )
           -- to make a contradiction from lem04?
           --
           -- if we have some point se out side of dd which is included in Cl dd and which is not touched in dd,
           -- we have some open  set, out side of dd which contains se, that is closed set which included in dd
           --
           --     if q is out of u, q is out of Cl u , because
           --        r ≤ q
           --        ∀ s ≤ r → ¬ (u ∋ s )
           --
           -- r p< q
           we : HODElement (Power HODww2)
           we = record { elt = w ; A∋elt = OS⊆PL TW ow  }
           -- w ∋ q, v⊆A means odef (Cl TW (downHOD HODww2 HwwOrder d) ) q
           --    q in not in dd, and it is in closure of dd
           lem04 : odef (Cl TW (downHOD HODww2 HwwOrder d) ) q
           lem04 = v⊆A ( u⊆v wq )
           se : HODElement HODww2
           se = ?
           s≤r : se p≤ r   -- r p≤ qe
           s≤r = ?
           s≤q : se p≤ qe
           s≤q = p≤-trans s≤r r≤q
           dds : odef (downHOD HODww2 HwwOrder d) (elt se)
           dds = record { px = ? ; is-below = ? }


    Hww2isRO :  (u : HODElement (Power HODww2) ) (ou : odef (Topology.OS TW) (elt u) )
        → (* (elt u)) =h= Interior TW (Cl TW (* (elt u)))
    Hww2isRO u ou = record { eq→ = lem00 ; eq← = lem31 } where 
        open Topology
        open OrderedHOD HwwOrder
        lem31 : Interior (TOPP HODww2 HwwOrder) (Cl (TOPP HODww2 HwwOrder) (* (elt u))) ⊆ (* (elt u))
        lem31 = CCond-lem00 HODww2 HwwOrder u ou (Hww2isCC u ou) 

        lem00 : {x : Ordinal} → odef (* (elt u)) x → odef (Interior TW (Cl TW (* (elt u)))) x
        lem00 {x} ux = ⟪ OS⊆PL TW ou  _ ux , record { v = elt u ; nv =
            record { u = elt u ; ou = ou ; ux = ux ; v⊆P = OS⊆PL TW ou  _  ; u⊆v = λ lt → lt } ; v⊆A = u⊆Clu TW (* (elt u)) (OS⊆PL TW ou  _  ) }  ⟫

    -- ( ∀ L ∋ q, u → u is open →  ¬ ( u ∋ q) → ∃ r ≤ q → L ∋ s → (s ≤ r ) → ¬ ( u ∋ s ) ) == (  Interior (Cl top u) ⊆  u )
    --
    -- we are unable to prove this without completeness of OP.
    --
    -- record  ROlem03 (L : HOD) (OL : OrderedHOD L) (u : HODElement (Power L) ) (ou : odef (Topology.OS (TOPP L OL)) (elt u) ) : Set n where
    --    open OrderedHOD OL
    --    field
    --       r : HODElement L
    --       prop : (q : HODElement L ) → ¬ ( odef (* (elt u)) (elt q) ) → ( r≤q : r p≤ q )
    --          → (s  : HODElement L ) → s p≤ r → ¬ ( odef (* (elt u)) (elt s)  )

    --
    -- Interior is a minimum open set containing x
    --
    ROH : (P : HOD) → (TP : Topology P) → HOD  -- regular open set of P
    ROH P TP = record { od = record { def = λ x → ((* x) ⊆ P )∧ (x ≡ & (Interior TP (Cl TP (* x)))) } ; odmax = osuc (& P )
       ; <odmax = λ {x} lt → subst (λ k → k o≤ & P) &iso ( ⊆→o≤ (λ {x} yx → proj1 lt yx )) }


    RO : (L : HOD)  (∋-p : (Q : HOD) → Q ⊆ L → ( x : HOD) → Dec0 ( x ∈ Q ))
         → (OL : OrderedHOD L )
         → BooleanAlgebra {n} {n} (HODElement (ROH L (TOPP L OL)))
    RO L ∋-p OL =  record { _≈_ = λ x y → (* (elt x)) =h= (* (elt y)) ; b1 = record { elt = & L ;  A∋elt =  ⟪ (λ lt → eq→ *iso lt ) , lem01 ⟫   }
          ; b0 = record { elt =  o∅  ;  A∋elt =  ⟪ (λ {x} lt → ⊥-elim (¬x<0 (eq→ o∅==od∅ lt) )) , lem00  ⟫ }
      ; -_ = λ x → record { elt = & ( L ＼ (Cl (TOPP L OL) (* (elt x)))) ; A∋elt = lem20 {x} }
      ; _+_ = λ x y → record { elt = & (Interior (TOPP L OL) (Cl (TOPP L OL) ((* (elt x)) ∪ (* (elt y)))))
          ; A∋elt = lem400 x y    }
      ; _x_ = λ x y → record { elt = & ((* (elt x)) ∩ (* (elt y))) ; A∋elt = ? }
       ; isBooleanAlgebra = record {
         isEquivalence = record { refl = ==-refl ; sym = ==-sym ; trans = ==-trans }
         ; x-resp = λ {f} {g} {h} {i} f=g h=i → ==-trans *iso ( ==-trans ?  (==-sym *iso))
         ; +-resp =  λ {f} {g} {h} {i} f=g h=i → ==-trans *iso (==-trans ?  (==-sym *iso)) ; neg-resp = λ {f} {g}  f=g → record { eq→ = λ lt → eq← *iso ⟪ proj1 ( eq→ *iso lt ) , (λ lt1 → proj2 (eq→ *iso lt) ?  ) ⟫
             ; eq← = λ lt → eq← *iso ⟪ proj1 ( eq→ *iso lt ) , (λ lt1 → proj2 (eq→ *iso lt) ?  ) ⟫ }
         ; +-assoc = λ {a} {b} {c} →  record { eq→ = λ lt → eq← *iso ?   ; eq← = λ lt → eq← *iso ?  }
         ; x-assoc = λ {a} {b} {c} →
            record { eq→ = λ lt → eq← *iso ?
                   ; eq← = λ lt → eq←  *iso ? }
         ; +-sym = λ {a} {b} →  record { eq→ = λ {x} lt → eq← *iso ?  ; eq← = λ  lt → eq← *iso ?   }
         ; x-sym = λ {a} {b} →  record { eq→ = λ lt → eq← *iso ? ; eq← = λ lt → eq← *iso ? }
         ; +-aab = λ {a} {b} →  record { eq→ = λ lt → ? ; eq← = λ lt → eq← *iso ?  }
         ; x-aab = λ {a} {b} →  record { eq→ = λ lt → ?  ; eq← = λ ax →  eq← *iso ?     }
         ; +-dist = λ {p} {q} {r} → ?
         ; x-dist = λ {p} {q} {r} → ?
         ; a+0 = λ {a} →  record { eq→ = λ lt →  ? ; eq← = λ lt → eq← *iso ?  }
         ; ax1 = λ {a} →  record { eq→ = λ lt → ? ; eq← = λ ax → ? } -- eq← *iso ⟪ ax , eq← *iso (OS⊆PL H (A∋elt a) _ ax)  ⟫  }
         ; a+-a1 = λ {a} →  record { eq→ = λ lt → eq← *iso ?
             ; eq← = λ lt → eq← *iso  ?   }
         ; ax-a0 =  λ {a} →  record { eq→ = λ lt → ⊥-elim ?
               ; eq← = λ lt → ⊥-elim ( ¬x<0 ( eq→ o∅==od∅ lt )) }
           } } where
       open Topology
       ROE = HODElement (ROH L (TOPP L OL))
       open OrderedHOD OL
       top = TOPP L OL
       lem100 : {u x y : HODElement L} {z : Ordinal } → odef (OS top ) (elt u) → odef (* (elt u)) (elt x) → y p≤ x → odef (* (elt u)) (elt y)
       lem100 {u} {x} {y} ou ux y≤x = OpenP.is-open ou _ _ ux (A∋elt y) (p≤-resp ? ? y≤x )
       lem09 : (x : Ordinal) → (* x) ⊆ od∅ → x ≡ o∅
       lem09 x lt with trio< x o∅
       ... | tri< a ¬b ¬c = ⊥-elim ( ¬x<0 a  )
       ... | tri≈ ¬a b ¬c = b
       ... | tri> ¬a ¬b c = ⊥-elim ( o≤> (subst₂ (λ j k → j o< k ) &iso (cong osuc ord-od∅) lem10  ) c) where
         lem10 : & (* x) o< osuc (& od∅ )
         lem10 = ⊆→o≤  lt
       lem08 : (x : Ordinal) → (nv : InteriorR top  od∅ x)  → InteriorR.v nv ≡ o∅
       lem08 x nv = lem09 _ (InteriorR.v⊆A nv)
       lem11 : OpenP L OL (& L )
       lem11 = record { u⊆P = λ lt → eq→ *iso lt  ; is-open = λ x y ux Ly lt → eq← *iso Ly  }
       lem14 : (x : Ordinal) → odef od∅  x → ⊥
       lem14 x lt = ⊥-elim ( ¬x<0 lt  )
       lem13 : (x : Ordinal) → odef (* o∅ ) x → ⊥
       lem13 x lt = lem14 _ (eq→  o∅==od∅ lt )
       lem12 : & L ≡ & (L ＼ * o∅)
       lem12 = ==→o≡ record { eq→ = λ lx → ⟪ lx , (λ lt → lem13 _ lt ) ⟫  ; eq← = λ lt → proj1 lt  }
          -- open BAlgebra O HODAxiom ho< L ∋-p
       lem06 : Cl top (* o∅) =h= * o∅
       lem06 = record { eq→ = λ {x} lt → proj2 lt o∅ ⟪ (λ lt1 →  ⊥-elim (lem13 _ lt1) )  , subst (λ k → OpenP L OL k ) lem12 lem11 ⟫  (λ lt → lt )
          ; eq← = λ lt → ⊥-elim ( ¬x<0 (eq→ o∅==od∅ lt)  ) }
       lem02 : (x : Ordinal) → ¬ ( InteriorR top (Cl top (* o∅)) x )
       lem02 x lt = ⊥-elim ( ¬x<0 (eq→ lem03 ( Neighbor.ux (InteriorR.nv lt ) ))) where
          lem04 : {x : Ordinal} → (* (InteriorR.v lt )) ⊆ (Cl top (* o∅))
          lem04 = InteriorR.v⊆A lt
          lem05 : {x : Ordinal } → (* (Neighbor.u (InteriorR.nv lt ))) ⊆ (* o∅)
          lem05 {y} lt1 = eq→ lem06 (lem04 {y} ( Neighbor.u⊆v (InteriorR.nv lt) lt1  ) )
          lem03 : (* (Neighbor.u (InteriorR.nv lt ))) =h= od∅
          lem03 = record { eq→ = λ {y} lt1 → eq→ o∅==od∅ (lem05 {y} lt1 ) ; eq← = λ lt → ⊥-elim ( ¬x<0 lt  ) }
       lem00 : o∅ ≡ & (Interior top (Cl top (* o∅)))
       lem00 = trans (sym ord-od∅) (==→o≡ record { eq→ = λ lt → ⊥-elim ( ¬x<0 lt ) ; eq← = λ lt → ⊥-elim ( lem02 _ (proj2 lt)) } )
       lem01 : & L ≡ & (Interior top (Cl top (* (& L))))
       lem01 = ==→o≡ record { eq→ = λ lt → ⟪ lt ,
             record { v = & L ; nv = record { u = & L ; ou = lem11 ; ux = eq← *iso lt ; v⊆P = λ lt → eq→ *iso lt ; u⊆v = λ lt → lt }
                ; v⊆A = λ lx → ⟪ eq→ *iso lx , (λ y lc L⊆c → L⊆c lx ) ⟫ } ⟫
           ; eq← = λ lt → proj1 lt }

       lem30 : HODElement (ROH L top) → HODElement (Power L)
       lem30 er = record { elt = elt er ; A∋elt = λ z lt → proj1 (A∋elt er) lt }
       negcl : (x : HODElement (ROH L top)) → HOD
       negcl x = Cl top  (* (& (L ＼ Cl top (* (elt x)))))
       lem40 :  {a b : HOD} → a =h= b →  (L ＼ a ) =h=  (L ＼ b)
       lem40 {a} {b} a=b = record { eq→ = λ lt → ⟪ proj1 lt , (λ lt1 → proj2 lt (eq← a=b lt1) ) ⟫
          ; eq← = λ lt → ⟪ proj1 lt ,  (λ lt1 → proj2 lt (eq→  a=b lt1) ) ⟫ }

       lem39 :  {A B C : HOD } → A ⊆ B → (L ＼ A ) ⊆ C  → (L ＼ B) ⊆ C
       lem39 {A} {B} {C} ab lac {x} lbc  = lac ⟪ proj1 lbc , (λ ax → proj2 lbc (ab ax)  ) ⟫

       lem300 : {x : ROE} → (* (elt x)) =h= Interior top  (Cl top  (* (elt x)))   -- from Regular open set definition
       lem300 {x} = ord→== ( trans &iso (proj2 ( A∋elt x )))

       lem20 : {x : ROE} →  * (& (L ＼ Cl top (* (elt x)))) ⊆ L ∧ (& (L ＼ Cl top (* (elt x))) ≡
             & (Interior top (Cl top (* (& (L ＼ Cl top (* (elt x))))))))
       lem20 {x} = ⟪ (λ lt → (proj1 (eq→ *iso lt))) , ==→o≡ record { eq→ = lem21 ; eq← = λ {z} lt → lem33 (eq→ (Interrior-cong top lem31 ) lt ) } ⟫ where
          lem21 : {z : Ordinal} → odef ((L ＼ Cl top (* (elt x)))) z
             → odef (Interior top (Cl top (* (& (L ＼ Cl top (* (elt x))))))) z
          lem21 {z} ⟪ lz , ne ⟫ = ⟪ lz ,  record { v = & lem200 ; nv = record { u = _ ; ou = lem202
                 ; ux = lem201 ; v⊆P = λ lt → proj1 (eq→ *iso lt) ; u⊆v = λ lt → lt  } ; v⊆A = lem203 } ⟫ where
             lem22 : odef (Cl top (* (elt x))) z → ⊥
             lem22 = ne
             lem200 : HOD
             lem200 = L ＼ Cl top (* (elt x))
             lem201 : odef (* (& lem200)) z
             lem201 = eq← *iso ⟪ lz , ne ⟫
             lem202 : OpenP L OL (& lem200)
             lem202 = P＼CS=OS top (CS∋Cl top (* (elt x)) )
             lem203 : {w : Ordinal} → odef (* (& lem200)) w → odef (Cl top (* (& (L ＼ Cl top (* (elt x)))))) w
             lem203 {w} clw = u⊆Clu top (* (& (L ＼ Cl top (* (elt x))))) (λ lc → proj1 (eq→ *iso lc) ) clw
          lem31 : (Cl top (* (& (L ＼ Cl top (* (elt x)))))) =h= (Cl top (L ＼ Cl top (* (elt x))))
          lem31 = Cl-cong {L} {(* (& (L ＼ Cl top (* (elt x)))))} {(L ＼ Cl top (* (elt x)))} top *iso
          lem33 : {z : Ordinal} → odef (Interior top (Cl top (L ＼ Cl top (* (elt x))))) z
              → odef ((L ＼ Cl top (* (elt x)))) z  -- extrnal without boundary
          lem33 {z} ⟪ lz , record { v = v ; nv = nv ; v⊆A = v⊆A } ⟫ = ⟪ lz , ( λ clz → lem26 (proj2 clz) )  ⟫ where
              open BAlgebra O HODAxiom ho< L ∋-p
              cclx = (Cl top (L ＼ Cl top (* (elt x)))) -- extrnal including boundary
              lem26  : (clz :  (c : Ordinal) →  odef (CS top) c →  * (elt x) ⊆ * c → odef (* c) z ) → ⊥
              lem26 clz  = proj2 lem03 (Neighbor.ux nv) where
                  -- z is not in * (elt x), and not on the boundary, because it is the interior
                  lem24 : {w : Ordinal} → odef (* v) w → odef (Cl top  (L ＼ Cl top (* (elt x)))) w
                  lem24 = v⊆A
                  lem28 : Neighbor top z v
                  lem28 = nv
                  --  odef (* (Neighbor.u nv)) z     z is in external without boundary
                  --  odef (Cl top (* (elt x))) z  z is in internal including boundary
                  lem07 : {w : Ordinal} → ¬ odef cclx w → ¬ odef (* (Neighbor.u nv)) w
                  lem07 = contra-position ( λ nuw → v⊆A (Neighbor.u⊆v nv nuw ))

                  lem16 : {w : Ordinal} → odef (* (elt x)) w → ¬ ( odef cclx w )
                  lem16 {w} xw cw = proj2 lem312 cw  where
                       lem311 : odef L w ∧ InteriorR top (Cl top  (* (elt x))) w   -- internal excluding boundary
                       lem311 = eq→ (lem300 {x}) xw
                       lem312 : odef (L ＼  Cl top (L ＼  (Cl top  (* (elt x))) )) w
                       lem312 = eq→ (Interior-Cl top (Cl top  (* (elt x)))) (eq→ (lem300 {x}) xw ) -- from regular open set
                  lem15 : {w : Ordinal} → odef (* (elt x)) w → odef (* (& (L ＼ * (Neighbor.u nv)))) w  -- external
                  lem15 {w} xw = eq← *iso ⟪ proj1 (A∋elt x) xw , lem07 (lem16 xw)  ⟫
                  lem10 : odef (CS top) ( &  (L ＼ (* (Neighbor.u nv))) )
                  lem10 = P＼OS=CS top (subst (λ k → odef (OS top) k) (sym &iso)  (Neighbor.ou nv) )
                  lem03 :  odef (L ＼ (* (Neighbor.u nv))) z
                  lem03 = eq→ *iso ( clz ( &  (L ＼ (* (Neighbor.u nv))) ) lem10 lem15 )
       lem400 : (x y : ROE ) → ( * (& (Interior top (Cl top (* (elt x) ∪ * (elt y))))) ⊆ L) ∧
        (& (Interior top (Cl top (* (elt x) ∪ * (elt y))))
         ≡ & (Interior top (Cl top (* (& (Interior top (Cl top (* (elt x) ∪ * (elt y)))))))))
       lem400 x y = ⟪ (λ lt → proj1 (eq→ *iso lt))  , ==→o≡ lem401 ⟫ where
           lem401 : (Interior top (Cl top (* (elt x) ∪ * (elt y)))) =h=
               (Interior top (Cl top (* (& (Interior top (Cl top (* (elt x) ∪ * (elt y))))))))
           lem401 = record { eq→ = ? ; eq← = ? }

