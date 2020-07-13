open import Level
module Ordinals where

open import zf

open import Data.Nat renaming ( zero to Zero ; suc to Suc ;  ℕ to Nat ; _⊔_ to _n⊔_ ) 
open import Data.Empty
open import  Relation.Binary.PropositionalEquality
open import  logic
open import  nat
open import Data.Unit using ( ⊤ )
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.Core

record IsOrdinals {n : Level} (ord : Set n)  (o∅ : ord ) (osuc : ord → ord )  (_o<_ : ord → ord → Set n) (next : ord → ord ) : Set (suc (suc n)) where
   field
     Otrans :  {x y z : ord }  → x o< y → y o< z → x o< z
     OTri : Trichotomous {n} _≡_  _o<_ 
     ¬x<0 :   { x  : ord  } → ¬ ( x o< o∅  )
     <-osuc :  { x : ord  } → x o< osuc x
     osuc-≡< :  { a x : ord  } → x o< osuc a  →  (x ≡ a ) ∨ (x o< a)  
     not-limit-p :  ( x : ord  ) → Dec ( ¬ ((y : ord) → ¬ (x ≡ osuc y) ))
     TransFinite : { ψ : ord  → Set n }
          → ( (x : ord)  → ( (y : ord  ) → y o< x → ψ y ) → ψ x )
          →  ∀ (x : ord)  → ψ x
     TransFinite1 : { ψ : ord  → Set (suc n) }
          → ( (x : ord)  → ( (y : ord  ) → y o< x → ψ y ) → ψ x )
          →  ∀ (x : ord)  → ψ x

record IsNext {n : Level } (ord : Set n)  (o∅ : ord ) (osuc : ord → ord )  (_o<_ : ord → ord → Set n) (next : ord → ord ) : Set (suc (suc n)) where
   field
     x<nx :    { y : ord } → (y o< next y )
     osuc<nx : { x y : ord } → x o< next y → osuc x o< next y 
     ¬nx<nx :  {x y : ord} → y o< x → x o< next y →  ¬ ((z : ord) → ¬ (x ≡ osuc z)) 

record Ordinals {n : Level} : Set (suc (suc n)) where
   field
     ord : Set n
     o∅ : ord
     osuc : ord → ord
     _o<_ : ord → ord → Set n
     next :  ord → ord
     isOrdinal : IsOrdinals ord o∅ osuc _o<_ next
     isNext : IsNext ord o∅ osuc _o<_ next

module inOrdinal  {n : Level} (O : Ordinals {n} ) where

        Ordinal : Set n
        Ordinal  = Ordinals.ord O 

        _o<_ :  Ordinal  → Ordinal  → Set n
        _o<_ = Ordinals._o<_ O 

        osuc :   Ordinal  → Ordinal 
        osuc  = Ordinals.osuc O 

        o∅ :   Ordinal  
        o∅ = Ordinals.o∅ O

        next :   Ordinal → Ordinal
        next = Ordinals.next O

        ¬x<0 = IsOrdinals.¬x<0 (Ordinals.isOrdinal O)
        osuc-≡< = IsOrdinals.osuc-≡<  (Ordinals.isOrdinal O)
        <-osuc = IsOrdinals.<-osuc  (Ordinals.isOrdinal O)
        TransFinite = IsOrdinals.TransFinite  (Ordinals.isOrdinal O)
        TransFinite1 = IsOrdinals.TransFinite1  (Ordinals.isOrdinal O)

        x<nx = IsNext.x<nx (Ordinals.isNext O)
        osuc<nx = IsNext.osuc<nx (Ordinals.isNext O) 
        ¬nx<nx = IsNext.¬nx<nx (Ordinals.isNext O) 

        o<-dom :   { x y : Ordinal } → x o< y → Ordinal 
        o<-dom  {x} _ = x

        o<-cod :   { x y : Ordinal } → x o< y → Ordinal 
        o<-cod  {_} {y} _ = y

        o<-subst : {Z X z x : Ordinal }  → Z o< X → Z ≡ z  →  X ≡ x  →  z o< x
        o<-subst df refl refl = df

        ordtrans :  {x y z : Ordinal  }   → x o< y → y o< z → x o< z
        ordtrans = IsOrdinals.Otrans (Ordinals.isOrdinal O)

        trio< : Trichotomous  _≡_  _o<_ 
        trio< = IsOrdinals.OTri (Ordinals.isOrdinal O)

        o<¬≡ :  { ox oy : Ordinal } → ox ≡ oy  → ox o< oy  → ⊥
        o<¬≡ {ox} {oy} eq lt with trio< ox oy
        o<¬≡ {ox} {oy} eq lt | tri< a ¬b ¬c = ¬b eq
        o<¬≡ {ox} {oy} eq lt | tri≈ ¬a b ¬c = ¬a lt
        o<¬≡ {ox} {oy} eq lt | tri> ¬a ¬b c = ¬b eq

        o<> :   {x y : Ordinal   }  →  y o< x → x o< y → ⊥
        o<> {ox} {oy} lt tl with trio< ox oy
        o<> {ox} {oy} lt tl | tri< a ¬b ¬c = ¬c lt
        o<> {ox} {oy} lt tl | tri≈ ¬a b ¬c = ¬a tl
        o<> {ox} {oy} lt tl | tri> ¬a ¬b c = ¬a tl

        osuc-< :  { x y : Ordinal  } → y o< osuc x  → x o< y → ⊥
        osuc-< {x} {y} y<ox x<y with osuc-≡< y<ox
        osuc-< {x} {y} y<ox x<y | case1 refl = o<¬≡ refl x<y
        osuc-< {x} {y} y<ox x<y | case2 y<x = o<> x<y y<x

        osucc :  {ox oy : Ordinal } → oy o< ox  → osuc oy o< osuc ox  
        ----   y < osuc y < x < osuc x
        ----   y < osuc y = x < osuc x
        ----   y < osuc y > x < osuc x   -> y = x ∨ x < y → ⊥
        osucc {ox} {oy} oy<ox with trio< (osuc oy) ox
        osucc {ox} {oy} oy<ox | tri< a ¬b ¬c = ordtrans a <-osuc
        osucc {ox} {oy} oy<ox | tri≈ ¬a refl ¬c = <-osuc
        osucc {ox} {oy} oy<ox | tri> ¬a ¬b c with  osuc-≡< c
        osucc {ox} {oy} oy<ox | tri> ¬a ¬b c | case1 eq = ⊥-elim (o<¬≡ (sym eq) oy<ox)
        osucc {ox} {oy} oy<ox | tri> ¬a ¬b c | case2 lt = ⊥-elim (o<> lt oy<ox)

        osucprev :  {ox oy : Ordinal } → osuc oy o< osuc ox  → oy o< ox  
        osucprev {ox} {oy} oy<ox with trio< oy ox
        osucprev {ox} {oy} oy<ox | tri< a ¬b ¬c = a
        osucprev {ox} {oy} oy<ox | tri≈ ¬a b ¬c = ⊥-elim (o<¬≡ (cong (λ k → osuc k) b) oy<ox )
        osucprev {ox} {oy} oy<ox | tri> ¬a ¬b c = ⊥-elim (o<> (osucc c) oy<ox )

        open _∧_

        osuc2 :  ( x y : Ordinal  ) → ( osuc x o< osuc (osuc y )) ⇔ (x o< osuc y)
        proj2 (osuc2 x y) lt = osucc lt
        proj1 (osuc2 x y) ox<ooy with osuc-≡< ox<ooy
        proj1 (osuc2 x y) ox<ooy | case1 ox=oy = o<-subst <-osuc refl ox=oy
        proj1 (osuc2 x y) ox<ooy | case2 ox<oy = ordtrans <-osuc ox<oy 

        _o≤_ :  Ordinal → Ordinal → Set  n
        a o≤ b  = a o< osuc b -- (a ≡ b)  ∨ ( a o< b )


        xo<ab :  {oa ob : Ordinal } → ( {ox : Ordinal } → ox o< oa  → ox o< ob ) → oa o< osuc ob
        xo<ab   {oa} {ob} a→b with trio< oa ob
        xo<ab   {oa} {ob} a→b | tri< a ¬b ¬c = ordtrans a <-osuc
        xo<ab   {oa} {ob} a→b | tri≈ ¬a refl ¬c = <-osuc
        xo<ab   {oa} {ob} a→b | tri> ¬a ¬b c = ⊥-elim ( o<¬≡ refl (a→b c )  )

        maxα :   Ordinal  →  Ordinal  → Ordinal
        maxα x y with trio< x y
        maxα x y | tri< a ¬b ¬c = y
        maxα x y | tri> ¬a ¬b c = x
        maxα x y | tri≈ ¬a refl ¬c = x

        omin :    Ordinal  →  Ordinal  → Ordinal
        omin  x y with trio<  x  y
        omin x y | tri< a ¬b ¬c = x
        omin x y | tri> ¬a ¬b c = y
        omin x y | tri≈ ¬a refl ¬c = x

        min1 :   {x y z : Ordinal  } → z o< x → z o< y → z o< omin x y
        min1  {x} {y} {z} z<x z<y with trio<  x y
        min1  {x} {y} {z} z<x z<y | tri< a ¬b ¬c = z<x
        min1  {x} {y} {z} z<x z<y | tri≈ ¬a refl ¬c = z<x
        min1  {x} {y} {z} z<x z<y | tri> ¬a ¬b c = z<y

        --
        --  max ( osuc x , osuc y )
        --

        omax :  ( x y : Ordinal  ) → Ordinal 
        omax  x y with trio< x y
        omax  x y | tri< a ¬b ¬c = osuc y
        omax  x y | tri> ¬a ¬b c = osuc x
        omax  x y | tri≈ ¬a refl ¬c  = osuc x

        omax< :  ( x y : Ordinal  ) → x o< y → osuc y ≡ omax x y
        omax<  x y lt with trio< x y
        omax<  x y lt | tri< a ¬b ¬c = refl
        omax<  x y lt | tri≈ ¬a b ¬c = ⊥-elim (¬a lt )
        omax<  x y lt | tri> ¬a ¬b c = ⊥-elim (¬a lt )

        omax≡ :  ( x y : Ordinal  ) → x ≡ y → osuc y ≡ omax x y
        omax≡  x y eq with trio< x y
        omax≡  x y eq | tri< a ¬b ¬c = ⊥-elim (¬b eq )
        omax≡  x y eq | tri≈ ¬a refl ¬c = refl
        omax≡  x y eq | tri> ¬a ¬b c = ⊥-elim (¬b eq )

        omax-x :  ( x y : Ordinal  ) → x o< omax x y
        omax-x  x y with trio< x y
        omax-x  x y | tri< a ¬b ¬c = ordtrans a <-osuc
        omax-x  x y | tri> ¬a ¬b c = <-osuc
        omax-x  x y | tri≈ ¬a refl ¬c = <-osuc

        omax-y :  ( x y : Ordinal  ) → y o< omax x y
        omax-y  x y with  trio< x y
        omax-y  x y | tri< a ¬b ¬c = <-osuc
        omax-y  x y | tri> ¬a ¬b c = ordtrans c <-osuc
        omax-y  x y | tri≈ ¬a refl ¬c = <-osuc

        omxx :  ( x : Ordinal  ) → omax x x ≡ osuc x
        omxx  x with  trio< x x
        omxx  x | tri< a ¬b ¬c = ⊥-elim (¬b refl )
        omxx  x | tri> ¬a ¬b c = ⊥-elim (¬b refl )
        omxx  x | tri≈ ¬a refl ¬c = refl

        omxxx :  ( x : Ordinal  ) → omax x (omax x x ) ≡ osuc (osuc x)
        omxxx  x = trans ( cong ( λ k → omax x k ) (omxx x )) (sym ( omax< x (osuc x) <-osuc ))

        open _∧_

        o≤-refl :  { i  j : Ordinal } → i ≡ j → i o≤ j
        o≤-refl {i} {j} eq = subst (λ k → i o< osuc k ) eq <-osuc
        OrdTrans :  Transitive  _o≤_
        OrdTrans a≤b b≤c with osuc-≡< a≤b | osuc-≡< b≤c
        OrdTrans a≤b b≤c | case1 refl | case1 refl = <-osuc
        OrdTrans a≤b b≤c | case1 refl | case2 a≤c = ordtrans a≤c <-osuc
        OrdTrans a≤b b≤c | case2 a≤c | case1 refl = ordtrans a≤c <-osuc
        OrdTrans a≤b b≤c | case2 a<b | case2 b<c = ordtrans (ordtrans a<b  b<c) <-osuc

        OrdPreorder :   Preorder n n n
        OrdPreorder  = record { Carrier = Ordinal
           ; _≈_  = _≡_ 
           ; _∼_   = _o≤_
           ; isPreorder   = record {
                isEquivalence = record { refl = refl  ; sym = sym ; trans = trans }
                ; reflexive     = o≤-refl
                ; trans         = OrdTrans 
             }
         }

        FExists : {m l : Level} → ( ψ : Ordinal  → Set m ) 
          → {p : Set l} ( P : { y : Ordinal  } →  ψ y → ¬ p )
          → (exists : ¬ (∀ y → ¬ ( ψ y ) ))
          → ¬ p
        FExists  {m} {l} ψ {p} P = contra-position ( λ p y ψy → P {y} ψy p ) 

        next< : {x y z : Ordinal} → x o< next z  → y o< next x → y o< next z
        next< {x} {y} {z} x<nz y<nx with trio< y (next z)
        next< {x} {y} {z} x<nz y<nx | tri< a ¬b ¬c = a
        next< {x} {y} {z} x<nz y<nx | tri≈ ¬a b ¬c = ⊥-elim (¬nx<nx x<nz (subst (λ k → k o< next x) b y<nx)
           (λ w nz=ow → o<¬≡ nz=ow (subst₂ (λ j k → j o< k ) (sym nz=ow) nz=ow (osuc<nx (subst (λ k → w o< k ) (sym nz=ow) <-osuc) ))))
        next< {x} {y} {z} x<nz y<nx | tri> ¬a ¬b c = ⊥-elim (¬nx<nx x<nz (ordtrans c y<nx )
           (λ w nz=ow → o<¬≡ (sym nz=ow) (osuc<nx (subst (λ k → w o< k ) (sym nz=ow) <-osuc ))))

        osuc< : {x y : Ordinal} → osuc x ≡ y → x o< y
        osuc< {x} {y} refl = <-osuc 

        nexto=n : {x y : Ordinal} → x o< next (osuc y)  → x o< next y 
        nexto=n {x} {y} x<noy = next< (osuc<nx x<nx) x<noy

        nexto≡ : {x : Ordinal} → next x ≡ next (osuc x)  
        nexto≡ {x} with trio< (next x) (next (osuc x) ) 
        --    next x o< next (osuc x ) ->  osuc x o< next x o< next (osuc x) -> next x ≡ osuc z -> z o o< next x -> osuc z o< next x -> next x o< next x
        nexto≡ {x} | tri< a ¬b ¬c = ⊥-elim (¬nx<nx (osuc<nx  x<nx ) a
           (λ z eq → o<¬≡ (sym eq) (osuc<nx  (osuc< (sym eq)))))
        nexto≡ {x} | tri≈ ¬a b ¬c = b
        --    next (osuc x) o< next x ->  osuc x o< next (osuc x) o< next x -> next (osuc x) ≡ osuc z -> z o o< next (osuc x) ...
        nexto≡ {x} | tri> ¬a ¬b c = ⊥-elim (¬nx<nx (ordtrans <-osuc x<nx) c
           (λ z eq → o<¬≡ (sym eq) (osuc<nx  (osuc< (sym eq)))))

        record OrdinalSubset (maxordinal : Ordinal) : Set (suc n) where
          field
            os→ : (x : Ordinal) → x o< maxordinal → Ordinal
            os← : Ordinal → Ordinal
            os←limit : (x : Ordinal) → os← x o< maxordinal
            os-iso← : {x : Ordinal} →  os→  (os← x) (os←limit x) ≡ x
            os-iso→ : {x : Ordinal} → (lt : x o< maxordinal ) →  os← (os→ x lt) ≡ x

