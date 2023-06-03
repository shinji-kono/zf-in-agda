{-# OPTIONS --allow-unsolved-metas #-}

open import Level
open import Ordinals
module ZProduct {n : Level } (O : Ordinals {n})   where

open import logic
import OD
import ODUtil
import OrdUtil

open import Relation.Nullary
open import Relation.Binary
open import Data.Empty
open import Relation.Binary
open import Relation.Binary.Core
open import  Relation.Binary.PropositionalEquality
open import Data.Nat renaming ( zero to Zero ; suc to Suc ;  ℕ to Nat ; _⊔_ to _n⊔_ )

open OD O
open OD.OD
open OD.HOD
open ODAxiom odAxiom

open Ordinals.Ordinals  O
open Ordinals.IsOrdinals isOrdinal
open Ordinals.IsNext isNext
open OrdUtil O
open ODUtil O

open _∧_
open _∨_
open Bool

open _==_

<_,_> : (x y : HOD) → HOD
< x , y > = (x , x ) , (x , y )

ZFP<AB : {X Y x y : HOD} → X ∋ x → Y ∋ y  → < x , y > ⊆ Power ( Union (X , Y ))
ZFP<AB {X} {Y} {x} {y} xx yy (case1 refl ) z lt with subst (λ k → odef k z) *iso lt
... | case1 refl = record { owner = _ ; ao = case1 refl  ; ox = subst₂ (λ j k → odef j k) (sym *iso) refl xx  }
... | case2 refl = record { owner = _ ; ao = case1 refl  ; ox = subst₂ (λ j k → odef j k) (sym *iso) refl xx  }
ZFP<AB {X} {Y} {x} {y} xx yy (case2 refl ) z lt with subst (λ k → odef k z) *iso lt
... | case1 refl = record { owner = _ ; ao = case1 refl  ; ox = subst₂ (λ j k → odef j k) (sym *iso) refl xx  }
... | case2 refl = record { owner = _ ; ao = case2 refl  ; ox = subst₂ (λ j k → odef j k) (sym *iso) refl yy  }

exg-pair : { x y : HOD } → (x , y ) =h= ( y , x )
exg-pair {x} {y} = record { eq→ = left ; eq← = right } where
    left : {z : Ordinal} → odef (x , y) z → odef (y , x) z
    left (case1 t) = case2 t
    left (case2 t) = case1 t
    right : {z : Ordinal} → odef (y , x) z → odef (x , y) z
    right (case1 t) = case2 t
    right (case2 t) = case1 t

ord≡→≡ : { x y : HOD } → & x ≡ & y → x ≡ y
ord≡→≡ eq = subst₂ (λ j k → j ≡ k ) *iso *iso ( cong ( λ k → * k ) eq )

od≡→≡ : { x y : Ordinal } → * x ≡ * y → x ≡ y
od≡→≡ eq = subst₂ (λ j k → j ≡ k ) &iso &iso ( cong ( λ k → & k ) eq )

eq-prod : { x x' y y' : HOD } → x ≡ x' → y ≡ y' → < x , y > ≡ < x' , y' >
eq-prod refl refl = refl

xx=zy→x=y : {x y z : HOD } → ( x , x ) =h= ( z , y ) → x ≡ y
xx=zy→x=y {x} {y} eq with trio< (& x) (& y)
xx=zy→x=y {x} {y} eq | tri< a ¬b ¬c with eq← eq {& y} (case2 refl)
xx=zy→x=y {x} {y} eq | tri< a ¬b ¬c | case1 s = ⊥-elim ( o<¬≡ (sym s) a )
xx=zy→x=y {x} {y} eq | tri< a ¬b ¬c | case2 s = ⊥-elim ( o<¬≡ (sym s) a )
xx=zy→x=y {x} {y} eq | tri≈ ¬a b ¬c = ord≡→≡ b
xx=zy→x=y {x} {y} eq | tri> ¬a ¬b c  with eq← eq {& y} (case2 refl)
xx=zy→x=y {x} {y} eq | tri> ¬a ¬b c | case1 s = ⊥-elim ( o<¬≡ s c )
xx=zy→x=y {x} {y} eq | tri> ¬a ¬b c | case2 s = ⊥-elim ( o<¬≡ s c )

prod-eq : { x x' y y' : HOD } → < x , y > =h= < x' , y' > → (x ≡ x' ) ∧ ( y ≡ y' )
prod-eq {x} {x'} {y} {y'} eq = ⟪ lemmax , lemmay ⟫ where
    lemma2 : {x y z : HOD } → ( x , x ) =h= ( z , y ) → z ≡ y
    lemma2 {x} {y} {z} eq = trans (sym (xx=zy→x=y lemma3 )) ( xx=zy→x=y eq )  where
        lemma3 : ( x , x ) =h= ( y , z )
        lemma3 = ==-trans eq exg-pair
    lemma1 : {x y : HOD } → ( x , x ) =h= ( y , y ) → x ≡ y
    lemma1 {x} {y} eq with eq← eq {& y} (case2 refl)
    lemma1 {x} {y} eq | case1 s = ord≡→≡ (sym s)
    lemma1 {x} {y} eq | case2 s = ord≡→≡ (sym s)
    lemma4 : {x y z : HOD } → ( x , y ) =h= ( x , z ) → y ≡ z
    lemma4 {x} {y} {z} eq with eq← eq {& z} (case2 refl)
    lemma4 {x} {y} {z} eq | case1 s with ord≡→≡ s -- x ≡ z
    ... | refl with lemma2 (==-sym eq )
    ... | refl = refl
    lemma4 {x} {y} {z} eq | case2 s = ord≡→≡ (sym s) -- y ≡ z
    lemmax : x ≡ x'
    lemmax with eq→ eq {& (x , x)} (case1 refl)
    lemmax | case1 s = lemma1 (ord→== s )  -- (x,x)≡(x',x')
    lemmax | case2 s with lemma2 (ord→== s ) -- (x,x)≡(x',y') with x'≡y'
    ... | refl = lemma1 (ord→== s )
    lemmay : y ≡ y'
    lemmay with lemmax
    ... | refl with lemma4 eq -- with (x,y)≡(x,y')
    ... | eq1 = lemma4 (ord→== (cong (λ  k → & k )  eq1 ))

prod-≡ : { x x' y y' : HOD } → < x , y > ≡ < x' , y' > → (x ≡ x' ) ∧ ( y ≡ y' )
prod-≡ eq = prod-eq (ord→== (cong (&) eq ))

--
-- unlike ordered pair, ZFPair is not a HOD

data ord-pair : (p : Ordinal) → Set n where
   pair : (x y : Ordinal ) → ord-pair ( & ( < * x , * y > ) )

ZFPair : OD
ZFPair = record { def = λ x → ord-pair x }

-- _⊗_ : (A B : HOD) → HOD
-- A ⊗ B  = Union ( Replace' B (λ b lb → Replace' A (λ a la → < a , b > ) record { ≤COD = ? } ) ? )

-- product→ : {A B a b : HOD} → A ∋ a → B ∋ b  → ( A ⊗ B ) ∋ < a , b >
-- product→ {A} {B} {a} {b} A∋a B∋b = record { owner = _ ; ao = lemma1 ; ox = subst (λ k → odef k _) (sym *iso) lemma2  } where
--     lemma1 :  odef (Replace' B (λ b₁ lb → Replace' A (λ a₁ la → < a₁ , b₁ >) ? ) ? ) (& (Replace' A (λ a₁ la → < a₁ , b >) ? ))
--     lemma1 = ? -- replacement← B b B∋b ?
--     lemma2 : odef (Replace' A (λ a₁ la → < a₁ , b >) ? ) (& < a , b >)
--     lemma2 = ? -- replacement← A a A∋a ?

data ZFProduct  (A B : HOD) : (p : Ordinal) → Set n where
    ab-pair : {a b : Ordinal } → odef A a → odef B b → ZFProduct A B ( & ( < * a , * b > ) )

ZFP  : (A B : HOD) → HOD
ZFP  A B = record { od = record { def = λ x → ZFProduct A B x  }
        ; odmax =  osuc (& ( Power ( Union (A , B )))) ; <odmax = λ {y} px → lemma0 px }
   where
        lemma0 : {x : Ordinal } →  ZFProduct A B x → x o< osuc (& ( Power ( Union (A , B )) ))
        lemma0 ( ab-pair {a} {b} ax by ) = lemma1  where
            lemma1 : & < * a , * b > o< osuc (& (Power (Union (A , B))))
            lemma1 = ⊆→o≤ (ZFP<AB (subst (λ k → odef A k) (sym &iso) ax) (subst (λ k → odef B k) (sym &iso) by) )

ZFP→ : {A B a b : HOD} → A ∋ a → B ∋ b  → ZFP A B ∋ < a , b >
ZFP→ {A} {B} {a} {b} aa bb = subst (λ k → ZFProduct A B k ) (cong₂ (λ j k → & < j , k >) *iso *iso ) ( ab-pair aa bb )

zπ1 : {A B : HOD} → {x : Ordinal } → odef (ZFP A B) x → Ordinal
zπ1 {A} {B} {.(& < * _ , * _ >)} (ab-pair {a} {b} aa bb) = a

zp1 : {A B : HOD} → {x : Ordinal } → (zx : odef (ZFP A B) x) → odef A (zπ1 zx)
zp1 {A} {B} {.(& < * _ , * _ >)} (ab-pair {a} {b} aa bb ) = aa

zπ2 : {A B : HOD} → {x : Ordinal } → odef (ZFP A B) x → Ordinal
zπ2 (ab-pair {a} {b} aa bb) = b

zp2 : {A B : HOD} → {x : Ordinal } → (zx : odef (ZFP A B) x) → odef B (zπ2 zx)
zp2 {A} {B} {.(& < * _ , * _ >)} (ab-pair {a} {b} aa bb ) = bb

zp-iso :  { A B : HOD } → {x : Ordinal } → (p : odef (ZFP A B) x ) → & < * (zπ1 p) , * (zπ2 p) > ≡ x
zp-iso {A} {B} {_} (ab-pair {a} {b} aa bb)  = refl

zp-iso1 :  { A B : HOD } → {a b : Ordinal } → (p : odef (ZFP A B) (& < * a , * b > )) → (* (zπ1 p) ≡ (* a)) ∧ (* (zπ2 p) ≡ (* b))
zp-iso1 {A} {B} {a} {b} pab = prod-≡ (subst₂ (λ j k → j ≡ k ) *iso *iso (cong (*) zz11) ) where
      zz11 : & < * (zπ1 pab) , * (zπ2 pab) > ≡ & < * a , * b >
      zz11 = zp-iso pab

zp-iso0 :  { A B : HOD } → {a b : Ordinal } → (p : odef (ZFP A B) (& < * a , * b > )) → (zπ1 p ≡ a) ∧ (zπ2 p ≡ b)
zp-iso0 {A} {B} {a} {b} pab = ⟪ subst₂ (λ j k → j ≡ k ) &iso &iso (cong (&) (proj1 (zp-iso1 pab) ))
                              , subst₂ (λ j k → j ≡ k ) &iso &iso (cong (&) (proj2 (zp-iso1 pab) ) )  ⟫

-- ZFP⊆⊗ :  {A B : HOD} {x : Ordinal} → odef (ZFP A B) x → odef (A ⊗ B) x
-- ZFP⊆⊗ {A} {B} {px} ( ab-pair {a} {b} ax by ) = product→ (d→∋ A ax) (d→∋ B by)

-- ⊗⊆ZFP : {A B x : HOD} → ( A ⊗ B ) ∋ x → odef (ZFP A B) (& x)
-- ⊗⊆ZFP {A} {B} {x} record { owner = owner ; ao = record { z = a ; az = ba ; x=ψz = x=ψa } ; ox = ox } = zfp01 where
--        zfp02 : Replace' A (λ z lz → < z , * a >) record { ≤COD = ? }  ≡ * owner
--        zfp02 = subst₂ ( λ j k → j ≡ k ) *iso refl (sym (cong (*) x=ψa ))
--        zfp01 : odef (ZFP A B) (& x)
--        zfp01 with subst (λ k → odef k (& x) ) (sym zfp02) ox
--        ... | t = ?
--        -- ... | record { z = b ; az = ab ; x=ψz = x=ψb } = subst (λ k → ZFProduct A B k ) (sym x=ψb) (ab-pair ab ba)

ZPI1 : (A B : HOD) → HOD
ZPI1 A B = Replace' (ZFP A B) ( λ x px → * (zπ1 px )) {Union A} record { ≤COD  = lemma1 } where
    lemma1 : {x : Ordinal } (lt : odef (ZFP A B) x) → * (zπ1 lt) ⊆ Union A
    lemma1  (ab-pair {a} {b} aa bb) {x} ax = record { owner = _ ; ao = aa ; ox = ax }

ZPI2 : (A B  : HOD) → HOD
ZPI2 A B = Replace' (ZFP A B) ( λ x px → * (zπ2 px )) {Union B} record { ≤COD  = lemma1 } where
    lemma1 : {x : Ordinal } (lt : odef (ZFP A B) x) → * (zπ2 lt) ⊆ Union B
    lemma1  (ab-pair {a} {b} aa bb) {x} bx = record { owner = _ ; ao = bb ; ox = bx }

ZFProj1-iso : {P Q : HOD} {a b x : Ordinal } ( p : ZFProduct P Q x ) → x ≡ & < * a , * b > → zπ1 p ≡ a
ZFProj1-iso {P} {Q} {a} {b} (ab-pair {c} {d} zp zq) eq with prod-≡ (subst₂ (λ j k → j ≡ k) *iso *iso (cong (*) eq))
... | ⟪ a=c , b=d ⟫ = subst₂ (λ j k → j ≡ k) &iso &iso (cong (&) a=c)

ZFProj2-iso : {P Q : HOD} {a b x : Ordinal } ( p : ZFProduct P Q x ) → x ≡ & < * a , * b > → zπ2 p ≡ b
ZFProj2-iso {P} {Q} {a} {b} (ab-pair {c} {d} zp zq) eq with prod-≡ (subst₂ (λ j k → j ≡ k) *iso *iso (cong (*) eq))
... | ⟪ a=c , b=d ⟫ = subst₂ (λ j k → j ≡ k) &iso &iso (cong (&) b=d)

ZPI1-iso : (A B : HOD) → {b : Ordinal } → odef B b → ZPI1 A B ≡ A
ZPI1-iso P Q {q} qq = ==→o≡ record { eq→ = ty20 ; eq← = ty22 } where
     ty21 : {a b : Ordinal } → (pz : odef P a) → (qz : odef Q b) → ZFProduct P Q (& (* (& < * a , * b >)))
     ty21 pz qz = subst (odef (ZFP P Q)) (sym &iso) (ab-pair pz qz )
     ty32 : {a b : Ordinal } → (pz : odef P a) → (qz : odef Q b) → zπ1 (ty21 pz qz) ≡ a
     ty32 {a} {b} pz qz  = ty33 (ty21 pz qz) (cong (&) *iso) where
         ty33 : {a b x : Ordinal } ( p : ZFProduct P Q x ) → x ≡ & < * a , * b > → zπ1 p ≡ a
         ty33 {a} {b} (ab-pair {c} {d} zp zq) eq with prod-≡ (subst₂ (λ j k → j ≡ k) *iso *iso (cong (*) eq))
         ... | ⟪ a=c , b=d ⟫ = subst₂ (λ j k → j ≡ k) &iso &iso (cong (&) a=c)
     ty20 : {x : Ordinal} → odef (ZPI1 P Q) x → odef P x
     ty20 {x} record { z = _ ; az = ab-pair {a} {b} pz qz ; x=ψz = x=ψz } = subst (λ k → odef P k) a=x pz  where
         ty24 : * x  ≡ * a
         ty24 = begin
            * x ≡⟨ cong (*) x=ψz ⟩
            _ ≡⟨ *iso  ⟩
            * (zπ1 (subst (odef (ZFP P Q)) (sym &iso) (ab-pair pz qz))) ≡⟨ cong (*) (ty32 pz qz) ⟩
            * a ∎ where open ≡-Reasoning
         a=x : a  ≡ x
         a=x = subst₂ (λ j k → j ≡ k ) &iso &iso (cong (&) (sym ty24))
     ty22 : {x : Ordinal} → odef P x → odef (ZPI1 P Q) x
     ty22 {x} px = record { z = _ ; az = ab-pair px qq ; x=ψz = subst₂ (λ j k → j ≡ k) &iso refl (cong (&) ty12 ) }  where
         ty12 : * x ≡ * (zπ1 (subst (odef (ZFP P Q)) (sym &iso) (ab-pair px qq )))
         ty12 = begin
            * x ≡⟨ sym (cong (*) (ty32 px qq )) ⟩
            * (zπ1 (subst (odef (ZFP P Q)) (sym &iso) (ab-pair px qq ))) ∎ where open ≡-Reasoning

ZPI2-iso : (A B : HOD) → {b : Ordinal } → odef A b → ZPI2 A B ≡ B
ZPI2-iso P Q {p} pp = ==→o≡ record { eq→ = ty20 ; eq← = ty22 } where
     ty21 : {a b : Ordinal } → (pz : odef P a) → (qz : odef Q b) → ZFProduct P Q (& (* (& < * a , * b >)))
     ty21 pz qz = subst (odef (ZFP P Q)) (sym &iso) (ab-pair pz qz )
     ty32 : {a b : Ordinal } → (pz : odef P a) → (qz : odef Q b) → zπ2 (ty21 pz qz) ≡ b
     ty32 {a} {b} pz qz  = ty33 (ty21 pz qz) (cong (&) *iso) where
         ty33 : {a b x : Ordinal } ( p : ZFProduct P Q x ) → x ≡ & < * a , * b > → zπ2 p ≡ b
         ty33 {a} {b} (ab-pair {c} {d} zp zq) eq with prod-≡ (subst₂ (λ j k → j ≡ k) *iso *iso (cong (*) eq))
         ... | ⟪ a=c , b=d ⟫ = subst₂ (λ j k → j ≡ k) &iso &iso (cong (&) b=d)
     ty20 : {x : Ordinal} → odef (ZPI2 P Q) x → odef Q x
     ty20 {x} record { z = _ ; az = ab-pair {a} {b} pz qz ; x=ψz = x=ψz } = subst (λ k → odef Q k) a=x qz  where
         ty24 : * x  ≡ * b
         ty24 = begin
            * x ≡⟨ cong (*) x=ψz ⟩
            _ ≡⟨ *iso  ⟩
            * (zπ2 (subst (odef (ZFP P Q)) (sym &iso) (ab-pair pz qz))) ≡⟨ cong (*) (ty32 pz qz) ⟩
            * b ∎ where open ≡-Reasoning
         a=x : b  ≡ x
         a=x = subst₂ (λ j k → j ≡ k ) &iso &iso (cong (&) (sym ty24))
     ty22 : {x : Ordinal} → odef Q x → odef (ZPI2 P Q) x
     ty22 {x} qx = record { z = _ ; az = ab-pair pp qx  ; x=ψz = subst₂ (λ j k → j ≡ k) &iso refl (cong (&) ty12 ) }  where
         ty12 : * x ≡ * (zπ2 (subst (odef (ZFP P Q)) (sym &iso) (ab-pair pp qx)))
         ty12 = begin
            * x ≡⟨ sym (cong (*) (ty32 pp qx  )) ⟩
            * (zπ2 (subst (odef (ZFP P Q)) (sym &iso) (ab-pair pp qx  ))) ∎ where open ≡-Reasoning

record ZP1 (A B C : HOD) ( cab : C ⊆ ZFP A B ) (a : Ordinal) : Set n where
    field
       b : Ordinal
       aa : odef A a
       bb : odef B b
       c∋ab : odef C (& < * a , * b > )

ZP-proj1 : (A B C : HOD) → C  ⊆ ZFP A B → HOD
ZP-proj1 A B C cab = record { od = record { def = λ x → ZP1 A B C cab x } ; odmax = & A ; <odmax = λ lt → odef< (ZP1.aa lt) } 

ZP-proj1⊆ZFP : {A B C : HOD} → {cab : C ⊆ ZFP A B} → C ⊆ ZFP (ZP-proj1 A B C cab) B
ZP-proj1⊆ZFP {A} {B} {C} {cab} {c} cc with cab cc
... | ab-pair {a} {b} aa bb = ab-pair record { b = _ ; aa = aa ; bb = bb ; c∋ab = cc }  bb

ZP-proj1=rev : {A B a m : HOD} {b : Ordinal } → {cab : m ⊆ ZFP A B} → odef B b → a ⊆ A → m ≡ ZFP a B → a ≡ ZP-proj1 A B m cab 
ZP-proj1=rev {A} {B} {a} {m} {b} {cab} bb a⊆A refl = ==→o≡ record { eq→ = zp00 ; eq← = zp01 } where
     zp00 : {x : Ordinal } → odef a x → ZP1 A B (ZFP a B) cab x
     zp00 {x} ax = record { b = _ ; aa = a⊆A ax ; bb = bb ; c∋ab = ab-pair ax bb  }  
     zp01 : {x : Ordinal } → ZP1 A B (ZFP a B) cab x → odef a x
     zp01 {x} record { b = b ; aa = aa ; bb = bb ; c∋ab = c∋ab }  = zp02 c∋ab refl where
        zp02 : {z : Ordinal } → odef (ZFP a B) z → z ≡ & < * x , * b > → odef a x
        zp02 {.(& < * _ , * _ >)} (ab-pair {a1} {b1} aa1 bb1) eq = subst (λ k → odef a k) (*≡*→≡ zp03) aa1 where
           zp03 : * a1 ≡ * x
           zp03 = proj1 (prod-≡ (&≡&→≡ eq))

ZP-proj1-0 : {A B : HOD} {z : Ordinal } → {zab : * z ⊆ ZFP A B} → ZP-proj1 A B (* z) zab ≡ od∅ → z ≡ & od∅
ZP-proj1-0 {A} {B} {z} {zab} eq = uf10 where
         uf10 : z ≡ & od∅
         uf10 = trans (sym &iso) ( cong (&) (¬x∋y→x≡od∅ (λ {y} zy → uf11 zy ) )) where
             uf11 : {y : Ordinal } → odef (* z) y → ⊥ 
             uf11 {y} zy = ⊥-elim ( ¬x<0 (subst (λ k → odef k (zπ1 pqy)) eq uf12  ) ) where
                pqy : odef (ZFP A B) y
                pqy = zab zy
                uf14 : odef (* z) (& < * (zπ1 pqy) , * (zπ2 pqy) >)
                uf14 = subst (λ k → odef (* z) k ) (sym ( zp-iso pqy)) zy
                uf12 : odef (ZP-proj1 A B  (* z) zab) (zπ1 pqy) 
                uf12 = record { b = _ ; aa = zp1 pqy ; bb = zp2 pqy ; c∋ab = uf14 }

record ZP2 (A B C : HOD) ( cab : C ⊆ ZFP A B ) (b : Ordinal) : Set n where
    field
       a : Ordinal
       aa : odef A a
       bb : odef B b
       c∋ab : odef C (& < * a , * b > )

ZP-proj2 : (A B C : HOD) → C  ⊆ ZFP A B → HOD
ZP-proj2 A B C cab = record { od = record { def = λ x → ZP2 A B C cab x } ; odmax = & B ; <odmax = λ lt → odef< (ZP2.bb lt) } 

ZP-proj2⊆ZFP : {A B C : HOD} → {cab : C ⊆ ZFP A B} → C ⊆ ZFP A (ZP-proj2 A B C cab) 
ZP-proj2⊆ZFP {A} {B} {C} {cab} {c} cc with cab cc
... | ab-pair {a} {b} aa bb = ab-pair aa record { a = _ ; aa = aa ; bb = bb ; c∋ab = cc }  

ZP-proj2=rev : {A B a m : HOD} {b : Ordinal } → {cab : m ⊆ ZFP A B} → odef A b → a ⊆ B → m ≡ ZFP A a  → a ≡ ZP-proj2 A B m cab 
ZP-proj2=rev {A} {B} {a} {m} {b} {cab} bb a⊆A refl = ==→o≡ record { eq→ = zp00 ; eq← = zp01 } where
     zp00 : {x : Ordinal } → odef a x → ZP2 A B (ZFP A a ) cab x
     zp00 {x} ax = record { a = _ ; aa = bb ; bb = a⊆A ax ; c∋ab = ab-pair bb ax   }  
     zp01 : {x : Ordinal } → ZP2 A B (ZFP A a ) cab x → odef a x
     zp01 {x} record { a = b ; aa = aa ; bb = bb ; c∋ab = c∋ab }  = zp02 c∋ab refl where
        zp02 : {z : Ordinal } → odef (ZFP A a ) z → z ≡ & < * b , * x > → odef a x
        zp02 {.(& < * _ , * _ >)} (ab-pair {a1} {b1} aa1 bb1) eq = subst (λ k → odef a k) (*≡*→≡ zp03) bb1 where
           zp03 : * b1 ≡ * x
           zp03 = proj2 (prod-≡ (&≡&→≡ eq))

ZP-proj2-0 : {A B : HOD} {z : Ordinal } → {zab : * z ⊆ ZFP A B} → ZP-proj2 A B (* z) zab ≡ od∅ → z ≡ & od∅
ZP-proj2-0 {A} {B} {z} {zab} eq = uf10 where
         uf10 : z ≡ & od∅
         uf10 = trans (sym &iso) ( cong (&) (¬x∋y→x≡od∅ (λ {y} zy → uf11 zy ) )) where
             uf11 : {y : Ordinal } → odef (* z) y → ⊥ 
             uf11 {y} zy = ⊥-elim ( ¬x<0 (subst (λ k → odef k (zπ2 pqy)) eq uf12  ) ) where
                pqy : odef (ZFP A B) y
                pqy = zab zy
                uf14 : odef (* z) (& < * (zπ1 pqy) , * (zπ2 pqy) >)
                uf14 = subst (λ k → odef (* z) k ) (sym ( zp-iso pqy)) zy
                uf12 : odef (ZP-proj2 A B  (* z) zab) (zπ2 pqy) 
                uf12 = record { a = _ ; aa = zp1 pqy ; bb = zp2 pqy ; c∋ab = uf14 }

record Func (A B : HOD) : Set n where
    field
       func : {x : Ordinal } → odef A x → Ordinal
       is-func : {x : Ordinal } → (ax : odef A x) → odef B (func ax )
    fodmax : RXCod A (Power (Union (A , B))) (λ x ax → < x , * (func ax) >)
    fodmax = record { ≤COD = λ {x} ax →  lemma1 ax } where
        lemma1 : {x : HOD} → (ax : odef A (& x)) → < x , * (func ax) > ⊆ Power (Union (A , B)) 
        lemma1 {x} ax = ZFP<AB ax (subst (λ k → odef B k) (sym &iso) ( is-func ax ) )

data FuncHOD (A B : HOD) : (x : Ordinal) →  Set n where
     felm :  (F : Func A B) → FuncHOD A B (& ( Replace' A ( λ x ax → < x , (* (Func.func F {& x} ax )) > ) (Func.fodmax F) ))

FuncHOD→F : {A B : HOD} {x : Ordinal} → FuncHOD A B x → Func A B
FuncHOD→F {A} {B} (felm F) = F

FuncHOD=R : {A B : HOD} {x : Ordinal} → (fc : FuncHOD A B x) → (* x) ≡  Replace' A ( λ x ax → < x , (* (Func.func (FuncHOD→F fc) ax)) > ) (Func.fodmax (FuncHOD→F fc) )
FuncHOD=R {A} {B}  (felm F) = *iso

--
--  Set of All function from A to B
--

open import Relation.Binary.HeterogeneousEquality as HE using (_≅_ )

Funcs : (A B : HOD) → HOD
Funcs A B = record { od = record { def = λ x → FuncHOD A B x } ; odmax = osuc (& (ZFP A B))
       ; <odmax = λ {y} px → subst ( λ k → k o≤ (& (ZFP A B)) ) &iso (⊆→o≤ (lemma1 px)) } where
    lemma1 : {y : Ordinal } → FuncHOD A B y → {x : Ordinal} → odef (* y) x → odef (ZFP A B) x
    lemma1 {y} (felm F) {x} yx with subst (λ k → odef k x) *iso yx
    ... | record { z = z ; az = az ; x=ψz = x=ψz } = subst (λ k → ZFProduct A B k)
          (sym x=ψz) lemma4 where
       lemma4 : ZFProduct A B (& < * z , * (Func.func F (subst (λ k → odef A k) (sym &iso) az)) > )
       lemma4 = ab-pair az (Func.is-func F (subst (λ k → odef A k) (sym &iso) az))

record Injection (A B : Ordinal ) : Set n where
   field
       i→  : (x : Ordinal ) → odef (* A)  x → Ordinal
       iB  : (x : Ordinal ) → ( lt : odef (* A)  x ) → odef (* B) ( i→ x lt )
       iiso : (x y : Ordinal ) → ( ltx : odef (* A)  x ) ( lty : odef (* A)  y ) → i→ x ltx ≡ i→ y lty → x ≡ y

record HODBijection (A B : HOD ) : Set n where
   field
       fun←  : (x : Ordinal ) → odef A  x → Ordinal
       fun→  : (x : Ordinal ) → odef B  x → Ordinal
       funB  : (x : Ordinal ) → ( lt : odef A  x ) → odef B ( fun← x lt )
       funA  : (x : Ordinal ) → ( lt : odef B  x ) → odef A ( fun→ x lt )
       fiso← : (x : Ordinal ) → ( lt : odef B  x ) → fun← ( fun→ x lt ) ( funA x lt ) ≡ x
       fiso→ : (x : Ordinal ) → ( lt : odef A  x ) → fun→ ( fun← x lt ) ( funB x lt ) ≡ x

hodbij-refl : { a b : HOD } → a ≡ b → HODBijection a b
hodbij-refl {a} refl = record {
       fun←  = λ x _ → x
     ; fun→  = λ x _ → x
     ; funB  = λ x lt → lt
     ; funA  = λ x lt → lt
     ; fiso← = λ x lt → refl
     ; fiso→ = λ x lt → refl
    }

pj12 : (A B : HOD) {x : Ordinal} → (ab : odef (ZFP A B) x ) →
   (zπ1  (subst (odef (ZFP A B)) (sym &iso) ab) ≡ & (* (zπ1 ab ))) ∧
   (zπ2  (subst (odef (ZFP A B)) (sym &iso) ab) ≡ & (* (zπ2 ab )))
pj12 A B (ab-pair {x} {y} ax by) = ⟪ subst₂ (λ j k → j ≡ k ) &iso &iso (cong (&) (proj1 (prod-≡ pj24 )))
      , subst₂ (λ j k → j ≡ k ) &iso &iso (cong (&) (proj2 (prod-≡ pj24)))  ⟫ where
   pj22 : odef (ZFP A B) (& (* (& < * x , * y >)))
   pj22 = subst (odef (ZFP A B)) (sym &iso) (ab-pair ax by)
   pj23 : & < * (zπ1 pj22 ) , * (zπ2 pj22) > ≡ & (* (& < * x , * y >) )
   pj23 = zp-iso pj22
   pj24 : < * (zπ1 (subst (odef (ZFP A B)) (sym &iso) (ab-pair ax by))) , * (zπ2 (subst (odef (ZFP A B)) (sym &iso) (ab-pair ax by))) >
    ≡ < * (& (* x)) ,  * (& (* y)) >
   pj24 = subst₂ (λ j k → j ≡ k ) *iso *iso (cong (*) ( trans pj23 (trans &iso
       (sym (cong (&) (cong₂ (λ j k → < j , k >) *iso *iso)) ))))
pj02 : (A B : HOD) (x : Ordinal) → (ab : odef (ZFP A B) x ) → odef (ZPI2 A B) (zπ2 ab)
pj02 A B x ab = record { z = _ ; az = ab ; x=ψz = trans (sym &iso) (trans ( sym (proj2 (pj12 A B ab))) (sym &iso))  }
pj01 : (A B : HOD) (x : Ordinal) → (ab : odef (ZFP A B) x ) → odef (ZPI1 A B) (zπ1 ab)
pj01 A B x ab = record { z = _ ; az = ab ; x=ψz = trans (sym &iso) (trans ( sym (proj1 (pj12 A B ab))) (sym &iso))  }

pj2 :  (A B : HOD) (x : Ordinal) (lt : odef (ZFP A B) x) → odef (ZFP (ZPI2 A B) (ZPI1 A B)) (& < * (zπ2 lt) , * (zπ1 lt) >)
pj2 A B x ab = ab-pair (pj02 A B x ab)  (pj01 A B x ab)

aZPI1 : (A B : HOD) {y : Ordinal} → odef (ZPI1 A B) y → odef A y
aZPI1 A B {y} record { z = z ; az = az ; x=ψz = x=ψz } = subst (λ k → odef A k) (trans (
    trans (sym &iso) (trans (sym (proj1 (pj12 A B az))) (sym &iso))) (sym x=ψz)  ) ( zp1 az )
aZPI2 : (A B : HOD) {y : Ordinal} → odef (ZPI2 A B) y → odef B y
aZPI2 A B {y} record { z = z ; az = az ; x=ψz = x=ψz } = subst (λ k → odef B k) (trans (
    trans (sym &iso) (trans (sym (proj2 (pj12 A B az))) (sym &iso))) (sym x=ψz)  ) ( zp2 az )

pj1 :  (A B : HOD) (x : Ordinal) (lt : odef (ZFP (ZPI2 A B) (ZPI1 A B)) x) → odef (ZFP A B) (& < * (zπ2 lt) , * (zπ1 lt) >)
pj1 A B _ (ab-pair ax by) = ab-pair (aZPI1 A B by) (aZPI2 A B ax)

ZFPsym1 : (A B  : HOD) → HODBijection (ZFP A B) (ZFP (ZPI2 A B) (ZPI1 A B))
ZFPsym1 A B = record {
       fun←  = λ xy ab → & < * ( zπ2 ab) , * ( zπ1 ab) >
     ; fun→  = λ xy ab → & < * ( zπ2 ab) , * ( zπ1 ab) >
     ; funB  = pj2 A B
     ; funA  = pj1 A B
     ; fiso← = λ xy ab → pj00 A B ab
     ; fiso→ = λ xy ab → zp-iso ab
    } where
       pj10 : (A B : HOD) → {xy : Ordinal} → (ab : odef (ZFP (ZPI2 A B) (ZPI1 A B)) xy )
           → & < * (zπ1 ab) , * (zπ2 ab) > ≡ & < *  (zπ2 (pj1 A B xy ab)) ,  * (zπ1 (pj1 A B xy ab)) >
       pj10 A B {.(& < * _ , * _ >)} (ab-pair ax by ) = refl
       pj00 : (A B : HOD) → {xy : Ordinal} → (ab : odef (ZFP (ZPI2 A B) (ZPI1 A B)) xy )
           → & < * (zπ2 (pj1 A B xy ab)) , * (zπ1 (pj1 A B xy ab)) > ≡ xy
       pj00 A B {xy} ab = trans (sym (pj10 A B ab)) (zp-iso {ZPI2 A B} {ZPI1 A B} {xy} ab)

--
-- Bijection of (A x B) and (B x A) requires one element or axiom of choice
--
ZFPsym : (A B  : HOD) → {a b : Ordinal } → odef A a → odef B b  → HODBijection (ZFP A B) (ZFP B A)
ZFPsym A B aa bb = subst₂ ( λ j k → HODBijection (ZFP A B) (ZFP j k)) (ZPI2-iso A B aa) (ZPI1-iso A B bb) ( ZFPsym1 A B )

⊆-ZFP : {A B : HOD} {X Y x y : HOD} → X ⊆ A → Y ⊆ B → ZFP X Y ⊆ ZFP A B
⊆-ZFP {A} {B} {X} {y} X<A Y<B (ab-pair xx yy) = ab-pair (X<A xx) (Y<B yy)

record ZPC (A B C : HOD) ( cab : C ⊆ ZFP A B ) (x : Ordinal) : Set n where
    field
       a b : Ordinal
       aa : odef A a
       bb : odef B b
       c∋ab : odef C (& < * a , * b > )
       x=ba : x ≡ & < * b , * a >

ZPmirror : (A B C : HOD) → C  ⊆ ZFP A B → HOD
ZPmirror A B C cab = record { od = record { def = λ x → ZPC A B C cab x } ; odmax = osuc (& (Power (Union (B , A)))) ; <odmax = lemma0 } where
        lemma0 : {x : Ordinal } →  ZPC A B C cab x → x o< osuc (& ( Power ( Union (B , A )) ))
        lemma0 {x} record { a = a ; b = b ; aa = aa ; bb = bb ; c∋ab = c∋ab ; x=ba = x=ba } = subst (λ k → k o< _) (sym x=ba) lemma1  where
            lemma1 : & < * b , * a > o< osuc (& (Power (Union (B , A))))
            lemma1 = ⊆→o≤ (ZFP<AB (subst (λ k → odef B k) (sym &iso) bb) (subst (λ k → odef A k) (sym &iso) aa)  )

ZPmirror⊆ZFPBA : (A B C : HOD) → (cab : C  ⊆ ZFP A B ) → ZPmirror A B C cab ⊆ ZFP B A
ZPmirror⊆ZFPBA A B C cab {z} record { a = a ; b = b ; aa = aa ; bb = bb ; c∋ab = c∋ab ; x=ba = x=ba } 
    = subst (λ k → odef (ZFP B A) k) (sym x=ba) lemma2 where
        lemma2 : odef (ZFP B A) (& < * b , * a > )
        lemma2 = ZFP→ (subst (λ k → odef B k ) (sym &iso) bb) (subst (λ k → odef A k ) (sym &iso) aa) 

ZPmirror-iso : (A B C : HOD)  → (cab : C  ⊆ ZFP A B ) → ( {x y : HOD} → C ∋ < x , y > →  ZPmirror A B C cab ∋ < y , x > ) 
                                                       ∧ ( {x y : HOD} →  ZPmirror A B C cab ∋ < y , x > → C ∋ < x , y > )
ZPmirror-iso A B C cab = ⟪ zs00 refl   , zs01 ⟫ where
    zs00 : {x y : HOD} → {z : Ordinal} → z ≡ & < x , y > → odef C z → ZPmirror A B C cab ∋ < y , x >
    zs00 {x} {y} {z} eq cz with cab cz
    ... | ab-pair {a} {b} aa bb = record { a = _ ; b = _ ; aa = aa ; bb = bb ; c∋ab = cz 
       ; x=ba = cong₂ (λ j k → & < j , k >) (sym (proj2 (prod-≡ (subst₂ (λ j k → j ≡ k) *iso  *iso  (cong (*) eq)))))  
                                            (sym (proj1 (prod-≡ (subst₂ (λ j k → j ≡ k) *iso  *iso  (cong (*) eq))))) }
    zs01 : {x y : HOD} → ZPmirror A B C cab ∋ < y , x > → C ∋ < x , y >
    zs01 {x} {y} record { a = a ; b = b ; aa = aa ; bb = bb ; c∋ab = c∋ab ; x=ba = x=ba } = subst (λ k → odef C k ) zs02 c∋ab where
        zs02 : & < * a , * b > ≡ & < x , y >
        zs02 = cong₂ (λ j k → & < j , k >) (sym (proj2 (prod-≡ (subst₂ (λ j k → j ≡ k) *iso  *iso  (cong (*) x=ba)))))  
                                           (sym (proj1 (prod-≡ (subst₂ (λ j k → j ≡ k) *iso  *iso  (cong (*) x=ba))))) 

ZPmirror-rev : {A B C m : HOD}  → {cab : C  ⊆ ZFP A B } → ZPmirror A B C cab ≡ m 
       → {m⊆Z : m ⊆ ZFP B A } → ZPmirror B A m m⊆Z   ≡ C  
ZPmirror-rev {A} {B} {C} {m} {cab} eq {m⊆Z} = ==→o≡ record { eq→  = zs02 ; eq← = zs04 } where
    zs02 : {x : Ordinal} → ZPC B A m m⊆Z x → odef C x
    zs02 {x} record { a = a ; b = b ; aa = aa ; bb = bb ; c∋ab = c∋ab ; x=ba = x=ba } with subst (λ k → odef k (& < * a , * b > )) (sym eq) c∋ab 
    ... | record { a = b1 ; b = a1 ; aa = bb1 ; bb = aa1 ; c∋ab = c∋ab1 ; x=ba = x=ba1 } = subst (λ k → odef C k) zs03  c∋ab1 where
        a=a1 : * a ≡ * a1 
        a=a1 = proj1 (prod-≡ (subst₂ (λ j k → j ≡ k ) *iso *iso (cong (*) x=ba1)))
        b=b1 : * b ≡ * b1 
        b=b1 = proj2 (prod-≡ (subst₂ (λ j k → j ≡ k ) *iso *iso (cong (*) x=ba1)))
        zs03 : & < * b1 , * a1 > ≡ x
        zs03 = begin
          & < * b1 , * a1 > ≡⟨ cong₂ (λ j k → & < j , k >) (sym b=b1) (sym a=a1)  ⟩ 
          & < * b , * a > ≡⟨ sym x=ba ⟩ 
          x ∎ where open ≡-Reasoning
    zs04 : {x : Ordinal} → odef C x → ZPC B A m m⊆Z x 
    zs04 {x} cx with cab cx 
    ... | ab-pair {a} {b} aa bb  = record { a = b ; b = a ; aa = bb ; bb = aa 
      ; c∋ab = subst (λ k → odef k (& < * b , * a >)) eq zs05 ; x=ba = refl } where
        zs05 : odef (ZPmirror A B C cab)  (& < * b , * a >)
        zs05 = record { a = _ ; b = _ ; aa = aa ; bb = bb ; c∋ab = cx ; x=ba = refl } 

ZPmirror-⊆ : {A B C D : HOD}  → (C⊆D : C ⊆ D) → {cab : C  ⊆ ZFP A B } {dab : D  ⊆ ZFP A B } → ZPmirror A B C cab ⊆ ZPmirror A B D dab
ZPmirror-⊆ {A} {B} {C} {D} C⊆D {cab} {dab} {x} record { a = a ; b = b ; aa = aa ; bb = bb ; c∋ab = c∋ab ; x=ba = x=ba } = 
        record { a = _ ; b = _ ; aa = aa ; bb = bb ; c∋ab = C⊆D c∋ab ; x=ba = x=ba } 

ZPmirror-∩ : {A B C D : HOD}  → {cdab : (C ∩ D) ⊆ ZFP A B } {cab : C  ⊆ ZFP A B } {dab : D  ⊆ ZFP A B } 
        → ZPmirror A B (C ∩ D) cdab ≡ ZPmirror A B C cab ∩ ZPmirror A B D dab
ZPmirror-∩ {A} {B} {C} {D} {cdab} {cab} {dab} = ==→o≡ record { eq→ = za06 ; eq← = za07 } where
        za06 :  ZPmirror A B (C ∩ D) cdab ⊆ ( ZPmirror A B C cab ∩ ZPmirror A B D dab )
        za06 {x} record { a = a ; b = b ; aa = aa ; bb = bb ; c∋ab = c∋ab ; x=ba = x=ba } = ⟪
             record { a = _ ; b = _ ; aa = aa ; bb = bb ; c∋ab = proj1 c∋ab ; x=ba = x=ba } ,
             record { a = _ ; b = _ ; aa = aa ; bb = bb ; c∋ab = proj2 c∋ab ; x=ba = x=ba } ⟫
        za07 :  ( ZPmirror A B C cab ∩ ZPmirror A B D dab ) ⊆ ZPmirror A B (C ∩ D) cdab 
        za07 {x} ⟪ record { a = a ; b = b ; aa = aa ; bb = bb ; c∋ab = c∋ab1 ; x=ba = x=ba } ,
             record { a = a' ; b = b' ; aa = aa' ; bb = bb' ; c∋ab = c∋ab2 ; x=ba = x=ba' } ⟫ =
             record { a = a ; b = b ; aa = aa ; bb = bb ; c∋ab = ⟪ c∋ab1 , subst (λ k → odef D k) (sym zs02) c∋ab2 ⟫ ; x=ba = x=ba } where
            zs02 : & < * a , * b > ≡ & < * a' , * b' >
            zs02 = cong₂ (λ j k → & < j , k >) (sym (proj2 (prod-≡ (subst₂ (λ j k → j ≡ k) *iso  *iso  (cong (*) (trans (sym x=ba') x=ba))))))  
                                           (sym (proj1 (prod-≡ (subst₂ (λ j k → j ≡ k) *iso  *iso  (cong (*) (trans (sym x=ba') x=ba)))))) 

ZPmirror-neg : {A B C D : HOD}  → {cdab : (C ＼ D) ⊆ ZFP A B } {cab : C  ⊆ ZFP A B } {dab : D  ⊆ ZFP A B } 
        → ZPmirror A B (C ＼ D) cdab ≡ ZPmirror A B C cab ＼ ZPmirror A B D dab
ZPmirror-neg {A} {B} {C} {D} {cdab} {cab} {dab} = ==→o≡ record { eq→ = za08 ; eq← = za10 } where
        za08 : {x : Ordinal} → ZPC A B (C ＼ D) cdab x → odef (ZPmirror A B C cab ＼ ZPmirror A B D dab) x
        za08 {x} record { a = a ; b = b ; aa = aa ; bb = bb ; c∋ab = c∋ab ; x=ba = x=ba } = 
             ⟪ record { a = a ; b = b ; aa = aa ; bb = bb ; c∋ab = proj1 c∋ab ; x=ba = x=ba }  , za09 ⟫ where
            za09 : ¬ odef (ZPmirror A B D dab) x
            za09 zd = ⊥-elim ( proj2 c∋ab (subst (λ k → odef D k) (sym zs02) (ZPC.c∋ab zd) ) ) where
                x=ba' = ZPC.x=ba zd
                zs02 : & < * a , * b > ≡ & < * (ZPC.a zd) , * (ZPC.b zd) >
                zs02 = cong₂ (λ j k → & < j , k >) (sym (proj2 (prod-≡ (subst₂ (λ j k → j ≡ k) *iso  *iso  (cong (*) (trans (sym x=ba' ) x=ba))))))  
                                           (sym (proj1 (prod-≡ (subst₂ (λ j k → j ≡ k) *iso  *iso  (cong (*) (trans (sym x=ba' ) x=ba)))))) 
        za10 : {x : Ordinal} → odef (ZPmirror A B C cab ＼ ZPmirror A B D dab) x → ZPC A B (C ＼ D) cdab x 
        za10 {x} ⟪ record { a = a ; b = b ; aa = aa ; bb = bb ; c∋ab = c∋ab ; x=ba = x=ba } , neg ⟫ = 
                   record { a = a ; b = b ; aa = aa ; bb = bb ; c∋ab = ⟪ c∋ab , za11 ⟫ ; x=ba = x=ba } where
            za11 : ¬ odef D (& < * a , * b >)
            za11 zd = ⊥-elim (neg record { a = a ; b = b ; aa = aa ; bb = bb ; c∋ab = zd ; x=ba = x=ba }) 


ZPmirror-whole : {A B : HOD}  → ZPmirror A B (ZFP A B) (λ x → x) ≡ ZFP B A
ZPmirror-whole {A} {B} = ==→o≡ record { eq→ = za12 ; eq← = za13 } where
        za12 : {x : Ordinal} → ZPC A B (ZFP A B) (λ x₁ → x₁) x → ZFProduct B A x
        za12 {x} record { a = a ; b = b ; aa = aa ; bb = bb ; c∋ab = c∋ab ; x=ba = x=ba } = subst (λ k → ZFProduct B A k) (sym x=ba) (ab-pair bb aa)
        za13 : {x : Ordinal} → ZFProduct B A x → ZPC A B (ZFP A B) (λ x₁ → x₁) x
        za13 {x} (ab-pair {b} {a} bb aa) = record { a = a ; b = b ; aa = aa ; bb = bb ; c∋ab = ab-pair aa bb ; x=ba = refl }

ZPmirror-0 : {A B : HOD} {z : Ordinal } → {zab : * z ⊆ ZFP A B} → ZPmirror A B (* z) zab ≡ od∅ → z ≡ & od∅
ZPmirror-0 {A} {B} {z} {zab} eq = uf10 where
         uf10 : z ≡ & od∅
         uf10 = trans (sym &iso) ( cong (&) (¬x∋y→x≡od∅ (λ {y} zy → uf11 zy ) )) where
             uf11 : {y : Ordinal } → odef (* z) y → ⊥ 
             uf11 {y} zy = ⊥-elim ( ¬x<0 (subst (λ k → odef k (& < * (zπ2 pqy) , * (zπ1 pqy) >) ) eq uf12  ) ) where
                pqy : odef (ZFP A B) y
                pqy = zab zy
                uf14 : odef (* z) (& < * (zπ1 pqy) , * (zπ2 pqy) >)
                uf14 = subst (λ k → odef (* z) k ) (sym ( zp-iso pqy)) zy
                uf12 : odef (ZPmirror A B  (* z) zab) (& < * (zπ2 pqy) , * (zπ1 pqy) > )
                uf12 = record { a = _ ; b = _ ; aa = zp1 pqy ; bb = zp2 pqy ; c∋ab = uf14 ; x=ba = refl }

ZFP∩  : {A B C : HOD} → ( ZFP (A ∩ B) C ≡ ZFP A C ∩ ZFP B C ) ∧ ( ZFP C (A ∩ B) ≡ ZFP C A  ∩ ZFP C B )
proj1 (ZFP∩ {A} {B} {C} ) = ==→o≡ record { eq→ = zfp00  ; eq← = zfp01 } where
   zfp00 : {x : Ordinal} → ZFProduct (A ∩ B) C x → odef (ZFP A C ∩ ZFP B C) x
   zfp00  (ab-pair ⟪ pa , pb ⟫ qx) = ⟪ ab-pair pa qx  , ab-pair pb qx  ⟫
   zfp01 : {x : Ordinal} → odef (ZFP A C ∩ ZFP B C) x → ZFProduct (A ∩ B) C x
   zfp01 {x} ⟪ p , q ⟫  = subst (λ k → ZFProduct (A ∩ B) C k) zfp07 ( ab-pair (zfp02 ⟪ p , q ⟫ ) (zfp04 q) ) where
       zfp05 : & < * (zπ1 p) , * (zπ2 p) > ≡ x
       zfp05 = zp-iso p
       zfp06 : & < * (zπ1 q) , * (zπ2 q) > ≡ x
       zfp06 = zp-iso q
       zfp07 : & < * (zπ1 p) , * (zπ2 q) > ≡ x
       zfp07 = trans (cong (λ k → & < k , * (zπ2 q)  >  )
           (proj1 (prod-≡ (subst₂ _≡_  *iso *iso (cong (*) (trans  zfp05 (sym (zfp06)))))))) zfp06
       zfp02 : {x  : Ordinal  } → (acx : odef (ZFP A C ∩ ZFP B C) x)   → odef (A ∩ B) (zπ1 (proj1 acx))
       zfp02 {.(& < * _ , * _ >)} ⟪ ab-pair {a} {b} ax bx , bcx ⟫ = ⟪ ax , zfp03 bcx refl ⟫ where
           zfp03 : {x : Ordinal } →  (bc : odef (ZFP B C) x) → x ≡ (& < * a , * b >)  → odef B (zπ1 (ab-pair {A} {C} ax bx))
           zfp03 (ab-pair {a1} {b1} x x₁) eq = subst (λ k → odef B k ) zfp08 x  where
              zfp08 : a1 ≡ a
              zfp08 = subst₂ _≡_ &iso &iso (cong (&) (proj1 (prod-≡ (subst₂  _≡_  *iso *iso (cong (*) eq)))))
       zfp04 : {x : Ordinal } (acx : odef (ZFP B C) x )→ odef C (zπ2 acx)
       zfp04 (ab-pair x x₁) = x₁
proj2 (ZFP∩ {A} {B} {C} ) = ==→o≡ record { eq→ = zfp00 ; eq← = zfp01  } where
   zfp00 : {x : Ordinal} → ZFProduct C (A ∩ B) x → odef (ZFP C A ∩ ZFP C B) x
   zfp00  (ab-pair qx ⟪ pa , pb ⟫ ) = ⟪ ab-pair qx pa  , ab-pair qx pb   ⟫
   zfp01 : {x : Ordinal} → odef (ZFP C A ∩ ZFP C B ) x → ZFProduct C (A ∩ B)  x
   zfp01 {x} ⟪ p , q ⟫  = subst (λ k → ZFProduct C (A ∩ B)  k) zfp07 ( ab-pair (zfp04 p) (zfp02 ⟪ p , q ⟫ )  ) where
       zfp05 : & < * (zπ1 p) , * (zπ2 p) > ≡ x
       zfp05 = zp-iso p
       zfp06 : & < * (zπ1 q) , * (zπ2 q) > ≡ x
       zfp06 = zp-iso q
       zfp07 : & < * (zπ1 p) , * (zπ2 q) > ≡ x
       zfp07 = trans (cong (λ k → & < * (zπ1 p) , k  >  )
           (sym (proj2 (prod-≡ (subst₂ _≡_  *iso *iso (cong (*) (trans  zfp05 (sym (zfp06))))))))) zfp05
       zfp02 : {x  : Ordinal  } → (acx : odef (ZFP C A ∩ ZFP C B ) x)   → odef (A ∩ B) (zπ2 (proj2 acx))
       zfp02 {.(& < * _ , * _ >)} ⟪ bcx , ab-pair {b} {a} ax bx  ⟫ = ⟪ zfp03 bcx refl , bx ⟫ where
           zfp03 : {x : Ordinal } →  (bc : odef (ZFP C A ) x) → x ≡ (& < * b , * a >)  → odef A (zπ2 (ab-pair {C} {B} ax bx ))
           zfp03 (ab-pair {b1} {a1} x x₁) eq = subst (λ k → odef A k ) zfp08 x₁ where
              zfp08 : a1 ≡ a
              zfp08 = subst₂ _≡_ &iso &iso (cong (&) (proj2 (prod-≡ (subst₂  _≡_  *iso *iso (cong (*) eq)))))
       zfp04 : {x : Ordinal } (acx : odef (ZFP C A ) x )→ odef C (zπ1 acx)
       zfp04 (ab-pair x x₁) = x

open import BAlgebra O

ZFP\Q : {P Q p : HOD} → (( ZFP P Q ＼ ZFP p Q ) ≡ ZFP (P ＼ p) Q ) ∧ (( ZFP P Q ＼ ZFP P p ) ≡ ZFP P (Q ＼ p) )
ZFP\Q {P} {Q} {p} = ⟪ ==→o≡ record { eq→ = ty70 ; eq← = ty71 } , ==→o≡ record { eq→ = ty73 ; eq← = ty75 } ⟫ where
    ty70 : {x : Ordinal } → odef ( ZFP P Q ＼ ZFP p Q ) x →  odef (ZFP (P ＼ p) Q) x
    ty70 ⟪ ab-pair {a} {b} Pa pb  , npq ⟫ = ab-pair ty72 pb  where
       ty72 : odef (P ＼ p ) a
       ty72 = ⟪ Pa , (λ pa → npq (ab-pair pa pb ) ) ⟫
    ty71 : {x : Ordinal } → odef (ZFP (P ＼ p) Q) x → odef ( ZFP P Q ＼ ZFP p Q ) x
    ty71 (ab-pair {a} {b} ⟪ Pa , npa ⟫ Qb) = ⟪ ab-pair Pa Qb
        , (λ pab → npa (subst (λ k → odef p k) (proj1 (zp-iso0 pab)) (zp1 pab)) ) ⟫
    ty73 : {x : Ordinal } → odef ( ZFP P Q ＼ ZFP P p ) x →  odef (ZFP P (Q ＼ p) ) x
    ty73 ⟪ ab-pair {a} {b} pa Qb  , npq ⟫ = ab-pair pa ty72  where
       ty72 : odef (Q ＼ p ) b
       ty72 = ⟪ Qb , (λ qb → npq (ab-pair pa qb ) ) ⟫
    ty75 : {x : Ordinal } → odef (ZFP P (Q ＼ p) ) x → odef ( ZFP P Q ＼ ZFP P p ) x
    ty75 (ab-pair {a} {b} Pa ⟪ Qb , nqb ⟫ ) = ⟪ ab-pair Pa Qb
        , (λ pab → nqb (subst (λ k → odef p k) (proj2 (zp-iso0 pab)) (zp2 pab)) ) ⟫





