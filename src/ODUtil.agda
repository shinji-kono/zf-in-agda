{-# OPTIONS --cubical-compatible --safe #-}
open import Level
open import Ordinals
import HODBase
import OD
module ODUtil {n : Level } (O : Ordinals {n} ) (HODAxiom : HODBase.ODAxiom O) (ho< : OD.ODAxiom-ho< O HODAxiom ) where

open import Data.Nat renaming ( zero to Zero ; suc to Suc ;  ℕ to Nat ; _⊔_ to _n⊔_ )
open import  Relation.Binary.PropositionalEquality hiding ( [_] )
open import Data.Nat.Properties
open import Data.Empty
open import Data.Unit
open import Relation.Nullary
open import Relation.Binary  hiding (_⇔_)
open import Relation.Binary.Core hiding (_⇔_)
import Relation.Binary.Reasoning.Setoid as EqR

open import logic
import OrdUtil
open import nat

open Ordinals.Ordinals  O
open Ordinals.IsOrdinals isOrdinal
-- open Ordinals.IsNext isNext
open OrdUtil O

-- Ordinal Definable Set

open HODBase.HOD 
open HODBase.OD 

open _∧_
open _∨_
open Bool

open  HODBase._==_

open HODBase.ODAxiom HODAxiom  
open OD O HODAxiom

_⊂_ : ( A B : HOD) → Set n
_⊂_ A B = ( & A o< & B) ∧ ( A ⊆ B )

⊆∩-dist : {a b c : HOD} → a ⊆ b → a ⊆ c  →  a ⊆ ( b ∩ c )
⊆∩-dist {a} {b} {c} a<b a<c {z} az = ⟪ a<b az , a<c az ⟫

⊆∩-incl-1 : {a b c : HOD} → a ⊆ c → ( a ∩ b ) ⊆ c
⊆∩-incl-1 {a} {b} {c} a<c {z} ab = a<c (proj1 ab)

⊆∩-incl-2 : {a b c : HOD} → a ⊆ c → ( b ∩ a ) ⊆ c
⊆∩-incl-2 {a} {b} {c} a<c {z} ab = a<c (proj2 ab)

*iso∩ : {p q : HOD} →  (p ∩ q) =h= (* (& p) ∩ * (& q))
eq→ (*iso∩ {p} {q}) {x} ⟪ px , qx ⟫ = ⟪ eq← *iso px , eq← *iso qx ⟫
eq← (*iso∩ {p} {q}) {x} ⟪ px , qx ⟫ = ⟪ eq→ *iso px , eq→ *iso qx ⟫

∩-cong : {A B C D : HOD} → A =h= B → C =h= D → (A ∩ C) =h= (B ∩ D)
eq→ (∩-cong eq1 eq2) {x} lt = ⟪ eq→ eq1 (proj1 lt) , eq→ eq2 (proj2 lt) ⟫
eq← (∩-cong eq1 eq2) {x} lt = ⟪ eq← eq1 (proj1 lt) , eq← eq2 (proj2 lt) ⟫

power→⊆ :  ( A t : HOD) → Power A ∋ t → t ⊆ A
power→⊆ A t  PA∋t t∋x = subst (λ k → odef A k ) &iso ( t1 (subst (λ k → odef t k ) (sym &iso) t∋x))  where
   t1 : {x : HOD }  → t ∋ x → A ∋ x
   t1 = power→ A t PA∋t

power-∩ : { A x y : HOD } → Power A ∋ x → Power A ∋ y → Power A ∋ ( x ∩ y )
power-∩ {A} {x} {y} ax ay = power← A (x ∩ y) p01  where
   p01 :  {z : HOD} → (x ∩ y) ∋ z → A ∋ z
   p01 {z} xyz = power→ A x ax (proj1 xyz )

odef-not : {S : HOD} {x : Ordinal } →  ¬ ( odef S x ) → odef S x → ⊥
odef-not neg sx = ⊥-elim ( neg sx )

-- HOD may defined by record { x=some-hod : & some-hod ≡ x }, some-hod ⊆ H we need to prove x o< osuc (& H)
--
record-hod : {h H : HOD} {x : Ordinal} → & h ≡ x → h ⊆ H  → x o< osuc (& H)
record-hod {h} eq h⊆H = subst₂ (λ j k → j o< k ) eq refl ( ⊆→o≤ h⊆H )

record-hod1 : {h H : HOD} {x : Ordinal} → & h ≡ x → odef H (& h)  → x o< (& H)
record-hod1 {h} eq H∋h = subst₂ (λ j k → j o< k ) eq refl ( c<→o< H∋h )


cseq :  HOD  →  HOD
cseq x = record { od = record { def = λ y → odef x (osuc y) } ; odmax = osuc (odmax x) ; <odmax = lemma } where
    lemma : {y : Ordinal} → def (od x) (osuc y) → y o< osuc (odmax x)
    lemma {y} lt = ordtrans <-osuc (ordtrans (<odmax x lt) <-osuc )

∩-comm : { A B : HOD } → (A ∩ B) =h= (B ∩ A)
∩-comm {A} {B} = record { eq← = λ {x} lt → ⟪ proj2 lt , proj1 lt ⟫ ; eq→ =  λ {x} lt → ⟪ proj2 lt , proj1 lt ⟫ }

_∪_ : ( A B : HOD  ) → HOD
A ∪ B = record { od = record { def = λ x → odef A x ∨ odef B x } ;
    odmax = omax (odmax A) (odmax B) ; <odmax = lemma } where
      lemma :  {y : Ordinal} → odef A y ∨ odef B y → y o< omax (odmax A) (odmax B)
      lemma {y} (case1 a) = ordtrans (<odmax A a) (omax-x _ _)
      lemma {y} (case2 b) = ordtrans (<odmax B b) (omax-y _ _)

∪-cong : {A B C D : HOD} → A =h= B → C =h= D → (A ∪ C) =h= (B ∪ D)
eq→ (∪-cong {A} {B} {C} {D} eq1 eq2) {x} (case1 lt) = case1 (eq→ eq1 lt)
eq→ (∪-cong {A} {B} {C} {D} eq1 eq2) {x} (case2 lt) = case2 (eq→ eq2 lt)
eq← (∪-cong {A} {B} {C} {D} eq1 eq2) {x} (case1 lt) = case1 (eq← eq1 lt)
eq← (∪-cong {A} {B} {C} {D} eq1 eq2) {x} (case2 lt) = case2 (eq← eq2 lt)

x∪x≡x : { A  : HOD  } → (A ∪ A) =h= A 
x∪x≡x {A} = record { eq← = λ {x} lt → case1 lt ; eq→ =  lem00 } where
    lem00 : {x : Ordinal} → odef A x ∨ odef A x → odef A x
    lem00 {x} (case1 ax) = ax
    lem00 {x} (case2 ax) = ax

_＼_ : ( A B : HOD  ) → HOD
A ＼ B = record { od = record { def = λ x → odef A x ∧ ( ¬ ( odef B x ) ) }; odmax = odmax A ; <odmax = λ y → <odmax A (proj1 y) }

¬∅∋ : {x : HOD} → ¬ ( od∅ ∋ x )
¬∅∋ {x} = ¬x<0


pair-xx<xy : {x y : HOD} → & (x , x) o< osuc (& (x , y) )
pair-xx<xy {x} {y} = ⊆→o≤  lemma where
   lemma : {z : Ordinal} → def (od (x , x)) z → def (od (x , y)) z
   lemma {z} (case1 refl) = case1 refl
   lemma {z} (case2 refl) = case1 refl

trans-⊆ :  { A B C : HOD} → A ⊆ B → B ⊆ C → A ⊆ C
trans-⊆ A⊆B B⊆C ab = B⊆C (A⊆B ab)

trans-⊂ :  { A B C : HOD} → A ⊂ B → B ⊂ C → A ⊂ C
trans-⊂ ⟪ A<B , A⊆B ⟫ ⟪ B<C , B⊆C ⟫ = ⟪ ordtrans A<B B<C , (λ ab → B⊆C (A⊆B ab)) ⟫

refl-⊆ : {A : HOD} → A ⊆ A
refl-⊆ x = x

od⊆→o≤  : {x y : HOD } → x ⊆ y → & x o< osuc (& y)
od⊆→o≤ {x} {y} lt  =  ⊆→o≤ {x} {y} (λ {z} x>z  → subst (λ k → def (od y) k ) &iso (lt (d→∋ x x>z)))

⊆→= : {F U : HOD} → F ⊆ U  → U ⊆ F → F =h= U
⊆→= {F} {U} FU UF = record { eq→ = λ {x} lt → subst (λ k → odef U k) &iso (FU (subst (λ k → odef F k) (sym &iso) lt) )
                                     ; eq← = λ {x} lt → subst (λ k → odef F k) &iso (UF (subst (λ k → odef U k) (sym &iso) lt) ) }

¬A∋x→A≡od∅ : (A : HOD) → {x : HOD} → A ∋ x  → ¬ ( & A ≡ o∅ )
¬A∋x→A≡od∅ A {x} ax a=0 = ¬x<0 ( subst (λ k → & x o< k) a=0 (c<→o< ax ))

subset-lemma : {A x : HOD  } → ( {y : HOD } →  x ∋ y → (A ∩ x ) ∋  y ) ⇔  ( x ⊆ A  )
subset-lemma  {A} {x} = record {
      proj1 = λ lt x∋z → subst (λ k → odef A k ) &iso ( proj1 (lt (subst (λ k →  odef x k) (sym &iso) x∋z ) ))
    ; proj2 = λ x⊆A lt → ⟪ x⊆A lt , lt ⟫
   }

nat→ω : Nat → HOD
nat→ω Zero = od∅
nat→ω (Suc y) = Union (nat→ω y , (nat→ω y , nat→ω y))

ω→nato : {y : Ordinal} → Omega-d y → Nat
ω→nato iφ = Zero
ω→nato (isuc lt) = Suc (ω→nato lt)

ω→nat : (n : HOD) → Omega ho< ∋ n → Nat
ω→nat n = ω→nato

ω∋nat→ω : {n : Nat} → def (od (Omega ho<)) (& (nat→ω n))
ω∋nat→ω {Zero} = subst (λ k → def (od (Omega ho<)) k) (sym ord-od∅) iφ
ω∋nat→ω {Suc n} =  subst (λ k → Omega-d k) (sym (==→o≡ nat01)) nat00 where
   nat00 : Omega-d (& (Union (* (& (nat→ω n)) , (* (& (nat→ω n)) , * (& (nat→ω n))))))
   nat00 = isuc ( ω∋nat→ω {n})
   nat01 : Union (nat→ω n , ( nat→ω n , nat→ω n)) =h= Union (* (& (nat→ω n)) , (* (& (nat→ω n)) , * (& (nat→ω n))))
   nat01 = ==-sym Omega-iso 

pair1 : { x y  : HOD  } →  (x , y ) ∋ x
pair1 = case1 refl

pair2 : { x y  : HOD  } →  (x , y ) ∋ y
pair2 = case2 refl

single : {x y : HOD } → (x , x ) ∋ y → x =h= y
single (case1 eq) = ord→== (sym eq) 
single (case2 eq) = ord→== (sym eq) 

single& : {x y : Ordinal } → odef (* x , * x ) y → x ≡ y
single& (case1 eq) = sym (trans eq &iso)
single& (case2 eq) = sym (trans eq &iso)

pair=∨ : {a b c : Ordinal  } → odef (* a , * b) c → (  a ≡ c ) ∨  (  b ≡ c )
pair=∨ {a} {b} {c} (case1 c=a) = case1 ( sym (trans c=a &iso))
pair=∨ {a} {b} {c} (case2 c=b) = case2 ( sym (trans c=b &iso))

ω-prev-eq1 : {x y : Ordinal} →  & (Union (* y , (* y , * y))) ≡ & (Union (* x , (* x , * x))) → ¬ (x o< y)
ω-prev-eq1 {x} {y} eq x<y with  eq→ (ord→== eq) record { owner = & (* y , * y) ; ao = case2 refl
        ; ox = eq→ (==-sym *iso) (case1 refl) }   --  (* x , (* x , * x)) ∋ * y
... | record { owner = u ; ao = xxx∋u ; ox = uy } with xxx∋u
... | case1 u=x = ⊥-elim ( o<> x<y (osucprev (begin
     osuc y ≡⟨ sym (cong osuc  &iso) ⟩ 
     osuc (& (* y)) ≤⟨ osucc (c<→o< {* y} {* u} uy) ⟩ -- * x ≡ * u ∋ * y
     & (* u) ≡⟨ &iso ⟩
     u ≡⟨ u=x ⟩
     & (* x) ≡⟨ &iso ⟩
     x ∎ ))) 
      where 
         open o≤-Reasoning 
... | case2 u=xx = ⊥-elim (o<¬≡ ( begin
        x ≡⟨ single& ( eq← (==-sym *iso)  (subst₂ (λ j k → odef j k ) (cong (*) u=xx ) &iso uy)) ⟩
        y ∎ ) x<y)  where open ≡-Reasoning 

Omega-inject : {x y : Ordinal} →  & (Union (* y , (* y , * y))) ≡ & (Union (* x , (* x , * x))) → y ≡ x
Omega-inject {x} {y} eq with trio< x y
Omega-inject {x} {y} eq | tri< a ¬b ¬c = ⊥-elim (ω-prev-eq1 eq a)
Omega-inject {x} {y} eq | tri≈ ¬a b ¬c = (sym b)
Omega-inject {x} {y} eq | tri> ¬a ¬b c = ⊥-elim (ω-prev-eq1 (sym eq) c)

ω-inject : {x y : HOD} →  Union ( y , ( y ,  y)) =h= Union ( x , ( x ,  x)) → y =h= x
ω-inject {x} {y} eq = ord→== ( Omega-inject (==→o≡ (==-trans Omega-iso (==-trans eq (==-sym Omega-iso)))))

ω-∈s : (x : HOD) →  Union ( x , (x , x)) ∋ x
ω-∈s x = record { owner = & ( x , x ) ; ao = case2 refl  ; ox = eq→ (==-sym *iso) (case2 refl) }

ωs≠0 : (x : HOD) →  ¬ ( Union ( x , (x , x)) =h= od∅ )
ωs≠0 x =  ∅< {Union ( x , ( x ,  x))} (ω-∈s  _)

ω→nato-cong : {n m : Ordinal} → (x : odef (Omega ho< ) n) (y : odef (Omega ho< ) m) → n ≡ m → ω→nato x ≡ ω→nato y
ω→nato-cong OD.iφ OD.iφ eq = refl
ω→nato-cong OD.iφ (OD.isuc {x} y) eq = ⊥-elim ( ∅< {Union (* x , (* x , * x))} {* x} (ω-∈s _) (≡o∅→=od∅ (sym eq)   ) )
ω→nato-cong (OD.isuc {x} y) OD.iφ eq = ⊥-elim ( ∅< {Union (* x , (* x , * x))} {* x} (ω-∈s _) (≡o∅→=od∅ eq   ) )
ω→nato-cong (OD.isuc x) (OD.isuc y) eq = cong Suc ( ω→nato-cong x y (Omega-inject eq) )

ωs0 : o∅ ≡ & (nat→ω 0)
ωs0 = trans (sym ord-od∅) (cong (&) refl ) 

Omega-subst : (x y : HOD) → x =h= y  →  Union ( x , (x , x)) =h= Union ( y , (y , y)) 
Omega-subst x y x=y = begin
    Union (x , (x , x)) ≈⟨ ==-sym Omega-iso ⟩ 
    Union (* (& x) , (* (& x) , * (& x))) ≈⟨ ord→== (cong (λ k → & (Union (* k , (* k , * k )))) (==→o≡ x=y) )  ⟩ 
    Union (* (& y) , (* (& y) , * (& y))) ≈⟨ Omega-iso ⟩ 
    Union (y , (y , y)) ∎ where open EqR ==-Setoid                       

nat→ω-iso : {i : HOD} → (lt : Omega ho< ∋ i ) → nat→ω ( ω→nat i lt ) =h= i
nat→ω-iso {i} lt = ==-trans (nat→ω-iso-ord _ lt) *iso where
    nat→ω-iso-ord : (x : Ordinal) → (lt : odef (Omega ho< ) x) → nat→ω ( ω→nato lt ) =h= (* x)
    nat→ω-iso-ord _ OD.iφ = ==-sym o∅==od∅
    nat→ω-iso-ord x (OD.isuc OD.iφ) = ==-trans (Omega-subst _ _ (==-sym o∅==od∅)) (==-sym *iso)
    nat→ω-iso-ord x (OD.isuc (OD.isuc {y} lt)) = ==-trans (Omega-subst _ _ 
      (==-trans (Omega-subst _ _ lem02 ) (==-sym *iso)))  (==-sym *iso)  where
      lem02  : nat→ω ( ω→nato lt ) =h= (* y)
      lem02  = nat→ω-iso-ord y lt

ω→nat-iso0 : (x : Nat) → {ox : Ordinal } → (ltd : Omega-d ox) → * ox =h= nat→ω x → ω→nato ltd ≡ x
ω→nat-iso0 Zero iφ eq = refl
ω→nat-iso0 (Suc x) iφ eq = ⊥-elim ( ωs≠0 _ (begin
    Union (nat→ω x , (nat→ω x , nat→ω x)) ≈⟨ ==-sym eq ⟩
    * o∅ ≈⟨ o∅==od∅  ⟩
    od∅ ∎ )) where open EqR ==-Setoid
ω→nat-iso0 Zero (isuc ltd) eq = ⊥-elim ( ωs≠0 _ (==-trans (==-sym *iso) eq) )
ω→nat-iso0 (Suc i) (isuc {x} ltd) eq = cong Suc ( ω→nat-iso0 i ltd (lemma1 eq) ) where
       lemma1 :  * (& (Union (* x , (* x , * x)))) =h= Union (nat→ω i , (nat→ω i , nat→ω i)) → * x =h= nat→ω i
       lemma1 eq = begin
          * x  ≈⟨ (o≡→== ( Omega-inject  (==→o≡ (begin
             Union (* x , (* x , * x)) ≈⟨ ==-sym  *iso ⟩
             * (& ( Union (* x , (* x , * x)))) ≈⟨  eq ⟩
             Union ((nat→ω i) , (nat→ω i , nat→ω i)) ≈⟨ ==-sym Omega-iso ⟩
             Union (* (& (nat→ω i)) , (* (& (nat→ω i)) , * (& (nat→ω i)))) ∎ )) ))  ⟩
          * (& ( nat→ω i))  ≈⟨ *iso ⟩
          nat→ω i ∎  where open EqR ==-Setoid

ω→nat-iso : {i : Nat} → ω→nat ( nat→ω i ) (ω∋nat→ω {i}) ≡ i
ω→nat-iso {i} = ω→nat-iso0 i (ω∋nat→ω {i}) *iso

nat→ω-inject : {i j : Nat} → nat→ω i =h=  nat→ω j → i ≡ j
nat→ω-inject {Zero} {Zero} eq = refl
nat→ω-inject {Zero} {Suc j} eq = ⊥-elim ( ∅< {Union (nat→ω j , (nat→ω j , nat→ω j))} (ω-∈s  _) (==-sym eq) )
nat→ω-inject {Suc i} {Zero} eq = ⊥-elim ( ∅< {Union (nat→ω i , (nat→ω i , nat→ω i))} (ω-∈s  _) eq )
nat→ω-inject {Suc i} {Suc j} eq = cong Suc (nat→ω-inject {i} {j} ( ω-inject eq ))

Repl⊆ : {A B : HOD} (A⊆B : A ⊆ B) → { ψa : ( x : HOD) → A ∋ x → HOD } { ψb : ( x : HOD) → B ∋ x → HOD }
   →  {Ca : HOD} → {rca : RXCod A Ca ψa }
   →  {Cb : HOD} → {rcb : RXCod B Cb ψb }
   → ( {z : Ordinal  } → (az : odef A z ) →  (ψa (* z) (subst (odef A) (sym &iso) az) ≡ ψb (* z) (subst (odef B) (sym &iso) (A⊆B az))))
   → Replace' A ψa rca ⊆ Replace' B ψb rcb
Repl⊆ {A} {B} A⊆B {ψa} {ψb} eq  record { z = z ; az = az ; x=ψz = x=ψz } = record { z = z ; az = A⊆B az
         ; x=ψz = trans  x=ψz (cong (&) (eq az) ) }

PPP : {P : HOD} → Power P ∋ P
PPP {P} z pz = eq← (==-sym *iso) pz

UPower⊆Q : {P Q : HOD} → P ⊆ Q → Union (Power P) ⊆ Q
UPower⊆Q {P} {Q} P⊆Q {z} record { owner = y ; ao = ppy ; ox = yz } = P⊆Q (ppy _ yz)

UPower∩ : {P  : HOD} → ({ p q : HOD } → P ∋ p →  P ∋ q  → P ∋ (p ∩ q))
    → { p q : HOD } → Union (Power P) ∋ p →  Union (Power P) ∋ q  → Union (Power P) ∋ (p ∩ q)
UPower∩ {P} each {p} {q} record { owner = x ; ao = ppx ; ox = xz } record { owner = y ; ao = ppy ; ox = yz }
   =  record { owner = & P ; ao = PPP ; ox = lem03 }  where
    lem03 :   odef (* (& P)) (& (p ∩ q))
    lem03 = eq→  (==-sym *iso) ( each (ppx _ xz) (ppy _ yz) )

