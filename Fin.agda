module Fin where

open import Data.Fin using (Fin; zero; suc; _≤_; _<_; toℕ)
open import Data.Nat using (ℕ)
open import Data.Fin.Properties as FinProp using (_≟_)
import Data.Nat.Properties as ℕProp
open import Data.Bool using (Bool; true; false)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.Definitions using (Tri)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; sym; trans)
open import Relation.Nullary using (¬_; contradiction)
open import Data.Product.Base using (∃; ∃-syntax; _×_)
open import Function using (_∘_; id)
open import Data.Empty using (⊥; ⊥-elim)
open import Agda.Builtin.Sigma using (Σ; _,_) renaming (fst to proj₁ ; snd to proj₂)

tail : ∀ {n m} → (f : Fin (ℕ.suc n) → Fin m) → Fin n → Fin m
tail f i = f (suc i)

Mono : {n m : ℕ} → (f : Fin n → Fin m) → Set
Mono f = ∀ {i j} → i ≤ j → f i ≤ f j

sMono : {n m : ℕ} → (f : Fin n → Fin m) → Set
sMono f = ∀ {i j} → i < j → f i < f j

Inj : {n m : ℕ} → (f : Fin n → Fin m) → Set
Inj f = ∀ {i j} → f i ≡ f j → i ≡ j

Mono+Inj⇒sMono : {n m : ℕ} → {f : Fin n → Fin m} → Mono f → Inj f → sMono f
Mono+Inj⇒sMono mono inj lt = FinProp.≤∧≢⇒< (mono (ℕProp.<⇒≤ lt)) λ eq → FinProp.<-irrefl (inj eq) lt

sMono⇒Mono : {n m : ℕ} → {f : Fin n → Fin m} → sMono f → Mono f
sMono⇒Mono {n} {m} {f} sMono {i} {j} i≤j with FinProp.<-cmp i j
... | Tri.tri< i<j _ _ = ℕProp.<⇒≤ (sMono i<j)
... | Tri.tri≈ _ i≡j _ = FinProp.≤-reflexive (cong f i≡j)
... | Tri.tri> _ _ j<i = contradiction (ℕProp.≤-<-trans i≤j j<i) (ℕProp.n≮n (toℕ i))

sMono⇒inj : {n m : ℕ} → {f : Fin n → Fin m} → sMono f → Inj f
sMono⇒inj {n} {m} {f} sMono {i} {j} fi≡fj with FinProp.<-cmp i j
... | Tri.tri< i<j _ _ = contradiction (sMono i<j) (FinProp.<-irrefl fi≡fj)
... | Tri.tri≈ _ i≡j _ = i≡j
... | Tri.tri> _ _ j<i = contradiction (sMono j<i) (FinProp.<-irrefl (sym fi≡fj))

tailMono+zero≤⇒Mono : ∀ {n m} → (f : Fin (ℕ.suc n) → Fin m) → Mono (tail f) → (∀ {i} → f zero ≤ f i) → Mono f
tailMono+zero≤⇒Mono f mono zero≤ {zero} _ = zero≤
tailMono+zero≤⇒Mono f mono zero≤ {suc i} {suc j} (Data.Nat.s≤s le) = mono le

Mono⇒tailMono : ∀ {n m} → (f : Fin (ℕ.suc n) → Fin m) → Mono f → Mono (tail f)
Mono⇒tailMono f mono le = mono (Data.Nat.s≤s le)

Mono⇒zero≤ : ∀ {n m} → (f : Fin (ℕ.suc n) → Fin m) → Mono f → (∀ {i} → f zero ≤ f i)
Mono⇒zero≤ f mono = mono Data.Nat.z≤n

Surj : {n m : ℕ} → (f : Fin n → Fin m) → Set
Surj f = ∀ y → ∃[ x ] y ≡ f x

record _→+_ (n m : ℕ) : Set where
  field
    fun : Fin n → Fin m
    mono : Mono fun

record _↪+_ (n m : ℕ) : Set where
  field
    fun : Fin n → Fin m
    smono : sMono fun

record _↠+_ (n m : ℕ) : Set where
  field
    fun : Fin n → Fin m
    mono : Mono fun
    surj : Surj fun

id→+ : (n : ℕ) →  n →+ n
id→+ n = record
  { fun = id
  ; mono = id
  }

_∘→+_ : ∀ {n m k} → m →+ k → n →+ m → n →+ k
_∘→+_ g f = record
  { fun  = _→+_.fun g ∘ _→+_.fun f
  ; mono = λ {i}{j} i≤j → _→+_.mono g (_→+_.mono f i≤j)
  }

{-
-- Inj ⇒ nondup imageList

-- headNotInTail : ∀ {n m} (f : Fin (ℕ.suc n) → Fin m) → Inj f → ¬ f zero ∈ imageList (λ i → f (suc i))

-- prove something like, x ∈ imageList, then y with fy = x...

of∈imageList : ∀ {n m y} → (f : Fin n → Fin m) → y ∈ imageList f → ∃[ i ] y ≡ f i
of∈imageList {ℕ.suc n} {m} {y} f ∈head = zero , refl
of∈imageList {ℕ.suc n} {m} {y} f (∈cons mem) = suc (proj₁ (of∈imageList _ mem)) , proj₂ (of∈imageList _ mem)

of∈?imageList≡trueInd : ∀ {n m y} → (f : Fin n → Fin m) → y ∈? imageList f ≡ true → ∃[ i ] y ≡ f i
of∈?imageList≡trueInd f mem = of∈imageList f (∈?≡true⇒∈ mem) 

Inj⇒¬∈imageList : ∀ {n m} (f : Fin (ℕ.suc n) → Fin m) → Inj f → ¬ f zero ∈ imageList (λ i → f (suc i))
Inj⇒¬∈imageList {n} {m} f inj mem = FinProp.0≢1+n (inj (proj₂ (of∈imageList _ mem)))

Inj⇒nondupImageList : ∀ {n m} → (f : Fin n → Fin m) → Inj f → nondup (imageList f)
Inj⇒nondupImageList {ℕ.zero} {m} f inj = nd-[]
Inj⇒nondupImageList {ℕ.suc n} {m} f inj = nd-∷ (¬∈⇒∈?≡false (Inj⇒¬∈imageList _ inj))
(Inj⇒nondupImageList _ (λ eq →  FinProp.suc-injective (inj eq)))
-}

infix 5 _∈''_

data _∈''_ : ∀ {n m} → (x : Fin m) → (f : Fin n → Fin m) → Set where
  ∈''-zero : ∀ {n m} → (f : Fin (ℕ.suc n) → Fin m) → f zero ∈'' f
  ∈''-tail : ∀ {n m} → (x : Fin m) → (f : Fin (ℕ.suc n) → Fin m) → x ∈'' tail f → x ∈'' f

app∈'' : ∀ {n m} → (x : Fin n) → (f : Fin n → Fin m) → f x ∈'' f
app∈'' {ℕ.suc n} zero f = ∈''-zero f
app∈'' {ℕ.suc n} (suc x) f = ∈''-tail _ _ (app∈'' _ _)

≡app∈'' : ∀ {n m x y} → (f : Fin n → Fin m) → y ≡ f x → y ∈'' f
≡app∈'' _ refl = app∈'' _ _

∈''⇒app∈'' : ∀ {n m k x} → (f : Fin n → Fin m) → (g : Fin m → Fin k) → x ∈'' f → g x ∈'' g ∘ f
∈''⇒app∈'' f g (∈''-zero f) = ∈''-zero _
∈''⇒app∈'' f g (∈''-tail x f mem) = ∈''-tail _ _ (∈''⇒app∈'' _ _ mem)

Dec∈''⇒Dec≡⇒Dec∈'' : ∀ {n m} → {x : Fin m} → {f : Fin (ℕ.suc n) → Fin m} → Dec (x ∈'' tail f) → Dec (x ≡ f zero) → Dec (x ∈'' f)
Dec∈''⇒Dec≡⇒Dec∈'' {n} {m} {x} {f} (yes p) _ = yes (∈''-tail _ _ p)
Dec∈''⇒Dec≡⇒Dec∈'' {n} {m} {x} {f} _ (yes refl) = yes (∈''-zero _)
Dec∈''⇒Dec≡⇒Dec∈'' {n} {m} {x} {f} (no np) (no nq) = no aux where
  aux : ¬ x ∈'' f
  aux (∈''-zero f) = nq refl
  aux (∈''-tail x f mem) = np mem

_∈''?_ : ∀ {n m} → (x : Fin m) → (f : Fin n → Fin m) → Dec (x ∈'' f)
_∈''?_ {ℕ.zero} x f = no λ()
_∈''?_ {ℕ.suc n} x f = Dec∈''⇒Dec≡⇒Dec∈'' (x ∈''? tail f) (x ≟ f zero)

∈''⇒i : ∀ {n m} → {x : Fin m} → {f : Fin n → Fin m} → x ∈'' f → Fin n
∈''⇒i {ℕ.suc n} {m} {x} {f} (∈''-zero f) = zero
∈''⇒i {ℕ.suc n} {m} {x} {f} (∈''-tail x f mem) = suc (∈''⇒i mem)

∈''⇒i≡ : ∀ {n m} → {x : Fin m} → {f : Fin n → Fin m} → (mem : x ∈'' f) → x ≡ f (∈''⇒i mem)
∈''⇒i≡ {ℕ.suc n} {m} {x} {f} (∈''-zero f) = refl
∈''⇒i≡ {ℕ.suc n} {m} {x} {f} (∈''-tail x f mem) = ∈''⇒i≡ mem

∀∈''⇒Surj : ∀ {n m} → (f : Fin n → Fin m) → (∀ {x} → x ∈'' f) → Surj f
∀∈''⇒Surj f p x = _ , ∈''⇒i≡ p

factorInd : ∀ {n m} → (f : Fin n → Fin m) → ℕ
factorInd {ℕ.zero} f = ℕ.zero
factorInd {ℕ.suc n} f with f zero ∈''? tail f
... | yes _ = factorInd (tail f)
... | no _ = ℕ.suc (factorInd (tail f))

factorL : ∀ {n m} → (f : Fin n → Fin m) →  Fin n → Fin (factorInd f)
updateLYes : ∀{n m} → (f : Fin (ℕ.suc n) → Fin (ℕ.suc m)) → (p : f zero ∈'' tail f) → Fin (ℕ.suc n) → Fin (factorInd (tail f))
updateLNo : ∀ {n m} → (f : Fin (ℕ.suc n) → Fin (ℕ.suc m)) → Fin (ℕ.suc n) → Fin (ℕ.suc (factorInd (tail f)))

factorL {ℕ.zero} f ()
factorL {ℕ.suc n} {ℕ.zero} f = ⊥-elim (FinProp.¬Fin0 (f zero)) 
factorL {ℕ.suc n} {ℕ.suc m} f x with f zero ∈''? tail f
...                              | yes mem = updateLYes f mem x
...                              | no _ = updateLNo f x

updateLYes f mem zero = factorL (tail f) (∈''⇒i mem)
updateLYes f mem (suc x) = factorL (tail f) x

updateLNo f zero = zero
updateLNo f (suc x) = suc (factorL (tail f) x)

factorR : ∀ {n m} → (f : Fin n → Fin m) →  Fin (factorInd f) → Fin m
updateR : ∀ {n m} → (f : Fin (ℕ.suc n) → Fin m) → Fin (ℕ.suc (factorInd (tail f))) → Fin m

factorR {ℕ.zero} f ()
factorR {ℕ.suc n} f x with f zero ∈''? tail f
...                   | yes _ = factorR (tail f) x
...                   | no _ = updateR f x

updateR f zero = f zero
updateR f (suc x) = factorR (tail f) x

factorRfactorL≡ : ∀ {n m} → (f : Fin n → Fin m) → (x : Fin n) → factorR f ((factorL f) x) ≡ f x
factorRfactorL≡ {ℕ.suc n} {ℕ.zero} f x = ⊥-elim (FinProp.¬Fin0 (f zero))
factorRfactorL≡ {ℕ.suc n} {ℕ.suc m} f x with f zero ∈''? tail f
factorRfactorL≡ {ℕ.suc n} {ℕ.suc m} f zero | yes p = trans (factorRfactorL≡ (tail f) (∈''⇒i p)) (sym (∈''⇒i≡ p)) 
factorRfactorL≡ {ℕ.suc n} {ℕ.suc m} f (suc x) | yes p = factorRfactorL≡ (tail f) x
factorRfactorL≡ {ℕ.suc n} {ℕ.suc m} f zero | no p = refl
factorRfactorL≡ {ℕ.suc n} {ℕ.suc m} f (suc x) | no p = factorRfactorL≡ (tail f) x

-- This proof needs to do recursion on factorR and updateR at the same time..
-- So I split out updateR instead of nesting it inside factorR.
∈''factorR⇒∈'' : ∀ {n m x} → (f : Fin n → Fin m) → x ∈'' factorR f → x ∈'' f
∈''updateR⇒∈'' : ∀ {n m x} → (f : Fin (ℕ.suc n) → Fin m) → x ∈'' updateR f → x ∈'' f

∈''factorR⇒∈'' {ℕ.suc n} {m} {x} f mem with f zero ∈''? tail f
∈''factorR⇒∈'' {ℕ.suc n} {m} f mem | yes p = ∈''-tail _ f (∈''factorR⇒∈'' (tail f) mem)
∈''factorR⇒∈'' {ℕ.suc n} {m} {x} f mem | no p = ∈''updateR⇒∈'' _ mem

∈''updateR⇒∈'' f (∈''-zero _) = ∈''-zero _
∈''updateR⇒∈'' f (∈''-tail x _ mem) = ∈''-tail _ _ (∈''factorR⇒∈'' _ mem)

∈''⇒∈''factorR : ∀ {n m x} → (f : Fin n → Fin m) → x ∈'' f → x ∈'' factorR f
∈''⇒∈''factorR f mem rewrite ∈''⇒i≡ mem = ≡app∈'' _ (sym (factorRfactorL≡ f (∈''⇒i mem)))

factorRInj : ∀ {n m} → (f : Fin n → Fin m) → Inj (factorR f)
factorRInj {ℕ.suc n} {m} f eq with f zero ∈''? tail f
factorRInj {ℕ.suc n} {m} f eq | yes p = factorRInj (tail f) eq
factorRInj {ℕ.suc n} {m} f {zero} {zero} eq | no p = refl
factorRInj {ℕ.suc n} {m} f {zero} {suc j} eq | no p = ⊥-elim (p (∈''factorR⇒∈'' _ (≡app∈'' _ eq)))
factorRInj {ℕ.suc n} {m} f {suc i} {zero} eq | no p = ⊥-elim (p (∈''factorR⇒∈'' _ (≡app∈'' _ (sym eq))))
factorRInj {ℕ.suc n} {m} f {suc i} {suc j} eq | no p = cong suc (factorRInj (tail f) eq)

≡⇒factorL≡ : ∀ {n m x y} → (f : Fin n → Fin m) → f x ≡ f y → factorL f x ≡ factorL f y
≡⇒factorL≡ {x = x} {y = y} f eq = factorRInj f (trans (factorRfactorL≡ f x) (trans eq (sym (factorRfactorL≡ f y))))

{-
f zero ∈''? tail f != w of type Dec (f zero ∈'' (λ i → f (suc i)))
when checking that the type
(n : ℕ) {m : ℕ} (f : Fin (ℕ.suc n) → Fin m)
(w : Dec (f zero ∈'' (λ i → f (suc i))))
(x : Fin (factorInd f | w)) →
x ∈'' factorL f
of the generated with function is well-formed

∀∈''factorL : ∀ {n m} → (f : Fin n → Fin m) → (x : Fin (factorInd f)) → x ∈'' factorL f
∀∈''factorL {ℕ.suc n} {m} f with f zero ∈''? tail f
... | yes p = ?
... | no p = ?-}


∀∈''factorL : ∀ {n m} → (f : Fin n → Fin m) → (x : Fin (factorInd f)) → x ∈'' factorL f
∀∈''updateLYes : ∀ {n m} → (f : Fin (ℕ.suc n) → Fin (ℕ.suc m)) → (mem : f zero ∈'' tail f)
  → (x : Fin (factorInd (tail f))) → x ∈'' updateLYes f mem 
∀∈''updateLNo : ∀ {n m} → (f : Fin (ℕ.suc n) → Fin (ℕ.suc m)) → (x : Fin (ℕ.suc (factorInd (tail f)))) → x ∈'' updateLNo f

∀∈''factorL {ℕ.suc n} {ℕ.zero} f x = ⊥-elim (FinProp.¬Fin0 (f zero))
∀∈''factorL {ℕ.suc n} {ℕ.suc m} f x with f zero ∈''? tail f
... | yes p = ∀∈''updateLYes _ p _
... | no p = ∀∈''updateLNo _ _

∀∈''updateLYes f mem x = ∈''-tail _ _ (∀∈''factorL (tail f) x)

∀∈''updateLNo f zero = ∈''-zero _
∀∈''updateLNo f (suc x) = ∈''-tail _ _ (∈''⇒app∈'' _ suc (∀∈''factorL (tail f) x))

factorLSurj : ∀ {n m} → (f : Fin n → Fin m) → Surj (factorL f)
factorLSurj f = ∀∈''⇒Surj _ λ{x} → ∀∈''factorL f x

Mono⇒factorRMono : ∀ {n m} → (f : Fin n → Fin m) → Mono f → Mono (factorR f)
Mono⇒updateRMono : ∀ {n m} → (f : Fin (ℕ.suc n) → Fin m) → Mono f → Mono (updateR f)

Mono⇒factorRMono {ℕ.suc n} f mono le with f zero ∈''? tail f
... | yes p = Mono⇒factorRMono (tail f) (Mono⇒tailMono f mono) le
... | no p = Mono⇒updateRMono f mono le

Mono⇒updateRMono f mono = tailMono+zero≤⇒Mono _ (Mono⇒factorRMono (tail f) (Mono⇒tailMono f mono)) λ{i} → aux i where
  aux : ∀ (i) → f zero ≤ updateR f i
  aux zero = FinProp.≤-refl
  aux (suc i) rewrite ∈''⇒i≡ (∈''-tail _ f (∈''factorR⇒∈'' (tail f) (app∈'' i (factorR (tail f))))) = mono Data.Nat.z≤n

Mono⇒factorRsMono : ∀ {n m} → (f : Fin n → Fin m) → Mono f → sMono (factorR f)
Mono⇒factorRsMono f mono = Mono+Inj⇒sMono (Mono⇒factorRMono f mono) (factorRInj f)

Mono⇒factorLMono : ∀ {n m} → (f : Fin n → Fin m) → Mono f → Mono (factorL f)
Mono⇒factorLMono f mono {i} {j} le with FinProp.<-cmp (factorL f i) (factorL f j)
... | Tri.tri< lt _ _ = ℕProp.<⇒≤ lt
... | Tri.tri≈ _ eq _ = FinProp.≤-reflexive eq
... | Tri.tri> _ _ lt = contradiction helper (ℕProp.<⇒≱ (Mono⇒factorRsMono f mono lt))
  where
  helper : factorR f (factorL f i) ≤ factorR f (factorL f j)
  helper rewrite factorRfactorL≡ f i | factorRfactorL≡ f j = mono le 
