module FinTest where

open import Data.Fin using (Fin; zero; suc; _≤_; _<_)
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
open import Data.Empty using (⊥; ⊥-elim)
open import Agda.Builtin.Sigma using (Σ; _,_) renaming (fst to proj₁ ; snd to proj₂)

{-
tail : ∀ {n m} → (f : Fin (ℕ.suc n) → Fin m) → Fin n → Fin m
tail f i = f (suc i)

infix 5 _∈''?_
_∈''?_ : ∀ {n m} → (x : Fin m) → (f : Fin n → Fin m) → Bool
_∈''?_ {ℕ.zero} x f = false
_∈''?_ {ℕ.suc n} x f with x ≟ f zero
... | yes _ = true
... | no _ = x ∈''? tail f

∈''≡true⇒i : ∀ {n m} → {x : Fin m} → {f : Fin n → Fin m} → x ∈''? f ≡ true → Fin n
∈''≡true⇒i {ℕ.suc n} {m} {x} {f} mem with x ≟ f zero
... | yes _ = zero
... | no _ = suc (∈''≡true⇒i mem)

-- removing "{f = tail f}" will lead to errors
∈''≡true⇒i≡ : ∀ {n m} → {x : Fin m} → {f : Fin n → Fin m} → (mem : x ∈''? f ≡ true) → x ≡ f (∈''≡true⇒i mem)
∈''≡true⇒i≡ {ℕ.suc n} {m} {x} {f} mem with x ≟ f zero
... | yes a = a
... | no _ = ∈''≡true⇒i≡ {f = tail f} mem

{-
factorInd : ∀ {n m} → (f : Fin n → Fin m) → ℕ
factorInd {ℕ.zero} f = ℕ.zero
factorInd {ℕ.suc n} f with f zero ∈''? tail f
... | true = factorInd (tail f)
... | false = ℕ.suc (factorInd (tail f))

factorL : ∀ {n m} → (f : Fin n → Fin m) →  Fin n → Fin (factorInd f)
factorL {ℕ.zero} f ()
factorL {ℕ.suc n} {ℕ.zero} f = ⊥-elim (FinProp.¬Fin0 (f zero)) 
factorL {ℕ.suc n} {ℕ.suc m} f x with f zero ∈''? tail f in mem
factorL {ℕ.suc n} {ℕ.suc m} f zero | true = factorL (tail f) (∈''≡true⇒i mem)
factorL {ℕ.suc n} {ℕ.suc m} f (suc x) | true = factorL (tail f) x
factorL {ℕ.suc n} {ℕ.suc m} f zero | false = zero
factorL {ℕ.suc n} {ℕ.suc m} f (suc x) | false = suc (factorL (tail f) x)

factorR : ∀ {n m} → (f : Fin n → Fin m) →  Fin (factorInd f) → Fin m
factorR {ℕ.zero} f ()
factorR {ℕ.suc n} f x with f zero ∈''? tail f
factorR {ℕ.suc n} f x | true = factorR (tail f) x
factorR {ℕ.suc n} f zero | false = f zero
factorR {ℕ.suc n} f (suc x) | false = factorR (tail f) x

factorRfactorL≡ : ∀ {n m} → (f : Fin n → Fin m) → (x : Fin n) → factorR f ((factorL f) x) ≡ f x
factorRfactorL≡ {ℕ.suc n} {ℕ.zero} f x = ⊥-elim (FinProp.¬Fin0 (f zero))
factorRfactorL≡ {ℕ.suc n} {ℕ.suc m} f zero with f zero ∈''? tail f
... | true = ?
... | false = ?
-}


factorInd : ∀ {n m} → (f : Fin n → Fin m) → ℕ
factorInd {ℕ.zero} f = ℕ.zero
factorInd {ℕ.suc n} f = aux₁ (f zero ∈''? tail f)
  where
  aux₁ : Bool → ℕ
  aux₁ true = factorInd (tail f)
  aux₁ false = ℕ.suc (factorInd (tail f))


factorL : ∀ {n m} → (f : Fin n → Fin m) →  Fin n → Fin (factorInd f)
factorL {ℕ.zero} f ()
factorL {ℕ.suc n} {ℕ.zero} f = ⊥-elim (FinProp.¬Fin0 (f zero)) 
factorL {ℕ.suc n} {ℕ.suc m} f x = {!!}
{-
factorL {ℕ.suc n} {ℕ.suc m} f zero | true = factorL (tail f) (∈''≡true⇒i mem)
factorL {ℕ.suc n} {ℕ.suc m} f (suc x) | true = factorL (tail f) x
factorL {ℕ.suc n} {ℕ.suc m} f zero | false = zero
factorL {ℕ.suc n} {ℕ.suc m} f (suc x) | false = suc (factorL (tail f) x)-}

factorR : ∀ {n m} → (f : Fin n → Fin m) →  Fin (factorInd f) → Fin m
factorR {ℕ.zero} f ()
factorR {ℕ.suc n} {m} f x = aux₃ x (f zero ∈''? tail f)
  where
  aux₃ : Fin (factorInd f) →  Bool → Fin m
  aux₃ x true = factorR (tail f) x
  aux₃ zero false = f zero
  aux₃ (suc x) false = factorR (tail f) x

{- with f zero ∈''? tail f
factorR {ℕ.suc n} f x | true = factorR (tail f) x
factorR {ℕ.suc n} f zero | false = f zero
factorR {ℕ.suc n} f (suc x) | false = factorR (tail f) x
-}
-}


tail : ∀ {n m} → (f : Fin (ℕ.suc n) → Fin m) → Fin n → Fin m
tail f i = f (suc i)

infix 5 _∈''_ -- _∈''?_

data _∈''_ : ∀ {n m} → (x : Fin m) → (f : Fin n → Fin m) → Set where
  ∈''-zero : ∀ {n m} → (f : Fin (ℕ.suc n) → Fin m) → f zero ∈'' f
  ∈''-tail : ∀ {n m} → (x : Fin m) → (f : Fin (ℕ.suc n) → Fin m) → x ∈'' tail f → x ∈'' f

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

{-
factorInd : ∀ {n m} → (f : Fin n → Fin m) → ℕ
factorInd {ℕ.zero} f = ℕ.zero
factorInd {ℕ.suc n} f = helper₁ (f zero ∈''? tail f)
  where
  helper₁ : Dec (f zero ∈'' tail f) → ℕ
  helper₁ (yes _) = factorInd (tail f)
  helper₁ (no _) = ℕ.suc (factorInd (tail f))

factorL : ∀ {n m} → (f : Fin n → Fin m) →  Fin n → Fin (factorInd f)
factorL {ℕ.zero} f ()
factorL {ℕ.suc n} {ℕ.zero} f = ⊥-elim (FinProp.¬Fin0 (f zero)) 
factorL {ℕ.suc n} {ℕ.suc m} f x = {!!}

factorR : ∀ {n m} → (f : Fin n → Fin m) →  Fin (factorInd f) → Fin m
factorR {ℕ.zero} f ()
factorR {ℕ.suc n} {m} f x = helper₃ (f zero ∈''? tail f) x where
  helper₃ : _ → _ → Fin m
  helper₃ (yes p) y = {!!}
  helper₃ (no np) _ = {!!}

{- with f zero ∈''? tail f
factorR {ℕ.suc n} f x | true = factorR (tail f) x
factorR {ℕ.suc n} f zero | false = f zero
factorR {ℕ.suc n} f (suc x) | false = factorR (tail f) x
-}
-}

{-
helper : ∀ {n m} → (f : Fin (ℕ.suc n) → Fin m) → Dec (f zero ∈'' tail f) → ℕ → ℕ
helper _ (yes _) n = n
helper _ (no _) n = ℕ.suc n

factorInd : ∀ {n m} → (f : Fin n → Fin m) → ℕ
factorInd {ℕ.zero} f = ℕ.zero
factorInd {ℕ.suc n} f = helper f (f zero ∈''? tail f) (factorInd (tail f))

factorL : ∀ {n m} → (f : Fin n → Fin m) →  Fin n → Fin (factorInd f)
factorL {ℕ.zero} f ()
factorL {ℕ.suc n} {ℕ.zero} f = ⊥-elim (FinProp.¬Fin0 (f zero)) 
factorL {ℕ.suc n} {ℕ.suc m} f x = {!!}

factorR : ∀ {n m} → (f : Fin n → Fin m) →  Fin (factorInd f) → Fin m
factorR {ℕ.zero} f ()
factorR {ℕ.suc n} {m} f x = helper₃ (f zero ∈''? tail f) x where
  helper₃ : _ → _ → Fin m
  helper₃ (yes p) y = {!!}
  helper₃ (no np) _ = {!!}
-}


factorInd : ∀ {n m} → (f : Fin n → Fin m) → ℕ
factorInd {ℕ.zero} f = ℕ.zero
factorInd {ℕ.suc n} f with f zero ∈''? tail f
... | yes _ = factorInd (tail f)
... | no _ = ℕ.suc (factorInd (tail f))

factorL : ∀ {n m} → (f : Fin n → Fin m) →  Fin n → Fin (factorInd f)
factorL {ℕ.zero} f ()
factorL {ℕ.suc n} {ℕ.zero} f = ⊥-elim (FinProp.¬Fin0 (f zero)) 
factorL {ℕ.suc n} {ℕ.suc m} f x with f zero ∈''? tail f
factorL {ℕ.suc n} {ℕ.suc m} f zero | yes mem = factorL (tail f) (∈''⇒i mem)
factorL {ℕ.suc n} {ℕ.suc m} f (suc x) | yes _ = factorL (tail f) x
factorL {ℕ.suc n} {ℕ.suc m} f zero | no _ = zero
factorL {ℕ.suc n} {ℕ.suc m} f (suc x) | no _ = suc (factorL (tail f) x)

factorR : ∀ {n m} → (f : Fin n → Fin m) →  Fin (factorInd f) → Fin m
factorR {ℕ.zero} f ()
factorR {ℕ.suc n} f x with f zero ∈''? tail f
factorR {ℕ.suc n} f x | yes _ = factorR (tail f) x
factorR {ℕ.suc n} f zero | no _ = f zero
factorR {ℕ.suc n} f (suc x) | no _ = factorR (tail f) x

factorRfactorL≡ : ∀ {n m} → (f : Fin n → Fin m) → (x : Fin n) → factorR f ((factorL f) x) ≡ f x
factorRfactorL≡ {ℕ.suc n} {ℕ.zero} f x = ⊥-elim (FinProp.¬Fin0 (f zero))
factorRfactorL≡ {ℕ.suc n} {ℕ.suc m} f x with f zero ∈''? tail f
factorRfactorL≡ {ℕ.suc n} {ℕ.suc m} f zero | yes p = trans (factorRfactorL≡ (tail f) (∈''⇒i p)) (sym (∈''⇒i≡ p)) 
factorRfactorL≡ {ℕ.suc n} {ℕ.suc m} f (suc x) | yes p = factorRfactorL≡ (tail f) x
factorRfactorL≡ {ℕ.suc n} {ℕ.suc m} f zero | no p = refl
factorRfactorL≡ {ℕ.suc n} {ℕ.suc m} f (suc x) | no p = factorRfactorL≡ (tail f) x
