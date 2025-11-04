module Fin where

open import Data.Fin using (Fin; zero; suc; _≤_; _<_; toℕ)
import Data.Fin.Properties as FinProp
import Data.Nat.Properties as ℕProp
open import Data.List
  using (List; []; _∷_; map; _++_; length)
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; true; false)
open import Data.Fin.Properties using (_≟_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.Definitions using (Tri)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; sym)
open import Relation.Nullary using (¬_; contradiction)
open import Function using (_∘_; id)
open import Data.Product.Base using (∃; ∃-syntax)
open import Data.Empty using (⊥; ⊥-elim)
open import Agda.Builtin.Sigma using (Σ; _,_) renaming (fst to proj₁ ; snd to proj₂)

imageList : ∀ {n m} → (Fin n → Fin m) → List (Fin m)
imageList {ℕ.zero}  f = []
imageList {ℕ.suc n} f = f zero ∷ imageList (λ i → f (suc i))

{-
open import Relation.Binary.PropositionalEquality
testFun : Fin 2 → Fin 3
testFun zero = zero
testFun (suc zero) = suc (suc zero)

testList : List (Fin 3)
testList = zero ∷ suc (suc zero) ∷ []

testEq : imageList testFun ≡ testList
testEq = refl
-}

infix 5 _∈?_
infix 5 _∈_

data _∈_ {n} : Fin n → List (Fin n) → Set where
  ∈head : ∀ {x xs} → x ∈ (x ∷ xs)
  ∈cons : ∀ {x y xs} → x ∈ xs → x ∈ (y ∷ xs)

_∈?_ : ∀ {n} → Fin n → List (Fin n) → Bool
x ∈? []       = false
x ∈? (y ∷ ys) with x ≟ y
... | yes _ = true
... | no  _ = x ∈? ys

∈⇒∈?≡true : ∀ {n} {x : Fin n} {xs : List (Fin n)} → x ∈ xs → x ∈? xs ≡ true
∈⇒∈?≡true {n} {x} {xs} ∈head with x ≟ x
... | yes _ = refl
... | no a = contradiction refl a
∈⇒∈?≡true {n} {x} {xs} (∈cons {y = y} mem) with x ≟ y
... | yes _ = refl
... | no _ = ∈⇒∈?≡true mem

∈?≡true⇒∈ : ∀ {n} {x : Fin n} {xs : List (Fin n)} → x ∈? xs ≡ true → x ∈ xs
∈?≡true⇒∈ {n} {x} {xs = y ∷ xs} mem with x ≟ y
... | yes a rewrite a = ∈head
... | no _ = ∈cons (∈?≡true⇒∈ mem)

¬∈⇒∈?≡false : ∀ {n} {x : Fin n} {xs : List (Fin n)} → ¬ x ∈ xs → x ∈? xs ≡ false
¬∈⇒∈?≡false {n} {x} {xs} notmem with x ∈? xs in eq
... | true = ⊥-elim (notmem (∈?≡true⇒∈ eq))
... | false = refl

data nondup {n} : List (Fin n) → Set where
  nd-[] : nondup []
  nd-∷ : ∀ {x xs} → (x ∈? xs ≡ false) → nondup xs → nondup (x ∷ xs)
  
toNondup : ∀ {n} → List (Fin n) → List (Fin n)
toNondup []       = []
toNondup (x ∷ xs) with x ∈? xs
... | true  = toNondup xs
... | false = x ∷ toNondup xs

toNondup≡ : ∀ {n} → {f : List (Fin n)} → nondup f → toNondup f ≡ f
toNondup≡ {n} {f} nd-[] = refl
toNondup≡ {n} {x ∷ xs} (nd-∷ x∈? nd) with x ∈? xs
... | false = cong (λ xs → _ ∷ xs) (toNondup≡ nd)

∈?≡true⇒∈?toNondup≡true : ∀ {n x} → (f : List (Fin n)) → x ∈? f ≡ true → x ∈? toNondup f ≡ true
∈?≡true⇒∈?toNondup≡true {x = x} (y ∷ f) eq with y ∈? f in eq'
... | true with x ≟ y
...     | yes a rewrite a = ∈?≡true⇒∈?toNondup≡true f eq'
...     | no _ = ∈?≡true⇒∈?toNondup≡true f eq
∈?≡true⇒∈?toNondup≡true  {x = x} (y ∷ f) eq | false with x ≟ y
... | yes _ = refl
... | no _ = ∈?≡true⇒∈?toNondup≡true f eq

∈?≡false⇒∈?toNondup≡false : ∀ {n x} → (f : List (Fin n)) → x ∈? f ≡ false → x ∈? toNondup f ≡ false
∈?≡false⇒∈?toNondup≡false [] eq = eq
∈?≡false⇒∈?toNondup≡false {x = x} (y ∷ f) eq with y ∈? f in eq'
... | true with x ≟ y
...     | no _ = ∈?≡false⇒∈?toNondup≡false f eq
∈?≡false⇒∈?toNondup≡false {x = x} (y ∷ f) eq | false with x ≟ y
... | yes _ = eq
... | no _ =  ∈?≡false⇒∈?toNondup≡false f eq

∈?toNondup≡true⇒∈?≡true : ∀ {n x} → (f : List (Fin n)) → x ∈? toNondup f ≡ true → x ∈? f ≡ true
∈?toNondup≡true⇒∈?≡true {x = x} f eq with x ∈? f in eq'
... | true = refl
... | false rewrite (∈?≡false⇒∈?toNondup≡false f eq') = eq

∈?toNondup≡false⇒∈?≡false : ∀ {n x} → (f : List (Fin n)) → x ∈? toNondup f ≡ false → x ∈? f ≡ false
∈?toNondup≡false⇒∈?≡false {x = x} f eq with x ∈? f in eq'
... | true rewrite (∈?≡true⇒∈?toNondup≡true f eq') = eq
... | false = refl

{-
∈≡true⇒∈toNondup≡true' : ∀ {n x} → (f : List (Fin n)) → x ∈? f ≡ true → x ∈? toNondup f ≡ true
∈≡true⇒∈toNondup≡true' {x = x} (y ∷ f) eq with x ≟ y | y ∈? f in eq'
... | yes _ | true = {!!}
... | yes _ | false = {!!}
... | no _  | fasle = {!!}
... | no _  | true = {!!}
-}
{-
∈≡true⇒∈toNondup≡true : ∀ {n x} → {f : List (Fin n)} → x ∈? f ≡ true → x ∈? toNondup f ≡ true
∈≡true⇒∈toNondup≡true {x = x} {f = y ∷ f} eq with y ∈? f in eq'
... | true with x ≟ y
...     | yes a rewrite a = ∈≡true⇒∈toNondup≡true f eq'
...     | no _ = ∈≡true⇒∈toNondup≡true f eq
∈≡true⇒∈toNondup≡true  {x = x} {f = y ∷ f} eq | false with x ≟ y
... | yes _ = refl
... | no _ = ∈≡true⇒∈toNondup≡true f eq
-}

toNondupNondup : ∀ {n} → (f : List (Fin n)) → nondup (toNondup f)
toNondupNondup [] = nd-[]
toNondupNondup (x ∷ f) with x ∈? f in eq
... | true = toNondupNondup f
... | false = nd-∷ (∈?≡false⇒∈?toNondup≡false f eq) (toNondupNondup f)

{-
open import Relation.Binary.PropositionalEquality

testList : List (Fin 4)
testList = zero ∷ zero ∷ suc (suc zero) ∷ suc (suc (suc zero))
  ∷ suc (suc zero) ∷ []

testEq : nondup testList ≡ zero ∷ suc (suc (suc zero)) ∷ suc (suc zero) ∷ []
testEq = refl
-}

imageCard : ∀ {n m} → (Fin n → Fin m) → ℕ
imageCard f = length (toNondup (imageList f))

{-
open import Relation.Binary.PropositionalEquality
testFun : Fin 3 → Fin 4
testFun zero = zero
testFun (suc zero) = suc (suc zero)
testFun (suc (suc zero)) = suc (suc zero)

testEq : imageCard testFun ≡ 2
testEq = refl
-}
Mono : {n m : ℕ} → (f : Fin n → Fin m) → Set
Mono f = ∀ {i j} → i ≤ j → f i ≤ f j

sMono : {n m : ℕ} → (f : Fin n → Fin m) → Set
sMono f = ∀ {i j} → (i < j → f i < f j)

Inj : {n m : ℕ} → (f : Fin n → Fin m) → Set
Inj f = ∀ {i j} → f i ≡ f j → i ≡ j

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

Surj : {n m : ℕ} → (f : Fin n → Fin m) → Set
Surj f = ∀ y → ∃[ x ] f x ≡ y

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


-- Inj ⇒ nondup imageList

-- headNotInTail : ∀ {n m} (f : Fin (ℕ.suc n) → Fin m) → Inj f → ¬ f zero ∈ imageList (λ i → f (suc i))

-- prove something like, x ∈ imageList, then y with fy = x...

of∈imageList : ∀ {n m y} → (f : Fin n → Fin m) → y ∈ imageList f → ∃[ i ] y ≡ f i
of∈imageList {ℕ.suc n} {m} {y} f ∈head = zero , refl
of∈imageList {ℕ.suc n} {m} {y} f (∈cons mem) = suc (proj₁ (of∈imageList _ mem)) , proj₂ (of∈imageList _ mem)

Inj⇒¬∈imageList : ∀ {n m} (f : Fin (ℕ.suc n) → Fin m) → Inj f → ¬ f zero ∈ imageList (λ i → f (suc i))
Inj⇒¬∈imageList {n} {m} f inj mem = FinProp.0≢1+n (inj (proj₂ (of∈imageList _ mem)))

Inj⇒nondupImageList : ∀ {n m} → (f : Fin n → Fin m) → Inj f → nondup (imageList f)
Inj⇒nondupImageList {ℕ.zero} {m} f inj = nd-[]
Inj⇒nondupImageList {ℕ.suc n} {m} f inj = nd-∷ (¬∈⇒∈?≡false (Inj⇒¬∈imageList _ inj))
  (Inj⇒nondupImageList _ (λ eq →  FinProp.suc-injective (inj eq)))

ListToFun : ∀ {m} → (f : List (Fin m)) → ∃[ i ] (Fin i → Fin m)
ListToFun {m} [] = ℕ.zero , λ()
ListToFun {m} (x ∷ f) = ℕ.suc (proj₁ (ListToFun f)) , f'
  where
    f' : Fin (ℕ.suc (proj₁ (ListToFun f))) → Fin m
    f' zero = x
    f' (suc i) = proj₂ (ListToFun f) i

factor : ∀ {n m} → (f : Fin n → Fin m) → ℕ
factor f = proj₁ (ListToFun (toNondup (imageList f)))

factorInj : ∀ {n m} → (f : Fin n → Fin m) → (Fin (factor f) → Fin m)
factorInj f = proj₂ (ListToFun (toNondup (imageList f)))

--- question.. Without funext, how can show it's a factorization???

-- for factorSurj : Consider a list like [011334799]; from its tail we have [00112344]; then with ¬ 0 ∈ tail, we add 0 ∷ suc (rest of them)
