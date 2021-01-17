module Learning.Relations where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm; +-identityʳ)

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n : ℕ} → zero ≤ n
  s≤s : ∀ {m n : ℕ} → m ≤ n → suc m ≤ suc n

infix 4 _≤_

-- Proof that 2 ≤ 4
_ : 2 ≤ 4
_ = s≤s (s≤s z≤n)

-- Proof that 2 ≤ 4 with explicit arguments
_ : 2 ≤ 4
_ = s≤s {1} {3} (s≤s {0} {2} (z≤n {2}))

inv-s≤s : ∀ {m n : ℕ} → suc m ≤ suc n → m ≤ n
inv-s≤s (s≤s m≤n) = m≤n

inv-z≤n : ∀ {m : ℕ} → m ≤ 0 → m ≡ 0
inv-z≤n z≤n = refl

-- Reflexivity
≤-refl : ∀ {n : ℕ} → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

-- Transitivity
≤-trans : ∀ {m n p : ℕ} → m ≤ n → n ≤ p → m ≤ p
≤-trans z≤n       _         = z≤n
≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)

-- Anti-symmetry
≤-antisym : ∀ {m n : ℕ} → m ≤ n → n ≤ m → m ≡ n
≤-antisym z≤n       z≤n       = inv-z≤n z≤n
≤-antisym (s≤s m≤n) (s≤s n≤m) = cong suc (≤-antisym m≤n n≤m)

-- Total
data Total (m n : ℕ) : Set where
  forward : m ≤ n → Total m n
  flipped : n ≤ m → Total m n

≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero    n                        = forward z≤n
≤-total (suc m) zero                     = flipped z≤n
≤-total (suc m) (suc n) with ≤-total m n
...                        | forward m≤n = forward (s≤s m≤n)
...                        | flipped n≤m = flipped (s≤s n≤m)

-- Monotonic Function

-- Addition is monotonic on the right
+-monoʳ-≤ : ∀ (n p q : ℕ) → p ≤ q → n + p ≤ n + q
+-monoʳ-≤ zero    p q p≤q = p≤q
+-monoʳ-≤ (suc n) p q p≤q = s≤s (+-monoʳ-≤ n p q p≤q)

-- Proof of addition is monotonic
+-monoˡ-≤ : ∀ (n p q : ℕ) → p ≤ q → p + n ≤ q + n
+-monoˡ-≤ n p q p≤q rewrite +-comm p n | +-comm q n = +-monoʳ-≤ n p q p≤q

-- General case
+-mono-≤ : ∀ (m n p q : ℕ) → m ≤ n → p ≤ q → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q = ≤-trans (+-monoˡ-≤ p m n m≤n) (+-monoʳ-≤ n p q p≤q)

data _<_ : ℕ → ℕ → Set where
  z<s : ∀ {n : ℕ} → zero < suc n
  s<s : ∀ {m n : ℕ} → m < n → suc m < suc n

infix 4 _<_

inv-s<s : ∀ {a b : ℕ} → suc a < suc b → a < b
inv-s<s (s<s a<b) = a<b

<-trans : ∀ {a b c : ℕ} → a < b → b < c → a < c
<-trans {a = zero} {c = suc c′} a<b b<c = z<s
<-trans {a = suc a′} {b}        a<b b<c = helper (≤-trans {n = b} (p a<b) (trivial b<c))
  where
  helper : ∀ {m n : ℕ} → suc m ≤ n → m < n
  helper (s≤s z≤n)       = z<s
  helper (s≤s (s≤s m≤n)) = s<s (helper (s≤s m≤n))
  trivial : ∀ {a b : ℕ} → a < b → a ≤ b
  trivial z<s     = z≤n
  trivial (s<s p) = s≤s (trivial p)
  p : ∀ {a b : ℕ} → a < b → suc a ≤ b
  p z<s       = s≤s (z≤n)
  p (s<s a<b) = s≤s (p a<b)

data even : ℕ → Set
data odd  : ℕ → Set

data even where
  zero : even zero
  suc  : ∀ {n : ℕ} → odd n → even (suc n)

data odd where
  suc : ∀ {n : ℕ} → even n → odd (suc n)

even+even-is-even : ∀ {m n : ℕ} → even m → even n → even (m + n)
odd+even-is-odd   : ∀ {m n : ℕ} → odd m  → even n → odd  (m + n)
even+even-is-even zero         even-n = even-n
even+even-is-even (suc odd-m)  even-n = suc (odd+even-is-odd odd-m even-n)
odd+even-is-odd   (suc even-m) even-n = suc (even+even-is-even even-m even-n)

even+odd-is-odd : ∀ {m n : ℕ} → even m  → odd n → odd  (m + n)
even+odd-is-odd {m} {n} even-m odd-n rewrite +-comm m n = odd+even-is-odd odd-n even-m

odd+odd-is-even : ∀ {m n : ℕ} → odd m → odd n → even (m + n)
odd+odd-is-even = {!!}
