module Learning.Induction where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p =
  begin
    (zero + n) + p
  ≡⟨⟩
    n + p
  ≡⟨⟩
    zero + (n + p)
  ∎
+-assoc (suc m) n p =
  begin
    (suc m + n) + p
  ≡⟨⟩
    suc (m + n) + p
  ≡⟨⟩
    suc ((m + n) + p)
  ≡⟨ cong suc (+-assoc m n p) ⟩
    suc (m + (n + p))
  ≡⟨⟩
    suc m + (n + p)
  ∎

+-identityʳ : ∀ (m : ℕ) → m + 0 ≡ m
+-identityʳ zero =
  begin
    zero + zero
  ≡⟨⟩
    zero
  ∎
+-identityʳ (suc m) =
  begin
    suc m + zero
  ≡⟨⟩
    suc (m + zero)
  ≡⟨ cong suc (+-identityʳ m) ⟩
    suc m
  ∎

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n = 
  begin
    zero + suc n
  ≡⟨⟩
    suc n
  ∎
+-suc (suc m) n = 
  begin
    suc m + suc n
  ≡⟨⟩
    suc (m + suc n)
  ≡⟨ cong suc (+-suc m n) ⟩
    suc (suc (m + n))
  ≡⟨⟩
    suc (suc m + n)
  ∎

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero = 
  begin
    m + zero
  ≡⟨ +-identityʳ m ⟩
    m
  ≡⟨⟩
    zero + m
  ∎
+-comm m (suc n) = 
  begin
    m + suc n
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc n + m
  ∎

+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q =
  begin
    (m + n) + (p + q)
  ≡⟨ +-assoc m n (p + q) ⟩
    m + (n + (p + q))
  ≡⟨ cong (m +_) (sym (+-assoc n p q)) ⟩
    m + ((n + p) + q)
  ≡⟨ sym (+-assoc m (n + p) q) ⟩
    m + (n + p) + q
  ∎

+-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc′ zero    n p                        = refl
+-assoc′ (suc m) n p rewrite +-assoc′ m n p = refl

+-identity′ : ∀ (n : ℕ) → n + zero ≡ n
+-identity′ zero                          = refl
+-identity′ (suc n) rewrite +-identity′ n = refl

+-suc′ : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc′ zero    n                    = refl
+-suc′ (suc m) n rewrite +-suc′ m n = refl

+-comm′ : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm′ m zero    rewrite +-identity′ m            = refl
+-comm′ m (suc n) rewrite +-suc′ m n | +-comm′ m n = refl

-- Exercise

+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p =
  begin
    m + (n + p)
  ≡⟨ sym (+-assoc m n p) ⟩
    (m + n) + p
  ≡⟨ cong (_+ p) (+-comm m n) ⟩
    (n + m) + p
  ≡⟨ +-assoc n m p ⟩
    n + (m + p)
  ∎

*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ (m * p) + (n * p)
*-distrib-+ zero n p = refl
*-distrib-+ (suc m) n p =
  begin
    (suc m + n) * p
  ≡⟨⟩
    (suc (m + n)) * p
  ≡⟨⟩
    p + ((m + n) * p)
  ≡⟨ cong (p +_) (*-distrib-+ m n p) ⟩
    p + ((m * p) + (n * p))
  ≡⟨ sym (+-assoc p (m * p) (n * p)) ⟩
    (p + (m * p)) + (n * p)
  ≡⟨⟩
    (suc m * p) + (n * p)
  ∎

*-assoc : ∀ (m n p : ℕ) → m * (n * p) ≡ (m * n) * p
*-assoc zero n p = refl
*-assoc (suc m) n p =
  begin
    suc m * (n * p)
  ≡⟨ refl ⟩
    n * p + m * (n * p)
  ≡⟨ cong ((n * p) +_) (*-assoc m n p) ⟩
    n * p + (m * n) * p
  ≡⟨ sym (*-distrib-+ n (m * n) p) ⟩
    (n + (m * n)) * p
  ≡⟨ refl ⟩
    (suc m * n) * p
  ∎

*-0 : ∀ (m : ℕ) → m * 0 ≡ 0
*-0 zero = refl
*-0 (suc m) =
  begin
    suc m * 0
  ≡⟨⟩
    0 + m * 0
  ≡⟨ cong (0 +_) (*-0 m) ⟩
    0
  ∎

*-identityˡ : ∀ (m : ℕ) → m * 1 ≡ m
*-identityˡ zero = refl
*-identityˡ (suc m) =
  begin
    suc m * 1
  ≡⟨⟩
    1 + m * 1
  ≡⟨ cong (1 +_) (*-identityˡ m) ⟩
    suc m
  ∎

*-distrib-+ʳ : ∀ (m n p : ℕ) → p * (m + n) ≡ (p * m) + (p * n)
*-distrib-+ʳ m n zero = refl
*-distrib-+ʳ m n (suc p) =
  begin
    suc p * (m + n)
  ≡⟨⟩
    (m + n) + p * (m + n)
  ≡⟨ cong (λ x → (m + n) + x) (*-distrib-+ʳ m n p) ⟩
    (m + n) + (p * m + p * n)
  ≡⟨ +-rearrange m n (p * m) (p * n)  ⟩
    m + (n + p * m) + p * n
  ≡⟨ cong (λ x → m + x + p * n) (+-comm n (p * m) ) ⟩
    m + (p * m + n) + p * n
  ≡⟨ cong (_+ p * n) (sym (+-assoc m (p * m) n)) ⟩
    (m + p * m) + n + p * n
  ≡⟨ +-assoc (m + p * m) n (p * n) ⟩
    (m + p * m) + (n + p * n)
  ≡⟨⟩
    (suc p * m) + (suc p * n)
  ∎

*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm zero n =
  begin
    zero * n
  ≡⟨⟩
    zero
  ≡⟨ sym (*-0 n) ⟩
    n * zero
  ∎
*-comm (suc m) n =
  begin
    suc m * n
  ≡⟨⟩
    n + m * n
  ≡⟨ cong (n +_) (*-comm m n) ⟩
    n + n * m
  ≡⟨ +-comm n (n * m) ⟩
    n * m + n
  ≡⟨ cong ((n * m) +_) (sym (*-identityˡ n)) ⟩
    n * m + n * 1
  ≡⟨ sym (*-distrib-+ʳ m 1 n) ⟩
    n * (m + 1)
  ≡⟨ cong (n *_) (+-comm m 1) ⟩
    n * suc m
  ∎
