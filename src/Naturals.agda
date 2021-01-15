module Naturals where

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

seven : ℕ
seven = suc (suc (suc (suc (suc (suc (suc zero))))))

import Relation.Binary.PropositionalEquality as Eq

open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

_+_ : ℕ → ℕ → ℕ
zero    + n = n
(suc m) + n = suc (m + n)

_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩ -- is shorthand for
    (suc (suc zero)) + (suc (suc (suc (zero))))
  ≡⟨⟩ -- inductive case
    suc ((suc zero) + (suc (suc (suc zero))))
  ≡⟨⟩ -- inductive case
    suc (suc (zero + (suc (suc (suc zero)))))
  ≡⟨⟩ -- base case
    suc (suc (suc (suc (suc zero))))
  ≡⟨⟩ -- is longhand for
    5
  ∎

_ : 2 + 3 ≡ 5
_ = refl

_*_ : ℕ → ℕ → ℕ
zero    * n = zero
(suc m) * n = n + (m * n)

_^_ : ℕ → ℕ → ℕ
m ^ zero    = suc zero
m ^ (suc n) = m * (m ^ n)

_ : 3 ^ 4 ≡ 81
_ =
  begin
    3 ^ 4
  ≡⟨⟩ -- applying ^
    3 * (3 ^ 3)
  ≡⟨⟩ -- applying ^
    3 * (3 * (3 ^ 2))
  ≡⟨⟩ -- applying ^
    3 * (3 * (3 * (3 ^ 1)))
  ≡⟨⟩ -- applying ^
    3 * (3 * (3 * (3 * (3 ^ 0))))
  ≡⟨⟩ -- base case
    3 * (3 * (3 * (3 * 1)))
  ≡⟨⟩ -- applying *
    3 * (3 * (3 * 3))
  ≡⟨⟩ -- applying *
    3 * (3 * 9)
  ≡⟨⟩ -- applying *
    3 * 27
  ≡⟨⟩ -- applying *
    81
  ∎

_-_ : ℕ → ℕ → ℕ
m     - zero  = m
zero  - suc n = zero
suc m - suc n = m - n

infixl 6 _+_ _-_
infixl 7 _*_

{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _-_ #-}

-- Binary Representation of number
data Bin : Set where
  ⟨⟩ : Bin
  _𝟘 : Bin → Bin
  _𝟙 : Bin → Bin

eleven : Bin
eleven = ⟨⟩ 𝟙 𝟘 𝟙 𝟙

ceil : Bin -> Bin
ceil ⟨⟩ = ⟨⟩ 𝟙
ceil (m 𝟘) = (ceil m) 𝟘
ceil (m 𝟙) = (ceil m) 𝟘

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ 𝟙
inc (⟨⟩ 𝟘) = ⟨⟩ 𝟙
inc (⟨⟩ 𝟙) = ⟨⟩ 𝟙 𝟘
inc ((m 𝟘) 𝟘) = (m 𝟘) 𝟙
inc ((m 𝟘) 𝟙) = (m 𝟙) 𝟘
inc ((m 𝟙) 𝟘) = (m 𝟙) 𝟙
inc ((m 𝟙) 𝟙) = ceil ((m 𝟙) 𝟙)

to : ℕ → Bin
to zero    = ⟨⟩ 𝟘
to (suc n) = inc (to n)

from : Bin → ℕ
from ⟨⟩ = zero
from (m 𝟘) = 2 * from m
from (m 𝟙) = 2 * from m + 1

_ : from eleven ≡ 11
_ =
  begin
    from eleven
  ≡⟨⟩ -- applying from
    2 * from (⟨⟩ 𝟙 𝟘 𝟙) + 1
  ≡⟨⟩ -- applying from
    2 * (2 * from (⟨⟩ 𝟙 𝟘) + 1) + 1
  ≡⟨⟩ -- applying from
    2 * (2 * (2 * from (⟨⟩ 𝟙)) + 1) + 1
  ≡⟨⟩ -- applying from
    2 * (2 * (2 * (2 * from ⟨⟩ + 1)) + 1) + 1
  ≡⟨⟩ -- base case
    2 * (2 * (2 * (2 * 0 + 1)) + 1) + 1
  ≡⟨⟩ -- refl
    11
  ∎

_ : inc (⟨⟩ 𝟘) ≡ ⟨⟩ 𝟙
_ = refl

_ : inc (⟨⟩ 𝟙) ≡ ⟨⟩ 𝟙 𝟘
_ = refl

_ : inc (⟨⟩ 𝟙 𝟘) ≡ ⟨⟩ 𝟙 𝟙
_ = refl

_ : inc (⟨⟩ 𝟙 𝟙) ≡ ⟨⟩ 𝟙 𝟘 𝟘
_ = refl
