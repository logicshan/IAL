module my-integer where

open import bool
open import bool-thms2
open import eq
open import nat
open import nat-thms
open import product
--open import product-thms
open import sum
-- open import unit

data ⊤ : Set where
  triv : ⊤

ℤ-pos-t : ℕ → Set
ℤ-pos-t 0 = ⊤
ℤ-pos-t (suc _) = 𝔹

data ℤ : Set where
  mkℤ : (n : ℕ) → ℤ-pos-t n → ℤ

0ℤ : ℤ
0ℤ = mkℤ 0 triv

1ℤ : ℤ
1ℤ = mkℤ 1 tt

-1ℤ : ℤ
-1ℤ = mkℤ 1 ff

abs-val : ℤ → ℕ
abs-val (mkℤ n _) = n

is-evenℤ : ℤ → 𝔹
is-evenℤ (mkℤ n _) = is-even n

is-oddℤ : ℤ → 𝔹
is-oddℤ (mkℤ n _) = is-odd n

{- subtract the second natural number from the first, returning an integer.
   This is mostly a helper for _+ℤ_ -}
diffℤ : ℕ → ℕ → ℤ
diffℤ n m with ℕ-trichotomy n m 
diffℤ n m | inj₁ p with <∸suc{m}{n} p               -- n < m
diffℤ n m | inj₁ p | x , _ = mkℤ (suc x) ff
diffℤ n m | inj₂ (inj₁ p) = mkℤ 0 triv              -- n = m 
diffℤ n m | inj₂ (inj₂ p) with <∸suc{n}{m} p
diffℤ n m | inj₂ (inj₂ p) | x , _ = mkℤ (suc x) tt  -- m < n 

_+ℤ_ : ℤ → ℤ → ℤ
(mkℤ 0 _) +ℤ x = x
x +ℤ (mkℤ 0 _) = x
(mkℤ (suc n) p1) +ℤ (mkℤ (suc m) p2) with p1 xor p2 
(mkℤ (suc n) p1) +ℤ (mkℤ (suc m) p2) | ff = mkℤ (suc n + suc m) p1
(mkℤ (suc n) p1) +ℤ (mkℤ (suc m) p2) | tt = if p1 imp p2 then diffℤ m n else diffℤ n m 
