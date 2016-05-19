module my-vector where

open import nat
open import bool
open import eq

data 𝕍 {ℓ}(A : Set ℓ) : ℕ → Set ℓ where
  [] : 𝕍 A 0
  _::_ : {n : ℕ} (x : A) (xs : 𝕍 A n) → 𝕍 A (suc n)

infixr 6 _::_ _++𝕍_

_++𝕍_ : ∀ {ℓ} {A : Set ℓ}{n m : ℕ} →
        𝕍 A n → 𝕍 A m → 𝕍 A (n + m)
[] ++𝕍 ys = ys
(x :: xs) ++𝕍 ys = x :: (xs ++𝕍 ys)

test-vector : 𝕍 𝔹 4
test-vector = ff :: tt :: ff :: ff :: []

test-vector-append : 𝕍 𝔹 8
test-vector-append = test-vector ++𝕍 test-vector

head𝕍 : ∀{ℓ}{A : Set ℓ}{n : ℕ} → 𝕍 A (suc n) → A
head𝕍 (x :: _) = x

tail𝕍 : ∀{ℓ}{A : Set ℓ}{n : ℕ} → 𝕍 A n → 𝕍 A (pred n)
tail𝕍 [] = []
tail𝕍 (_ :: xs) = xs

map𝕍 : ∀{ℓ ℓ'}{A : Set ℓ}{B : Set ℓ'}{n : ℕ} →
       (A → B) → 𝕍 A n → 𝕍 B n
map𝕍 f [] = []
map𝕍 f (x :: xs) = f x :: map𝕍 f xs

concat𝕍 : ∀{ℓ}{A : Set ℓ}{n m : ℕ} →
          𝕍 (𝕍 A n) m → 𝕍 A (m * n)
concat𝕍 [] = []
concat𝕍 (xs :: xs₁) = xs ++𝕍 (concat𝕍 xs₁)

nth𝕍 : ∀{ℓ}{A : Set ℓ}{m : ℕ} →
       (n : ℕ) → n < m ≡ tt → 𝕍 A m → A
nth𝕍 zero () []
nth𝕍 zero _ (x :: _) = x
nth𝕍 (suc _) () []
nth𝕍 (suc n₁) p (_ :: xs) = nth𝕍 n₁ p xs

repeat𝕍 : ∀{ℓ}{A : Set ℓ} → (a : A)(n : ℕ) → 𝕍 A n
repeat𝕍 a zero = []
repeat𝕍 a (suc n) = a :: (repeat𝕍 a n)
