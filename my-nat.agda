module my-nat where

open import product
open import bool
open import eq

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

infixl 10 _*_
infixl 9 _+_
--infixl 8 _<_ _=ℕ_ _≤_ _>_ _≥_

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

0+ : ∀ (x : ℕ) → 0 + x ≡ x
0+ x = refl

+0 : ∀ (x : ℕ) → x + 0 ≡ x
+0 zero = refl
+0 (suc x) rewrite +0 x = refl

+assoc : ∀ (x y z : ℕ) → x + (y + z) ≡ (x + y) + z
+assoc zero y z = refl
+assoc (suc x) y z rewrite +assoc x y z = refl

+suc : ∀ (x y : ℕ) → x + (suc y) ≡ suc(x + y)
+suc zero y = refl
+suc (suc x) y rewrite +suc x y = refl

+comm : ∀ (x y : ℕ) → x + y ≡ y + x
+comm zero y rewrite +0 y = refl
+comm (suc x) y rewrite +suc y x | +comm x y = refl

_*_ : ℕ → ℕ → ℕ
zero  * n = zero
suc m * n = n + (m * n)

*distribr : ∀ (x y z : ℕ) → (x + y) * z ≡ x * z + y * z
--*distribr : ∀ (x y z : ℕ) → (x + y) * z ≡ x * z + y * z
*distribr zero y z = refl
*distribr (suc x) y z rewrite *distribr x y z = +assoc z (x * z) (y * z)

*0 : ∀ (x : ℕ) → x * 0 ≡ 0
*0 zero = refl
*0 (suc x) = *0 x

*suc : ∀ (x y : ℕ) → x * (suc y) ≡ x + x * y
*suc zero y = refl
*suc (suc x) y rewrite *suc x y
                       | +assoc y x (x * y)
                       | +assoc x y (x * y)
                       | +comm x y = refl

*comm : ∀ (x y : ℕ) → x * y ≡ y * x
*comm zero y rewrite *0 y = refl
*comm (suc x) y rewrite *suc y x | *comm x y = refl

*assoc : ∀ (x y z : ℕ) → x * (y * z) ≡ (x * y) * z
*assoc zero y z = refl
*assoc (suc x) y z rewrite *distribr y (x * y) z
                           | *assoc x y z = refl

_<_ : ℕ → ℕ → 𝔹
0 < 0 = ff
0 < (suc y) = tt
(suc x) < (suc y) = x < y
(suc x) < 0 = ff

_=ℕ_ : ℕ → ℕ → 𝔹
0 =ℕ 0 = tt
suc x =ℕ suc y = x =ℕ y
_ =ℕ _ = ff

=ℕ-refl : ∀ (x : ℕ) → (x =ℕ x) ≡ tt
=ℕ-refl zero = refl
=ℕ-refl (suc x) = =ℕ-refl x

=ℕ-to-≡ : ∀ {x y : ℕ} → x =ℕ y ≡ tt → x ≡ y
=ℕ-to-≡ {zero} {zero} u = refl
=ℕ-to-≡ {zero} {suc y} ()
=ℕ-to-≡ {suc x} {zero} ()
=ℕ-to-≡ {suc x} {suc y} u rewrite =ℕ-to-≡ {x} {y} u = refl

=ℕ-from-≡ : ∀ {x y : ℕ} → x ≡ y → x =ℕ y ≡ tt
=ℕ-from-≡ {x} {.x} refl = =ℕ-refl x

is-even : ℕ → 𝔹
is-odd : ℕ → 𝔹
is-even 0 = tt
is-even (suc x) = is-odd x
is-odd 0 = ff
is-odd (suc x) = is-even x

even~odd : ∀ (x : ℕ) → is-even x ≡ ~ is-odd x
odd~even : ∀ (x : ℕ) → is-odd x ≡ ~ is-even x
even~odd zero = refl
even~odd (suc x) = odd~even x
odd~even zero = refl
odd~even (suc x) = even~odd x
