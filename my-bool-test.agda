module my-bool-test where

open import bool
open import eq
open import level

~~tt : ~ ~ tt ≡ tt
~~tt = refl

~~ff : ~ ~ ff ≡ ff
~~ff = refl
{-
~~-elim : ∀ (b : 𝔹) → ~ ~ b ≡ b
~~-elim tt = refl
~~-elim ff = refl
-}
~~-elim2 : ∀ (b : 𝔹) → ~ ~ b ≡ b
~~-elim2 tt = ~~tt
~~-elim2 ff = ~~ff

~~tt' : ~ ~ tt ≡ tt
~~tt' = refl{lzero}{𝔹}{tt}

~~ff' : ~ ~ ff ≡ ff
~~ff' = refl{lzero}{𝔹}{ff}

~~-elim : ∀ (b : 𝔹) → ~ ~ b ≡ b
~~-elim tt = refl
~~-elim ff = refl

||≡ff₁ : ∀ {b1 b2} → b1 || b2 ≡ ff → b1 ≡ ff
||≡ff₁ {ff} _ = refl{lzero}{𝔹}{ff}
||≡ff₁ {tt} ()

||≡ff₂ : ∀ {b1 b2} → b1 || b2 ≡ ff → ff ≡ b1
||≡ff₂ {ff} _ = refl{lzero}{𝔹}{ff}
||≡ff₂ {tt} p = sym p

||-cong₁ : ∀ {b1 b1' b2} → b1 ≡ b1' → b1 || b2 ≡ b1' || b2
||-cong₁{b1}{.b1}{b2} refl = refl

||-cong₂ : ∀ {b1 b2 b2'} → b2 ≡ b2' → b1 || b2 ≡ b1 || b2'
||-cong₂ p rewrite p = refl

ite-same : ∀{ℓ}{A : Set ℓ} →
           ∀(b : 𝔹) (x : A) →
           (if b then x else x) ≡ x
ite-same tt x = refl
ite-same ff x = refl

𝔹-contra : ff ≡ tt → ∀ {P : Set} → P
𝔹-contra ()

p : ff && ff ≡ ~ tt
p = refl
