module sk where

open import nat

data comb : Set where
  S : comb
  K : comb
  app : comb → comb → comb

data _↝_ : comb → comb → Set where
  ↝K : (a b : comb) → (app (app K a) b) ↝ a
  ↝S : (a b c : comb) → (app (app (app S a) b) c) ↝ (app (app a c) (app b c))
  ↝Cong1 : {a a' : comb} (b : comb) → a ↝ a' → (app a b) ↝ (app a' b)
  ↝Cong2 : (a : comb) {b b' : comb} → b ↝ b' → (app a b) ↝ (app a b')

size : comb → ℕ
size S = 1
size K = 1
size (app a b) = suc (size a + size b)
