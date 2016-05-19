module my-list where

open import level
open import bool
open import eq
open import maybe
open import nat
open import nat-thms
open import product-thms
open import product

data 𝕃 {ℓ} (A : Set ℓ) : Set ℓ where
  [] : 𝕃 A
  _::_ : (x : A) (xs : 𝕃 A) → 𝕃 A

{-# BUILTIN LIST 𝕃 #-}
{-# BUILTIN NIL  []   #-}
{-# BUILTIN CONS _::_  #-}

length : ∀{ℓ}{A : Set ℓ} → 𝕃 A → ℕ
length [] = 0
length (x :: x₁) = suc (length x₁)

_++_ : ∀ {ℓ}{A : Set ℓ} → 𝕃 A → 𝕃 A → 𝕃 A
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

map : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → (A → B) → 𝕃 A → 𝕃 B
map f []        = []
map f (x :: xs) = f x :: map f xs

filter : ∀{ℓ}{A : Set ℓ} → (A → 𝔹) → 𝕃 A → 𝕃 A
filter p [] = []
filter p (x :: xs) = let r = filter p xs in 
                     if p x then x :: r else r

-- remove all elements equal to the given one
remove : ∀{ℓ}{A : Set ℓ}(eq : A → A → 𝔹)(a : A)(l : 𝕃 A) → 𝕃 A
remove eq a l = filter (λ x → ~ (eq a x)) l

nth : ∀{ℓ}{A : Set ℓ} → ℕ → 𝕃 A → maybe A
nth _ [] = nothing
nth 0 (x :: xs) = just x
nth (suc n) (x :: xs) = nth n xs

reverse-helper : ∀ {ℓ}{A : Set ℓ} → 𝕃 A → 𝕃 A → 𝕃 A
reverse-helper h [] = h
reverse-helper h (x :: xs) = reverse-helper (x :: h) xs

reverse : ∀ {ℓ}{A : Set ℓ} → 𝕃 A → 𝕃 A
reverse l = reverse-helper [] l

length-++ : ∀{ℓ}{A : Set ℓ}(l1 l2 : 𝕃 A) →
            length (l1 ++ l2) ≡ (length l1) + (length l2)
length-++ [] l2 = refl
length-++ (x :: l1) l2 rewrite length-++ l1 l2 = refl

++-assoc : ∀{ℓ}{A : Set ℓ} (l1 l2 l3 : 𝕃 A) →
           (l1 ++ l2) ++ l3 ≡ l1 ++ (l2 ++ l3)
++-assoc [] l2 l3 = refl
++-assoc (x :: l1) l2 l3 rewrite ++-assoc l1 l2 l3 = refl

length-filter : ∀{ℓ}{A : Set ℓ}(p : A → 𝔹)(l : 𝕃 A) →
                length (filter p l) ≤ length l ≡ tt
length-filter p [] = refl
length-filter p (x :: l) with p x
...                      | tt = length-filter p l
...                      | ff = ≤-trans{length (filter p l)}
                                   (length-filter p l) (≤-suc (length l))

filter-idem : ∀{ℓ}{A : Set ℓ}(p : A → 𝔹)(l : 𝕃 A) →
              (filter p (filter p l)) ≡ (filter p l)
filter-idem p [] = refl
filter-idem p (x :: l) with keep (p x)
...                    | tt , p'
  rewrite p' | p' | filter-idem p l = refl
...                    | ff , p' rewrite p' = filter-idem p l

length-reverse-helper : ∀{ℓ}{A : Set ℓ}(h l : 𝕃 A) →
                        length (reverse-helper h l) ≡ length h + length l
length-reverse-helper h [] = sym (+0 (length h))
length-reverse-helper h (x :: l)
  rewrite length-reverse-helper (x :: h) l =
    sym (+suc (length h) (length l))
