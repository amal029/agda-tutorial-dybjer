module Universe where

-- This is universe polymorphism and extensional equality module
open import Sec2

data _≃₀_ {A : Set} (a : A) (b : A) : Set where
  a≃b : (a ≡ b) → a ≃₀ b

data _≃₁_ {A : Set} (f : A → A) (g : A → A) : Set where
  f≃g : ((x y : A) → (x ≃₀ y) → (f x ≃₀ g y)) → f ≃₁ g

B==B : 1 ≃₀ 1
B==B = a≃b refl

B==B1 : T ≃₀ T
B==B1 = a≃b refl 


-- This is the same as + for natural numbers
_⋆_ : (x y : ℕ) → ℕ
Z ⋆ y = y
(S x) ⋆ y = S (x ⋆ y)

-- Proof that + and ⋆ are equivalent functions!
+==⋆ : (x : ℕ) → ((_+_) x) ≃₁ ((_⋆_) x)
+==⋆ x = f≃g (λ x₁ y x₂ → a≃b (prove x x₁ y x₂))
  where
    fcong : (x y : ℕ) → (p : (x + y) ≡ (x ⋆ y)) → S (x + y) ≡ S (x ⋆ y)
    fcong x y p with (x + y) | (x ⋆ y) 
    fcong x y refl | m | .m = refl

    prove' : (x y : ℕ) → (x + y) ≡ (x ⋆ y)
    prove' Z y = refl
    prove' (S x) y with (prove' x y)
    prove' (S x) y | p = fcong x y p


    prove : (x y z : ℕ) → (p : y ≃₀ z) → (x + y) ≡ (x ⋆ z)
    prove x y .y (a≃b refl) = prove' x y

-- Theorem that ≃₁ is a partial equivalence relation
≃₁-symmetric : {A : Set} → {f g : A → A} → (f ≃₁ g) → (g ≃₁ f)
≃₁-symmetric {A} {f} {g} (f≃g x) = f≃g (λ x₁ y x₂ → a≃b (prove x₁ y x₂ (f≃g x)))
  where
    prove : (z y : A) → (p : z ≃₀ y) → (f ≃₁ g) → (g z ≡ f y) 
    prove z .z (a≃b refl) (f≃g x) = {!!}

≃₁-transitive : {A : Set} → {f g h : A → A}
                → (f ≃₁ g) → (g ≃₁ h) → (f ≃₁ h)
≃₁-transitive (f≃g x) (f≃g y) = f≃g (λ x₁ y₁ x₂ → a≃b {!!}) -- todo
-- Goal: .f x₁ ≡ .h y₁
-- ————————————————————————————————————————————————————————————
-- x₂ : x₁ ≃₀ y₁
-- y₁ : .A
-- x₁ : .A
-- y  : (x₃ y₂ : .A) → x₃ ≃₀ y₂ → .g x₃ ≃₀ .h y₂
-- x  : (x₃ y₂ : .A) → x₃ ≃₀ y₂ → .f x₃ ≃₀ .g y₂
-- .h : .A → .A
-- .g : .A → .A
-- .f : .A → .A
-- .A : Set

≃₁-semi-reflexive : {A : Set} → {f g : A → A}
                    → (f ≃₁ g) → (f ≃₁ f)
≃₁-semi-reflexive (f≃g x) = f≃g (λ x₁ y x₂ → a≃b {!!}) -- todo
-- Goal: .f x₁ ≡ .f y
-- ————————————————————————————————————————————————————————————
-- x₂ : x₁ ≃₀ y
-- y  : .A
-- x₁ : .A
-- x  : (x₃ y₁ : .A) → x₃ ≃₀ y₁ → .f x₃ ≃₀ .g y₁
-- .g : .A → .A
-- .f : .A → .A
-- .A : Set
