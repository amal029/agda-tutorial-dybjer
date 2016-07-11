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

elim≃₁ : {A : Set} → (f g : A → A) (a : f ≃₁ g)
                 → (x y : A) → (p : x ≃₀ y)
                 → (f x ≃₀ g y)
elim≃₁ f g (f≃g a) x .x (a≃b refl) = a x x (a≃b refl)

-- Theorem that ≃₁ is a partial equivalence relation
≃₁-symmetric : {A : Set} → {f g : A → A} → (f ≃₁ g) → (g ≃₁ f)
≃₁-symmetric {A} {f} {g} (f≃g x) = f≃g (λ x₁ y x₂ → a≃b (prove x₁ y x₂ (f≃g x)))
  where
    prove : (z y : A) → (p : z ≃₀ y) → (f ≃₁ g) → (g z ≡ f y) 
    prove z .z (a≃b refl) (f≃g x) with (x z z (a≃b refl) )
    prove z .z (a≃b refl) (f≃g x₁) | a≃b p with (f z) | (g z) 
    prove z .z (a≃b refl) (f≃g x₁) | a≃b refl | m | .m = refl

≃₁-transitive : {A : Set} → {f g h : A → A}
                → (f ≃₁ g) → (g ≃₁ h) → (f ≃₁ h)
≃₁-transitive {A} {f} {g} {h} (f≃g x) (f≃g y) = f≃g (λ x₁ y₁ x₂ → a≃b (prove x₁ y₁ x₂ (f≃g x) (f≃g y)))
  where
    prove : (x y : A) (p : x ≃₀ y)
            → (f ≃₁ g)
            → (g ≃₁ h)
            → (f x ≡ h y)
    prove x₁ .x₁ (a≃b refl) (f≃g x₂) (f≃g x₃) with (x₂ x₁ x₁ (a≃b refl)) | (x₃ x₁ x₁ (a≃b refl))
    prove x₁ .x₁ (a≃b refl) (f≃g x₂) (f≃g x₃) | a≃b x₄ | a≃b x₅ with (f x₁) | (g x₁) | (h x₁)
    prove x₁ .x₁ (a≃b refl) (f≃g x₂) (f≃g x₃) | a≃b refl | a≃b refl | p1 | .p1 | .p1 = refl
