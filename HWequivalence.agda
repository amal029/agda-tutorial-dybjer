module HWequivalence where
open import Sec4

data Bool : Set where
  T : Bool
  F : Bool

-- AND
_&_ : Bool → Bool → Bool
T & T = T
T & F = F
F & _ = F

-- OR
_||_ : Bool → Bool → Bool
T || _ = T
F || T = T
F || F = F

-- NOT
!_ : Bool → Bool
! T = F
! F = T

infixr 50 !_
infixr 60 _&_
infixr 70 _||_

-- A 1-bit adder
bit-adder-spec : Bool → Bool → Bool → Bool
bit-adder-spec A B C = (A & (! B) & (! C))
      || ((! A) & B & C)
      || ((! A) & (! B) & C)
      || (A & B & C)
      &
      (A & B
      || (A & C)
      || (B & C))

bit-adder-imp : Bool → Bool → Bool → Bool
bit-adder-imp A B C = X & Y
  where
  u : Bool
  u = (A & (! B))
      || ((! A) & B)
  v : Bool
  v = u & C
  w : Bool
  w = A & B
  X : Bool
  X = (u & (! C))
      || ((! u) & C)
  Y : Bool
  Y = w || v

infix 4 _≡_
data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x
{-# BUILTIN EQUALITY _≡_  #-}
{-# BUILTIN REFL     refl #-}

data _≃_ {A : Set} (f : A → A) (g : A → A) : Set where
  f≃g : ((x y : A) → (x ≡ y) → (f x ≡ g y)) → f ≃ g

-- Prove equivalence of specification and implementation using
-- ≃ data type.
equivalence-spec-imp : ∀ (A B : Bool) → (bit-adder-spec A B) ≃ (bit-adder-imp A B)
equivalence-spec-imp A B = f≃g (λ x y x₁ → prove x y x₁)
  where
  pr1 : (x y : Bool) → (bit-adder-spec x y T) ≡ (bit-adder-imp x y T)
  pr1 T T = refl
  pr1 T F = refl
  pr1 F T = refl
  pr1 F F = refl


  pr2 : (x y : Bool) → (bit-adder-spec x y F) ≡ (bit-adder-imp x y F)
  pr2 T T = refl
  pr2 T F = refl
  pr2 F T = refl
  pr2 F F = refl

  prove : (x y : Bool) → (p : x ≡ y) → (bit-adder-spec A B x) ≡ (bit-adder-imp A B y)
  prove T .T refl = pr1 A B
  prove F .F refl = pr2 A B
