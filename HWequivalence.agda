module Hwequivalence where

open import Relation.Binary.PropositionalEquality
open import Data.Bool

-- A 1-bit adder
bit-adder-spec : Bool → Bool → Bool → Bool
bit-adder-spec A B C = X ∧ Y
  where
  X : Bool
  X = (A ∧ not B ∧ not C)
      ∨
      (not A ∧ B ∧ not C)
      ∨
      (not A ∧ not B ∧ C)
      ∨
      (A ∧ B ∧ C)

  Y : Bool
  Y = (A ∧ B)
      ∨
      (A ∧ C)
      ∨
      (B ∧ C)

bit-adder-imp : Bool → Bool → Bool → Bool
bit-adder-imp A B C = X ∧ Y
  where
  u : Bool
  u = (A ∧ not B)
      ∨
      (not A ∧ B)
  v : Bool
  v = u ∧ C
  w : Bool
  w = A ∧ B
  X : Bool
  X = (u ∧ not C)
      ∨
      (not u ∧ C)
  Y : Bool
  Y = (w ∨ v)

data _≃_ {A : Set} (f : A → A) (g : A → A) : Set where
  f≃g : ((x y : A) → (x ≡ y) → (f x ≡ g y)) → f ≃ g

-- Prove equivalence of specification and implementation using
-- ≃ data type.
equivalence-spec-imp : ∀ (A B : Bool) → (bit-adder-spec A B) ≃ (bit-adder-imp A B)
equivalence-spec-imp A B = f≃g (λ x y x₁ → prove x y x₁)
  where
  pr1 : (x y : Bool) → (bit-adder-spec x y true) ≡ (bit-adder-imp x y true)
  pr1 true true = refl
  pr1 true false = refl
  pr1 false true = refl
  pr1 false false = refl


  pr2 : (x y : Bool) → (bit-adder-spec x y false) ≡ (bit-adder-imp x y false)
  pr2 true true = refl
  pr2 true false = refl
  pr2 false true = refl
  pr2 false false = refl

  prove : (x y : Bool) → (p : x ≡ y) → (bit-adder-spec A B x) ≡ (bit-adder-imp A B y)
  prove true .true refl = pr1 A B
  prove false .false refl = pr2 A B
