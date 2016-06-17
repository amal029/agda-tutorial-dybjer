open import Sec2
data Vec (A : Set) : ℕ → Set where
  [] : Vec A Z
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (S n)


head : {A : Set} → {n : ℕ} → Vec A (S n) → A
head (x ∷ vs) = x


tail : {A : Set} → {n : ℕ} → Vec A (S n) → Vec A n
tail (x ∷ vs) = vs

map : {A B : Set} → {n : ℕ} → (f : A → B) → Vec A n → Vec B n
map f [] = []
map f (x ∷ vs) = f x ∷ map f vs

zip : {A B : Set} → {n : ℕ} → Vec A n → Vec B n → Vec (A Π B) n
zip [] [] = []
zip (x ∷ xs) (x₁ ∷ ys) = < x , x₁ > ∷ zip xs ys
