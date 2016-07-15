module ExCoinduction where


open import Coinduction
open import Relation.Binary.PropositionalEquality
open import Data.Stream
open import Data.Nat
open import Data.Bool

data Loc : Set where
  A : Loc
  DONE : Loc

record Values : Set where
  field
    x : ℕ
    δ : ℕ
    k : ℕ

data _Π_ (A B : Set) : Set where
  <_,_> : (a : Loc) → (b : Values) →  A Π B

-- The computation of x in the state
-- The state machine step function

funₓ : ℕ → ℕ → ℕ → ℕ
funₓ x slope δ = x + δ * slope

step : (Loc Π Values) → (Loc Π Values)
step < A , b > with (X >= 10)
 where
 _>=_ : ℕ → ℕ → Bool
 zero >= zero = true
 zero >= suc y = false
 suc x >= zero = false
 suc x >= suc y = x >= y

 _==_ : ℕ → ℕ → Bool
 zero == zero = true
 zero == suc y = false
 suc x == zero = false
 suc x == suc y = x == y

 X : ℕ
 X = funₓ (Values.x b) 1 (Values.δ b)
step < A , b > | false = < A , record { x = X; δ = Values.δ b ; k = Values.k b + 1 } >
 where
 X : ℕ
 X = funₓ (Values.x b) 1 (Values.δ b)
step < A , b > | true = < DONE , record { x = X; δ = Values.δ b ; k = Values.k b + 1 } >
 where
 X : ℕ
 X = funₓ (Values.x b) 1 (Values.δ b)

step < DONE , b > = < DONE , b > -- Just remain in this state forever

-- Make a stream of runFSM
-- 
f' : ∀ st → Stream (Loc Π Values)
f' st = st ∷ ♯ (f' (step st))
from : Stream (Loc Π Values)
from =  f' (< A , (record { x = zero ; δ = 1 ; k = zero }) >)

thm : from ≈ from 
thm = refl ∷ ♯ (refl ∷ (♯ (refl ∷ (♯ (refl ∷ (♯ (refl ∷ (♯ (refl ∷ (♯ (refl ∷ (♯ (refl ∷ (♯ (refl ∷
             (♯ (refl ∷ ♯ (t'))))))))))))))))))

    where
    y : Stream (Loc Π Values)
    y = f' (< DONE , record { x = 10 ; δ = 1 ; k = 10 } > ) 
    t' : y ≈ y
    t' = refl ∷ (♯ t')
