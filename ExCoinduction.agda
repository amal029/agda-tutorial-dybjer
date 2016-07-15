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
from : (st : (Loc Π Values)) → Stream (Loc Π Values)
from st = st ∷ (♯ from (step st))

-- Trivial proof.
thm : ∀ (st : (Loc Π Values)) →  from st ≈ from st
thm st = refl ∷ ♯ thm (step st)
