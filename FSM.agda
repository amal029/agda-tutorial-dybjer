module FSM where
open import Sec4
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Bool
-- open import Data.Rational
-- open import Data.Integer
-- open import Relation.Nullary.Decidable

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
step : (Loc Π Values) → (Loc Π Values)
step < A , b > =
  if (X >= 10)
  then
    < DONE , record { x = X; δ = Values.δ b ; k = Values.k b + 1 } >
  else
    < A , record { x = X; δ = Values.δ b ; k = Values.k b + 1 } >
 where
 funₓ : ℕ → ℕ → ℕ → ℕ           -- slope = 1 here!
 funₓ x k δ = x + δ * k

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
 X = funₓ (Values.x b) (Values.k b) (Values.δ b)

step < DONE , b > = < DONE , b > -- Just remain in this state forever

runFSM : (n : ℕ) → (st : (Loc Π Values)) → (Loc Π Values)
runFSM zero st = st
runFSM (suc n) st = runFSM n (step st)

theorem : runFSM 10 (< A , (record { x = zero ; δ = 1 ; k = zero }) >) ≡ < DONE , record { x = 10 ; δ = 1 ; k = 5 } >
theorem  = refl

-- invariant when in DONE state, X ≥ 10
invariant : (Loc Π Values) → Prop
invariant < A , record { x = x ; δ = δ ; k = k } > = ⊥
invariant < DONE , record { x = x ; δ = δ ; k = k } > =  x ≥ 10

thm : invariant (runFSM 5 (< A , (record { x = zero ; δ = 1 ; k = zero }) >))
thm = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))
