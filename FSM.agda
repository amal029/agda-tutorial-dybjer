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

theorem : runFSM 10 (< A , (record { x = zero ; δ = 1 ; k = zero }) >) ≡ < DONE ,
                           record { x = 10 ; δ = 1 ; k = 5 } >
theorem  = refl


-- invariant when in DONE state, X ≥ 10
invariant : (Loc Π Values) → Prop
invariant < A , record { x = x ; δ = δ ; k = k } > = ⊥
invariant < DONE , record { x = x ; δ = δ ; k = k } > =  x ≥ 10

thm : invariant (runFSM 5 (< A , (record { x = zero ; δ = 1 ; k = zero }) >))
thm = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))


-- Example of arithexpr as a relation
data aexp : Set where
  ANum : ∀ (n : ℕ) → aexp
  APlus : aexp → aexp → aexp
  AMult : aexp → aexp → aexp


aeval : aexp → ℕ
aeval (ANum n) = n
aeval (APlus a₁ a₂) = (aeval a₁) + (aeval a₂)
aeval (AMult n₁ n₂) = (aeval n₁) * (aeval n₂)


-- Now as a relation
data _⇓_ : aexp → ℕ → Prop where
  ANumR : ∀ (n : ℕ) → ANum n ⇓ n
  APlusR : ∀ (n₁ n₂ : ℕ) → ∀ (a₁ a₂ : aexp)
           → (a₁ ⇓ n₁) → (a₂ ⇓ n₂)
           → (APlus a₁ a₂) ⇓ (n₁ + n₂)
  AMultR : ∀ (n₁ n₂ : ℕ) → ∀ (a₁ a₂ : aexp)
           → (a₁ ⇓ n₁) → (a₂ ⇓ n₂)
           → (AMult a₁ a₂) ⇓ (n₁ * n₂)

th : (APlus (ANum 10) (ANum 10)) ⇓ 20
th = APlusR
       (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))
       (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))
       (ANum
        (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))
       (ANum
        (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))
       (ANumR
        (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))
       (ANumR
        (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))

t : (a : aexp) → ∀ (p : ℕ) → (aeval a ≡ p) → (a ⇓ p)
t (ANum n) .n refl = ANumR n
t (APlus a a₁) .(aeval a + aeval a₁) refl = APlusR (aeval a) (aeval a₁) a a₁ (t a (aeval a) refl)
                                            (t a₁ (aeval a₁) refl)
t (AMult a a₁) .(aeval a * aeval a₁) refl = AMultR (aeval a) (aeval a₁) a a₁ (t a (aeval a) refl)
                                            (t a₁ (aeval a₁) refl)

pr1 : ∀ (a b : aexp) → ∀ (n1 n2 : ℕ) → (p1 : a ⇓ n1) → (p2 : b ⇓ n2) → ANum (aeval a + aeval b) ⇓ (n1 + n2)
pr1 a b n1 n2 p1 p2 = {!!}

tt : (a : aexp) → (n : ℕ) → (a ⇓ n) → (aeval a ≡ n)
tt (ANum n₁) .n₁ (ANumR .n₁) = refl
tt (APlus a a₁) .(n₁ + n₂) (APlusR n₁ n₂ .a .a₁ p p₁) with tt a n₁ p | tt a₁ n₂ p₁
tt (APlus a a₁) .(aeval a + aeval a₁) (APlusR .(aeval a) .(aeval a₁) .a .a₁ p p₁) | refl | refl = refl
tt (AMult a a₁) .(n₁ * n₂) (AMultR n₁ n₂ .a .a₁ p p₁) with tt a n₁ p | tt a₁ n₂ p₁
tt (AMult a a₁) .(aeval a * aeval a₁) (AMultR .(aeval a) .(aeval a₁) .a .a₁ p p₁) | refl | refl = refl
