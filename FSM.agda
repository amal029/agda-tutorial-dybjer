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

-- Example of state machine as a relation
data State : Set where
  A : ∀ (n : ℕ) → State
  D : ∀ (n : ℕ) → State

private funₓ : ℕ → ℕ → ℕ → ℕ
        funₓ x δ slope = x + δ * slope

data _↓_ : State → State → Prop where
  S1 : ∀ (n : ℕ) → (n < 10) → (A n) ↓ (A (funₓ n 1 1))
  S2 : ∀ (n : ℕ) → (n ≥ 10) → (A n) ↓ (D n)

data fState : State → Prop where
  F : ∀ (n : ℕ) →  (n ≥ 10) →  fState (D n)

data oState : State → Prop where
  O : oState (A 0)

c1 : ∀ (n : ℕ) → (p : (suc n) ≤ 9) → (n ≤ 9)
c1 .0 (s≤s z≤n) = z≤n
c1 .1 (s≤s (s≤s z≤n)) = s≤s z≤n
c1 .2 (s≤s (s≤s (s≤s z≤n))) = s≤s (s≤s z≤n)
c1 .3 (s≤s (s≤s (s≤s (s≤s z≤n)))) = s≤s (s≤s (s≤s z≤n))
c1 .4 (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) = s≤s (s≤s (s≤s (s≤s z≤n)))
c1 .5 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) = s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))
c1 .6 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))
c1 .7 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))) = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))
c1 .8 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))) = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))

y : ∀ (n : ℕ) → (p : n < 10) → (A n) ↓ (A (suc n))
y zero (s≤s p) = S1 zero (s≤s p)
y (suc n) (s≤s p) with (y n (s≤s (c1 n p)))
y (suc n) (s≤s p) | h = c n h
  where
  c : ∀ (a : ℕ) →  (h : (A a) ↓ (A (suc a))) → (A (suc a) ↓ (A (suc (suc a))))
  c a h = {!!} 
  
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

t : ∀ (a : aexp) (p : ℕ) → (aeval a ≡ p) → (a ⇓ p)
t (ANum n) .n refl = ANumR n
t (APlus a a₁) .(aeval a + aeval a₁) refl = APlusR (aeval a) (aeval a₁) a a₁ (t a (aeval a) refl)
                                            (t a₁ (aeval a₁) refl)
t (AMult a a₁) .(aeval a * aeval a₁) refl = AMultR (aeval a) (aeval a₁) a a₁ (t a (aeval a) refl)
                                            (t a₁ (aeval a₁) refl)

tt : ∀ (a : aexp) (n : ℕ) → (a ⇓ n) → (aeval a ≡ n)
tt (ANum n₁) .n₁ (ANumR .n₁) = refl
tt (APlus a a₁) .(n₁ + n₂) (APlusR n₁ n₂ .a .a₁ p p₁) with tt a n₁ p | tt a₁ n₂ p₁
tt (APlus a a₁) .(aeval a + aeval a₁) (APlusR .(aeval a) .(aeval a₁) .a .a₁ p p₁) | refl | refl = refl
tt (AMult a a₁) .(n₁ * n₂) (AMultR n₁ n₂ .a .a₁ p p₁) with tt a n₁ p | tt a₁ n₂ p₁
tt (AMult a a₁) .(aeval a * aeval a₁) (AMultR .(aeval a) .(aeval a₁) .a .a₁ p p₁) | refl | refl = refl
