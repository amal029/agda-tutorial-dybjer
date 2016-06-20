module Sec4 where
-- open import Sec2

-- XXX: The true type
data ⊤ : Set where
  <> : ⊤

-- XXX: The false type
data ⊥ : Set where

-- XXX: Conjunction of Propositions
data _∧_ (A B : Set) : Set where
  and : A → B → (A ∧ B)

-- XXX: The disjuction of propositions
data _∨_ (A B : Set) : Set where
  ora : A → A ∨ B
  orb : B → A ∨ B

-- XXX: implication
data _⇒_ (A B : Set) : Set where
  impl : (f : A → B) → A ⇒ B
  
-- XXX: equivalence
data _⇔_ (A B : Set) : Set where
  eq : (f₁ : A ⇒ B) → (f₂ : B ⇒ A) → A ⇔ B

-- XXX: Negation as a function
¬_ : Set → Set
¬_ A = A → ⊥

-- XXX: Elimination rules as functions

-- XXX: Eliminating ≡>
elim-⇒ : {A B : Set} → (f₁ : A ⇒ B) → A → B
elim-⇒ (impl f) x = f x

elim1-⇔ : {A B : Set} → (A ⇔ B) → A → B
elim1-⇔ (eq (impl f) (impl f₁)) = λ x → f x
elim2-⇔ : {A B : Set} → (A ⇔ B) → B → A
elim2-⇔ (eq (impl f) (impl f₁)) = λ x → f₁ x


-- XXX: Eliminating disjunction
elim-∨ : {A B C : Set} → (A ∨ B) → (A → C) → (B → C) → C
elim-∨ (ora x) f₁ _ = f₁ x
elim-∨ (orb x) _ f₂ = f₂ x

-- XXX: Eliminating conjunction
elim1-∧ : {A B : Set} → (A ∧ B) → A
elim1-∧ (and x x₁) = x
elim2-∧ : {A B : Set} → (A ∧ B) → B
elim2-∧ (and x x₁) = x₁

-- TODO: Example of proofs of tautology
-- XXX: Easy one
ex1 : {A B : Set} → ((A ⇒ B) ∧ (B ⇒ A)) ⇔ (A ⇔ B)
ex1 {A} {B} =
        eq
        (impl (λ x →
          let x1 = elim1-∧ x
              x2 = elim2-∧ x
          in
          eq (impl (λ x₁ → elim-⇒ x1 x₁))
             (impl (λ x₁ → elim-⇒ x2 x₁))))

        (impl (λ x →
                   let x1 = elim1-⇔ x
                       x2 = elim2-⇔ x
                   in
                   and
                   (impl (λ x₁ → x1 x₁))
                   (impl (λ x₁ → x2 x₁))))

-- XXX: Transitivity
transitive : {A B C : Set} → ((A ⇒ B) ∧ (B ⇒ C)) ⇒ (A ⇒ C)
transitive = impl (λ x →
           let x1 = elim1-∧ x
               x2 = elim2-∧ x
           in
           impl (λ x₁ →
                      let xx1 = elim-⇒ x1 x₁
                          xx2 = elim-⇒ x2 xx1
                      in
                      xx2))

-- XXX: Transitivity in the function space of Agda itself. Equivalent to
-- the above one.
trans : {A B C : Set} → ((A → B) ∧ (B → C)) → (A → C)
trans (and x1 x2) z = let t = x1 z
                          t1 = x2 t
                      in t1

-- XXX: Moving ∧ into Agda's space. Equivalent to transitivity and trans
-- above.
trans' : {A B C : Set} → (A → B) → (B → C) → (A → C)
trans' x y = λ z → y (x z)


-- XXX: absorption law 
absorption : {P Q : Set} → (P ∨ (P ∧ Q)) ⇔ P
absorption {p} {q} =
               eq
               (impl (λ x → let x1 = elim-∨ x (λ p → p) (λ y → elim1-∧ y) in x1))
               (impl (λ x → ora x))

-- XXX: commutative
commute : {P Q : Set} → (P ∧ Q) ⇔ (Q ∧ P)
commute = eq (impl (λ x → and (elim2-∧ x) (elim1-∧ x))) (impl (λ x → and (elim2-∧ x) (elim1-∧ x)))

-- XXX: associative 
associative : {P Q R : Set} → ((P ∧ Q) ∧ R) ⇔ (P ∧ (Q ∧ R))
associative  = eq
               (impl (λ x →
                        let x1 = elim1-∧ x
                            x2 = elim1-∧ x1
                            x3 = elim2-∧ x1
                        in
                        and x2 (and x3 (elim2-∧ x))))
               (impl (λ x →
                        let x1 = elim2-∧ x
                        in
                        and (and (elim1-∧ x) (elim1-∧ x1)) (elim2-∧ x1)))

-- XXX: Axiom of choice one way
C-⇒ : {P : Set} → (P ∨ (¬ P)) ⇒ ⊤
C-⇒ = impl (λ _ → <>)

-- XXX: The proper Axiom of choice
C-⇔ : {P : Set} → (x : P ∨ (¬ P)) → (P ∨ (¬ P)) ⇔ ⊤
C-⇔ x = eq
      (impl (λ _ → <>))
      -- XXX: The following proof is impossible todo
      -- Goal: .P ∨ (¬ .P)
      -- ————————————————————————————————————————————————————————————
      -- x  : ⊤
      -- .P : Set
      (impl (λ _ → x)) -- XXX: We do not have any proof object of P on
                          -- the right hand side. This is the difference
                          -- between constructive logic, and classical
                          -- logic. I need an explicit proof object of
                          -- type P ∨ ¬ P (x in the example above) to
                          -- prove the axiom of choice.

distributive : {P Q R : Set} → (P ∧ (Q ∨ R)) ⇔ ((P ∧ Q) ∨ (P ∧ R))
distributive =
               eq
               (impl (λ x →
                        let p = elim1-∧ x
                            x2 = elim2-∧ x
                            x3 = elim-∨ x2 (λ q → {!!}) (λ r → {!!})
                        in
                        {!!}))
               (impl (λ x →
                        let x1 = elim-∨ x (λ l → elim1-∧ l) (λ r → elim1-∧ r)
                            x2 = elim-∨ x (λ l → {!!}) (λ r → {!!})
                        in
                        and x1 (orb {!!})))
