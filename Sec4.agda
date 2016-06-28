module Sec4 where
-- open import Sec2

Prop : Set₁
Prop = Set

-- XXX: The true type
data ⊤ : Prop where
  <> : ⊤

-- XXX: The false type
data ⊥ : Prop where

-- XXX: Conjunction of Propositions
data _∧_ (A B : Prop) : Prop where
  and : A → B → (A ∧ B)

-- XXX: The disjuction of propositions
data _∨_ (A B : Prop) : Prop where
  ora : A → A ∨ B
  orb : B → A ∨ B

-- XXX: implication
data _⇒_ (A B : Prop) : Prop where
  impl : (f : A → B) → A ⇒ B
  
-- XXX: equivalence
data _⇔_ (A B : Prop) : Prop where
  eq : (f₁ : A ⇒ B) → (f₂ : B ⇒ A) → A ⇔ B

-- XXX: Negation as a function
data ¬_ (A : Prop) : Prop where
  neg : A ⇒ ⊥ → (¬ A)

-- XXX: Elimination rules as functions

-- XXX: Eliminating ≡>
elim-⇒ : {A B : Prop} → (f₁ : A ⇒ B) → A → B
elim-⇒ (impl f) x = f x

elim1-⇔ : {A B : Prop} → (A ⇔ B) → A → B
elim1-⇔ (eq (impl f) (impl f₁)) = λ x → f x
elim2-⇔ : {A B : Prop} → (A ⇔ B) → B → A
elim2-⇔ (eq (impl f) (impl f₁)) = λ x → f₁ x


-- XXX: Eliminating disjunction
elim-∨ : {A B C : Prop} → (A ∨ B) → (A → C) → (B → C) → C
elim-∨ (ora x) f₁ _ = f₁ x
elim-∨ (orb x) _ f₂ = f₂ x

-- XXX: Eliminating conjuction
elim1-∧ : {A B : Prop} → (A ∧ B) → A
elim1-∧ (and x x₁) = x
elim2-∧ : {A B : Prop} → (A ∧ B) → B
elim2-∧ (and x x₁) = x₁

-- TODO: Example of proofs of tautology
-- XXX: Easy one
ex1 : {A B : Prop} → ((A ⇒ B) ∧ (B ⇒ A)) ⇔ (A ⇔ B)
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
ex2 : {A B C : Prop} → ((A ⇒ B) ∧ (B ⇒ C)) ⇒ (A ⇒ C)
ex2 = impl (λ x →
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
absorption : {P Q : Prop} → (P ∨ (P ∧ Q)) ⇔ P
absorption {p} {q} =
               eq
               (impl (λ x → let x1 = elim-∨ x (λ p → p) (λ y → elim1-∧ y) in x1))
               (impl (λ x → ora x))

-- XXX: commutativity
commute : {P Q : Prop} → (P ∧ Q) ⇔ (Q ∧ P)
commute = eq (impl (λ x → and (elim2-∧ x) (elim1-∧ x))) (impl (λ x → and (elim2-∧ x) (elim1-∧ x)))

-- XXX: associativity 
associative : {P Q R : Prop} → ((P ∧ Q) ∧ R) ⇔ (P ∧ (Q ∧ R))
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

elim-neg : {A : Prop} → A → (¬ A) → ⊥
elim-neg y (neg x) = elim-⇒ x y

-- XXX: A ⇒ ¬¬ A
f : {A : Prop} → A ⇒ (¬ (¬ A))
f = impl (λ x → neg (impl (λ x₁ → elim-neg x x₁)))

-- XXX: Axiom of choice one way
C-⇒ : {P : Prop} → (P ∨ (¬ P)) ⇒ ⊤
C-⇒ = impl (λ _ → <>)

-- XXX: The proper Axiom of choice
-- C-⇔ : {P : Prop} → (P ∨ (¬ P)) ⇔ ⊤
-- C-⇔ = eq
--       (impl (λ _ → <>))
--       -- XXX: The following proof is impossible todo
--       -- Goal: .P ∨ (¬ .P)
--       -- ————————————————————————————————————————————————————————————
--       -- x  : ⊤
--       -- .P : Prop
--       (impl (λ x → {!!})) -- XXX: We do not have any proof object of P
--                           -- on the right hand side. This is the
--                           -- difference between constructive logic, and
--                           -- classical logic.

distributive : {P Q R : Prop} → (P ∧ (Q ∨ R)) ⇔ ((P ∧ Q) ∨ (P ∧ R))
distributive =
               eq
               (impl (λ x →
                        let p = elim1-∧ x
                            x2 = elim2-∧ x
                            x3 = elim-∨ x2 (λ q → q) _ 
                        in
                        ora (and p x3)))
               (impl (λ x →
                        let x1 = elim-∨ x (λ l → elim1-∧ l) (λ r → elim1-∧ r)
                            x2 = elim-∨ x _ (λ r → elim2-∧ r)
                        in
                        and x1 (orb x2)))


-- XXX: Predicate logic
-- XXX: For all introduction
data ForAll (A : Set) (B : A → Prop) : Prop where
  dfun : ((x : A) → (B x)) → (ForAll A B)

elim-ForAll : {A : Set} → (x : A) → {B : A → Prop} → (ForAll A B) → (B x)
elim-ForAll x (dfun x₁) = x₁ x

-- XXX: Exists
data Exists (A : Set) (B : A → Prop) : Prop where
  [_,_] : (x : A) → (B x) → Exists A B

elim1-exists : {A : Prop} → {B : A → Prop} → (Exists A B) → A
elim1-exists [ x , _ ] = x

elim2-exists : {A : Prop} → {B : A → Prop} → (p : Exists A B) → (B (elim1-exists p))
elim2-exists [ _ , x ] = x

-- TODO: Proofs in predicate logic
pex0 : {X : Set} → {P : X → Prop} → (Exists X (λ (x : X) → (¬ P x))) ⇒ (¬ (ForAll X P))
pex0 = {!!}

pex2 : {X Y : Set} → {P : X → Y → Prop} → (Exists Y (λ (y : Y) → (ForAll X (λ (x : X) → P x y))))
                                        ⇒ (ForAll X (λ (x : X) → (Exists Y (λ (y : Y) → P x y))))
pex2 = {!!}

-- TODO: Tautology in FOL predicate logic
ptau : {V B : Set} → {A : V → Prop} → (ForAll V (λ (x : V) → (A x) ⇒ B))
                                    ⇔ (Exists V A ⇒ B)
ptau = {!!}
