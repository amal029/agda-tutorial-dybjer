module Sort where
  open import Sec4
  import Sec2
  postulate _≤_ : {A : Set} →  A → A → Prop
  postulate tot-list : {A : Set} → (a b : A) → (a ≤ b) ∨ (b ≤ a)
  postulate trans-list :  {A : Set} → (a b c : A) → (a ≤ b) → (b ≤ c) → (a ≤ c)

-- XXX: Definition of a list
  data List (A : Set) : Set where
    Nil : List A
    _∷_ : A → List A → List A

-- XXX: definition of an ordered list
  all-ordered-list : {A : Set} → (a : A)
                     → (l : List A)
                     → Prop
  all-ordered-list a Nil = ⊤
  all-ordered-list a (x ∷ l) = (a ≤ x) ∧ all-ordered-list a l

  ordered-list : {A : Set} → List A → Prop
  ordered-list Nil = ⊤
  ordered-list (x ∷ l) = all-ordered-list x l ∧ (ordered-list l)

-- XXX: Inserting elements in the list
  insert-list : {A : Set} → (a : A) → (l : List A) → List A
  insert-list a Nil = a ∷ Nil
  insert-list a (x ∷ l) with (tot-list a x)
  insert-list a (x ∷ l) | ora h = a ∷ (x ∷ l)
  insert-list a (x ∷ l) | orb h = x ∷ (insert-list a l)

  lem1 : {A : Set}
         → (a x : A)
         → (l : List A)
         → (p : all-ordered-list x l)
         → (p1 : a ≤ x)
         → (all-ordered-list a l)
  lem1 a x Nil p p1 = ⋆
  lem1 a x (x₁ ∷ l) (and x₂ x₃) p1 = and (trans-list a x x₁ p1 x₂) (lem1 a x l x₃ p1)


  lem2 : {A : Set} → (x a : A) → (l : List A) → (h : x ≤ a)
         → (p1 : all-ordered-list x l) → (p2 : ordered-list l)
         → (v : ordered-list (insert-list a l))
         → all-ordered-list x (insert-list a l)
  lem2 x a Nil h p1 p3 v = and h ⋆
  lem2 x a (x₁ ∷ l) h p1 p3 v with (tot-list a x₁)
  lem2 x₂ a (x₁ ∷ l) h p1 p3 v | ora x = and h p1
  lem2 x₂ a (x₁ ∷ l) h (and x₃ x₄) (and x₅ x₆) (and x₇ x₈) | orb x = and x₃ (lem2 x₂ a l h x₄ x₆ x₈)

  thm2 : {A : Set}
         → ∀ (a : A)
         → ∀ (l : List A)
         → (p : ordered-list l)
         → (ordered-list (insert-list a l))
  thm2 a Nil p = and ⋆ ⋆
  thm2 a (x ∷ l) p with (tot-list a x)
  thm2 a (x ∷ l) (and x₁ x₂) | ora h = and (and h (lem1 a x l x₁ h)) (and x₁ x₂)
  thm2 a (x ∷ l) (and x₁ x₂) | orb h =
                                   let v = (thm2 a l x₂)
                                   in
                                   and (lem2 x a l h x₁ x₂ v) v

-- XXX: append lists
  _++_ : {A : Set} → (l : List A) → (m : List A) → List A
  Nil ++ m = m
  (x ∷ l) ++ m = x ∷ (l ++ m)

-- XXX: Length of a list
  length : {A : Set} → (l : List A) → Sec2.ℕ
  length Nil = Sec2.Z
  length (x ∷ l) = Sec2.S (length l)


-- XXX: reverse of a list
  rev : {A : Set} → (List A) → (List A)
  rev Nil = Nil
  rev (x ∷ l) = (rev l) ++ (x ∷ Nil)

-- XXX: Theorem on length of lists
  thm : {A : Set} → (l : List A) → (m : List A) → ((length l) Sec2.+ (length m) Sec2.≡ length (l ++ m))
  thm Nil m = Sec2.refl
  thm (x ∷ l) m =
                let
                  xx = thm l m
                in
                Sec2.cong xx

  cong : {A : Set} → (x : A) → (l m : List A) → (l Sec2.≡ m)
         → (x ∷ l) Sec2.≡ (x ∷ m)
  cong x l .l Sec2.refl = Sec2.refl

  cong2 : {A : Set} → (l m q : List A) → (l Sec2.≡ m)
          → (l ++ q) Sec2.≡ (m ++ q)
  cong2 l .l q Sec2.refl = Sec2.refl

  ++-lem : {A : Set} → (l : List A) → ((l ++ Nil) Sec2.≡ l)
  ++-lem Nil = Sec2.refl
  ++-lem (x ∷ l) = cong x (l ++ Nil) l (++-lem l)

  assoc : {A : Set} → (l m q : List A)
          → l ++ (m ++ q) Sec2.≡ (l ++ m) ++ q 
  assoc Nil m q = Sec2.refl
  assoc (x ∷ l) m q = cong x (l ++ (m ++ q)) ((l ++ m) ++ q) (assoc l m q)

  rev-lem : {A : Set} → ∀ (l m : List A)
            → rev (l ++ m) Sec2.≡ (rev m) ++ (rev l)
  rev-lem Nil m rewrite
                ++-lem (rev m) = Sec2.refl
  rev-lem (x ∷ l) m rewrite
                    assoc (rev m) (rev l) (x ∷ Nil)
                    = let p = rev-lem l m in
                      cong2 (rev (l ++ m)) (rev m ++ rev l) (x ∷ Nil) p

-- XXX: Involution of reversal of lists
  rev-involute : {A : Set} → (l : List A) → l Sec2.≡ (rev (rev l))
  rev-involute Nil = Sec2.refl
  rev-involute (x ∷ l) rewrite 
                       rev-lem (rev l) (x ∷ Nil)
                       = cong x l (rev (rev l)) (rev-involute l)

