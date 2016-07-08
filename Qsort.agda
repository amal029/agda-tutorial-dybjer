module Qsort where
open import Sec4                -- The module with definition of propositions
import Sec2

-- postulate needed for ≤ on A
postulate leq : {A : Set} → A → A → Prop
postulate geq : {A : Set} → A → A → Prop
postulate tot-list : {A : Set} → (a b : A) → (leq a  b) ∨ (leq b a)
postulate trans-list :  {A : Set} → (a b c : A) → (leq a b) → (leq b c) → (leq a c)

{-
  Definition of a list
-}
data List (A : Set) : Set where
  []  : List A                  -- Empty list
  _∷_ : A → List A → List A     -- Cons


-- Proposition stating what is a non empty list
nelist : {A : Set} → (List A) → Prop
nelist [] = ⊥
nelist (x ∷ x₁) = ⊤


-- Head function that only works on non empty list
head : {A : Set} → (l : List A) → (p : nelist l) → A
head [] ()                      -- This can never happen
head (x ∷ _) ⋆ = x              -- This is the head of the list

-- The tail of the list only works on non empty list
tail : {A : Set} → (l : List A) → (p : nelist l) → (List A)
tail [] ()
tail (_ ∷ l) ⋆ = l

data Bool : Set where
  True  : Bool
  False : Bool

data ℕ : Set where
  Z : ℕ
  S : ℕ → ℕ

-- Addition of natural numbers
_+_ : ℕ → ℕ → ℕ
Z + y = y
S x + y = S (x + y)

-- Relation on natural numbers
_≤_ : ℕ → ℕ → Prop
Z ≤ Z = ⊤
Z ≤ (S y) = ⊤
S x ≤ Z = ⊥
S x ≤ S y = x ≤ y


-- {-# BUILTIN NATURAL ℕ #-}
-- {-# BUILTIN BOOL Bool #-}

-- ≤ is reflexive
≤-ref : ∀ (x : ℕ) → (x ≤ x) → (x ≤ x)
≤-ref x = λ z → z

-- ≤ is not symmetric
-- ≤-sym : ∀ (x y : ℕ) → (x ≤ y) → (y ≤ x)
-- ≤-sym Z Z p = ⋆
-- ≤-sym Z (S y) ⋆ = {!!}
-- ≤-sym (S x) Z ()
-- ≤-sym (S x) (S y) p = ≤-sym x y p

-- ≤ is transitive
≤-trans : ∀ (x y z : ℕ) → (x ≤ y) → (y ≤ z) → (x ≤ z)
≤-trans Z Z Z p1 p2 = ⋆
≤-trans Z Z (S z) p1 p2 = ⋆
≤-trans Z (S y) Z p1 p2 = ⋆
≤-trans Z (S y) (S z) p1 p2 = ⋆
≤-trans (S x) Z z () p2
≤-trans (S x) (S y) Z p1 ()
≤-trans (S x) (S y) (S z) p1 p2 = ≤-trans x y z p1 p2

-- length of a list 
length : {A : Set} → (List A) → ℕ
length [] = Z
length (x ∷ l) = (S Z) + (length l)

-- filter' on a list
filter' : {A : Set} → (A → Bool) → (l : List A)
         → List A
filter' f [] = []
filter' f (x ∷ l) with (f x)
filter' f (x ∷ l) | True = (x ∷ (filter' f l))
filter' f (x ∷ l) | False = filter' f l

≤-cong : ∀ (x y : ℕ) → (x ≤ y) → (x ≤ (S y))
≤-cong Z y p = ⋆
≤-cong (S x) Z ()
≤-cong (S x) (S y) p = ≤-cong x y p

thm-filter' : {A : Set} → (l : List A) → (f : A → Bool) → length (filter' f l) ≤ S (length l)
thm-filter' [] f = ⋆
thm-filter' (x ∷ l) f with (f x) 
thm-filter' (x ∷ l) f | True = thm-filter' l f
thm-filter' (x ∷ l) f | False = ≤-cong (length (filter' f l)) (S (length l)) (thm-filter' l  f)

filter : {A : Set} → (A → Bool) → (l : List A)
         → Exists (List A) (λ l' → (length l') ≤ (length l))
filter f [] = [ [] , ⋆ ]
filter f (x ∷ l) = [ filter' f l , thm-filter' l f ]

_++_ : {A : Set} → (l : List A) → (l' : List A) → (List A)
[] ++ l' = l'
(x ∷ l) ++ l' = (x ∷ (l ++ l'))

leq-nat : ℕ → ℕ → Bool
leq-nat Z  _ = True
leq-nat (S n) Z = False
leq-nat (S n) (S m) = leq-nat n m

_<_ : ℕ → ℕ → Bool
Z < (S _) = True
Z < Z = False
(S n) < (S m) = n < m
(S n) < Z = False

_>_ : ℕ → ℕ → Bool
m > n = n < m

-- The sorting algorithm
qsort' : (l : List ℕ) → List ℕ
qsort' [] = []
qsort' (x ∷ l) =
              let
                left = qsort' (elim1-exists (filter (leq-nat x) l))
                right = qsort' (elim1-exists (filter ((_>_) x) l))
              in
              (left ++ (x ∷ [])) ++ right


-- XXX: definition of an sorted list
all-sorted-list : {A : Set} → (a : A)
                   → (l : List A)
                   → Prop
all-sorted-list a [] = ⊤
all-sorted-list a (x ∷ l) = leq a x ∧ (all-sorted-list a l)

sorted-list : {A : Set} → List A → Prop
sorted-list [] = ⊤
sorted-list (x ∷ l) = (all-sorted-list x l) ∧ (sorted-list l)
