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
≤-ref _ y = y

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

-- append two lists
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
-- The trick here is that we are reducing qsort on "n"
qsort' : ∀ (n : ℕ) → ∀ (l : List ℕ) → (p : (length l) ≤ n) → (List ℕ)
qsort' Z [] p = []
qsort' Z (x ∷ l) ()
qsort' (S n) [] p = []
qsort' (S n) (x ∷ l) p =
                       let
                         ll = (filter (leq-nat x) l)
                         rr = (filter ((_>_) x) l)
                         pl = elim2-exists ll
                         pr = elim2-exists rr
                         left = qsort' n (elim1-exists ll) (≤-trans (length (elim1-exists ll)) (length l) n pl p)
                         right = qsort' n (elim1-exists rr) (≤-trans (length (elim1-exists rr)) (length l) n pr p)
                       in
                       (left ++ (x ∷ [])) ++ right


l' : {A : Set} → (l : List A) → (length l ≤ length l)
l' [] = ⋆
l' (x ∷ l) = l' l

qsort : ∀ (l : List ℕ) → List ℕ
qsort l = qsort' (length l) l (l' l)

-- XXX: definition of an sorted list
all-sorted-list : {A : Set} → (a : A)
                   → (l : List A)
                   → Prop
all-sorted-list a [] = ⊤
all-sorted-list a (x ∷ l) = leq a x ∧ (all-sorted-list a l)

sorted-list : {A : Set} → List A → Prop
sorted-list [] = ⊤
sorted-list (x ∷ l) = (all-sorted-list x l) ∧ (sorted-list l)


lem-qsort' : (x₁ : ℕ) → (l : List ℕ) → sorted-list
      ((qsort' (S (length l)) (filter' (leq-nat x₁) l)
        (≤-trans (length (filter' (leq-nat x₁) l)) (S (length l))
         (S (length l)) (thm-filter' l (leq-nat x₁)) (l' l))
        ++ (x₁ ∷ []))
       ++
       qsort' (S (length l)) (filter' (_>_ x₁) l)
       (≤-trans (length (filter' (_>_ x₁) l)) (S (length l))
        (S (length l)) (thm-filter' l (_>_ x₁)) (l' l)))
lem-qsort' x [] = and ⋆ ⋆
lem-qsort' x (x₁ ∷ l) = {!!}

lem-qsort : (l : List ℕ) → (x : ℕ) →
  sorted-list
      ((qsort' (length l) (elim1-exists (filter (leq-nat x) l))
        (≤-trans (length (elim1-exists (filter (leq-nat x) l))) (length l)
         (length l) (elim2-exists (filter (leq-nat x) l)) (l' l))
        ++ (x ∷ []))
       ++
       qsort' (length l) (elim1-exists (filter (_>_ x) l))
       (≤-trans (length (elim1-exists (filter (_>_ x) l))) (length l)
        (length l) (elim2-exists (filter (_>_ x) l)) (l' l)))
lem-qsort [] x = and ⋆ ⋆
lem-qsort (x ∷ l) x₁ = lem-qsort' x₁ l

-- Theorem that given a list, qsort will actually sort the list
thm-qsort : ∀ (l : List ℕ) → sorted-list (qsort l)
thm-qsort [] = ⋆
thm-qsort (x ∷ l) = lem-qsort l x 



