module Sec2 where
open import Sec4
data Bool : Set where
  T : Bool
  F : Bool
  

_∣∣_ : Bool → Bool → Bool
_ ∣∣ F = F
_ ∣∣ T = T

_&_ : Bool → Bool → Bool
_ & F = F
F & T = F
T & T = T

_==>_ : Bool → Bool → Bool
F ==> _ = T
T ==> F = F
T ==> T = T


not : Bool -> Bool
not T = F 
not F = T 

data ℕ : Set where
  Z : ℕ
  S : ℕ → ℕ

_+_ : ∀ (m : ℕ) → ∀ (n : ℕ) → ℕ
Z + m = m
(S n) + m = S (n + m)

_*_ : ℕ → ℕ → ℕ
Z * m = Z
(S n) * m = (n * m) + m

{-# BUILTIN NATURAL ℕ #-}
{-# BUILTIN BOOL Bool #-}

_≤_ : ℕ → ℕ → Bool
Z ≤ _ = T
(S n) ≤ Z = F
(S n) ≤ (S m) = n ≤ m

_<_ : ℕ → ℕ → Bool
Z < (S _) = T
Z < Z = F
(S n) < (S m) = n < m
(S n) < Z = F

_≥_ : ℕ → ℕ → Bool
m ≥ n = n ≤ m

_>_ : ℕ → ℕ → Bool
m > n = n < m

-- XXX: == on Nat
_==_ : ℕ → ℕ → Bool
x == y = (x ≥ y) & (x ≤ y)

_-_ : ℕ → ℕ → ℕ
Z - _ = Z
(S n) - Z = (S n)
(S n) - (S m) = n - m


K : {A B : Set} → A → B → A
K x _ = x

SC : {A B C : Set} → (A → B → C) → (A → B) → A → C
SC f g x = f x (g x)

-- XXX: The list type
data List (A : Set) : Set where
  []  : List A 
  _∷_ : A → List A → List A


length : {A : Set} → List A → ℕ
length [] = Z
length (x ∷ m) = 1 + length m

test : List ℕ
test = 2 ∷ (3 ∷ [])

test1 : ℕ
test1 = length test

data So : Bool → Set where
  ok : So T

private head : {A : Set} → (x : List A) → So ((length x) ≥ 1) → A
head [] ()
head (x ∷ x₁) _ = x

private tail : {A : Set} → (x : List A) → So ((length x) ≥ 1) → List A
tail [] ()
tail (x ∷ x₁) _ = x₁


if_then_else_ : {A : Set} → Bool → A → A → A
if T then x else _ = x
if F then _ else y = y
  
private filter : {A : Set} → (A → Bool) → List A → List A
filter cmp [] = []
filter cmp (x ∷ x₁) = if (cmp x) 
                      then x ∷ (filter cmp x₁)
                      else filter cmp x₁

_++_ : {A : Set} →  List A → List A → List A
[] ++ r = r
(x ∷ l) ++ r = x ∷ (l ++ r)

insert : (a : ℕ) → (List ℕ) → (List ℕ)
insert a [] = (a ∷ [])
insert a (x ∷ l) = if (a ≤ x)
                   then (a ∷ (x ∷ l))
                   else (x ∷ (insert a l))

tt2 : List ℕ
tt2 = insert 9 (0 ∷ (8 ∷ []))

private foldl : {A : Set} → (A → A → A) → List A → A → A
foldl _ [] y = y
foldl f (x ∷ x₁) y = foldl f x₁ (f x y)

-- XXX: injective tuple
data _+′_  (A B : Set) : Set where
  inl : (x : A) → A +′ B
  inr : (x : B) → A +′ B

case : {A B C : Set} → (A +′ B) → (f₁ : (A → C)) → (f₂ : (B → C)) → C
case (inl x) f₁ _ = f₁ x
case (inr x) _ f₂ = f₂ x

-- XXX: Proof of transitivity of >
T> : (a b c : ℕ) → So (a > b) → So (b > c) → So (a > c)
T> Z Z Z () y
T> Z Z (S c) () y
T> Z (S b) c () y
T> (S a) Z Z ok ()
T> (S a) Z (S c) ok ()
T> (S a) (S b) Z x y = ok
T> (S a) (S b) (S c) x y = T> a b c x y

-- XXX: Tuple type
data _Π_ (A B : Set) : Set where
  <_,_> : (x : A) → (y : B) → A Π B


private zip : {A B : Set} → (xs : List A) → (ys : List B) → So ((length xs) == (length ys)) → List (A Π B)
zip [] [] k = []
zip [] (x ∷ ys) ()
zip (x ∷ xs) [] ()
zip (x ∷ xs) (y ∷ ys) k = < x , y > ∷ zip xs ys k

-- TODO: Write unzip later on
-- unzip : {A B : Set} → List (A Π B) → (List A Π List B)
-- unzip xs = {!!}

test5 : List (ℕ Π ℕ)
test5 = zip ((1 ∷ [])) (2 ∷ []) ok

infix 4 _≡_
data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x
{-# BUILTIN EQUALITY _≡_  #-}
{-# BUILTIN REFL     refl #-}

-- XXX: Transitivity of ℕ
ℕ-trans : ∀ {x y z : ℕ} → (x ≡ y) → (y ≡ z) → (x ≡ z)
ℕ-trans refl refl = refl

-- XXX: Symmetry of ℕ 
sym : ∀ {x y : ℕ} → (x ≡ y) → (y ≡ x)
sym refl = refl

-- XXX: Congruence of ℕ
cong : ∀ {x y : ℕ} → (x ≡ y) → (1 + x) ≡ (1 + y)
cong refl = refl

plus-z : ∀ (y : ℕ) → ((y + Z) ≡ y)
plus-z Z = refl
plus-z (S y) = cong (plus-z y)

assoc-+ : ∀ (a b c : ℕ) → ((a + b) + c) ≡ (a + (b + c))
assoc-+ Z y z = refl
assoc-+ (S x) y z = cong (assoc-+ x y z)


t1 : ∀ (x y : ℕ) → (x + S y) ≡ S (x + y)
t1 Z y = refl
t1 (S x) y = cong (t1 x y)

-- See this: https://github.com/dvanhorn/play/blob/master/agda/Rewrite.agda
-- for examples of rewrite.
-- Also read: http://agda.readthedocs.io/en/latest/language/with-abstraction.html#generalisation
commute-+ : ∀ (x y : ℕ) → ((x + y) ≡ (y + x))
commute-+ Z y rewrite plus-z y = refl
commute-+ (S x) y rewrite t1 y x = cong (commute-+ x y)

mult-z : ∀ (y : ℕ) → ((y * Z) ≡ Z)
mult-z Z = refl
mult-z (S y) rewrite plus-z (y * Z) = mult-z y

lemma-1 : ∀ {a b : ℕ} → ∀ (n : ℕ) → (a ≡ b) → (n + a ≡ n + b) 
lemma-1 _ refl = refl

c-* : ∀ (m n : ℕ) → (m * S n) ≡ (m * n) + m
c-* Z n rewrite commute-+ (n * Z) Z
                | mult-z n = refl
c-* (S m) n rewrite
            commute-+ (m * S n) (S n)
            | commute-+ ((m * n) + n) (S m)
            | commute-+ m ((m * n) + n)
            | assoc-+ (m * n) n m
            | commute-+  (m * n) (n + m)
            | assoc-+ n m (m * n)
            | commute-+ m (m * n)
            = cong (lemma-1 n (c-* m n))


commute-* : ∀ (m n : ℕ) → (m * n) ≡ (n * m)
commute-* m Z = mult-z m
commute-* m (S n) rewrite c-* m n
                          | commute-+ (m * n) m
                          | commute-+ (n * m) m = lemma-1 m (commute-* m n)

lemma-2 : ∀ (m n x : ℕ) → (m + n) * x ≡ ((m * x) + (n * x))
lemma-2 m n Z rewrite mult-z (m + n)
              | mult-z m
              | mult-z n = refl
lemma-2 m n (S x) rewrite c-* (m + n) x
                  | c-* m x
                  | c-* n x
                  | assoc-+ (m * x) m ((n * x) + n)
                  | commute-+ m ((n * x) + n)
                  | assoc-+ (n * x) n m
                  | commute-+ n m
                  | commute-+ (n * x) (m + n)
                  | commute-+ (m * x) ((m + n) + (n * x))
                  | assoc-+ (m + n) (n * x) (m * x)
                  | commute-+ (m + n) ((n * x) + (m * x))
                  | commute-+ (n * x) (m * x)
                  | commute-+ ((m * x) + (n * x)) (m + n)
                  | commute-+ ((m + n) * x) (m + n) = lemma-1 (m + n) (lemma-2 m n x)

assoc-* : ∀ (a b c : ℕ) → ((a * b) * c) ≡ (a * (b * c)) 
assoc-* Z b c = refl
assoc-* (S a) b c rewrite lemma-2 (a * b) b c
                  | commute-+ ((a * b) * c) (b * c)
                  | commute-+ (a * (b * c)) (b * c) = lemma-1 (b * c) (assoc-* a b c)


distributivity-+-* : ∀ (a b c : ℕ) → (a * (b + c)) ≡ ((a * b) + (a * c))
distributivity-+-* a b c rewrite commute-* a (b + c)
                         | commute-* a b
                         | commute-* a c
                         | lemma-2 b c a = refl

-- XXX: factorial function on naturals
fact : ∀ (x : ℕ) → ℕ
fact Z = (S Z)
fact (S Z) = (S Z)
fact (S x) = x * (fact x)

-- TODO: Relation on ℕ and >
_>⋆_ : ℕ → ℕ → Prop
Z >⋆ Z = ⊥
S x >⋆ Z = ⊤
Z >⋆ S y = ⊥
S x >⋆ S y = x >⋆ y

lem : (m n : ℕ) → (p : n >⋆ Z) → (m + n) >⋆ 0
lem Z n p = p
lem (S m) n p = ⋆

-- XXX: Theorem; factorial of any natural number is > 0
-- XXX: page-124, problem 4.35, Type Theory and functional programming
thm : ∀ (x : ℕ) → (fact x) >⋆ Z
thm Z = ⋆
thm (S Z) = ⋆
thm (S (S x)) = lem (x * fact (S x)) (fact (S x)) (thm (S x))

_<=_ : ∀ (m n : ℕ) → Prop
Z <= n = ⊤
S m <= Z = ⊥
S m <= S n = m <= n

-- symm : ∀ (m n : ℕ) → (p : m <= n) → (n <= m)
-- symm Z Z p = ⋆
-- symm Z (S n) p = {!!}
-- symm (S m) Z p = ⋆
-- symm (S m) (S n) p = symm m n p

transm : ∀ (m n p : ℕ) → (m <= n) → (n <= p) → (m <= p)
transm Z n p p1 p2 = ⋆
transm (S m) Z Z p1 p2 = p1
transm (S m) (S n) Z p1 p2 = p2
transm (S m) Z (S p) () p2 
transm (S m) (S n) (S p) p1 p2 = transm m n p p1 p2

-- Show that 2 + 3 ≡ 3 + 2
eqq : 2 + 3 ≡ 3 + 2
eqq = refl
