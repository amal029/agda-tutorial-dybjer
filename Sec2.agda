module Sec2 where
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

_⇒_ : Bool → Bool → Bool
F ⇒ _ = T
T ⇒ F = F
T ⇒ T = T


not : Bool -> Bool
not T = F 
not F = T 

data ℕ : Set where
  Z : ℕ
  S : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
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
private _==_ : ℕ → ℕ → Bool
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
ℕ-trans : {x y z : ℕ} → (x ≡ y) → (y ≡ z) → (x ≡ z)
ℕ-trans refl p2 = p2

-- XXX: Symmetry of ℕ 
sym : {x y : ℕ} → (x ≡ y) → (y ≡ x)
sym refl = refl

-- XXX: Congruence of ℕ
cong : {x y : ℕ} → (x ≡ y) → (1 + x) ≡ (1 + y)
cong refl = refl

plus-z : (y : ℕ) → (y ≡ (y + Z))
plus-z Z = refl
plus-z (S y) = cong (plus-z y)

associativity-N : (a b c : ℕ) → ((a + b) + c) ≡ (a + (b + c))
associativity-N Z y z = refl
associativity-N (S x) y z = cong (associativity-N x y z)

t1 : (x y : ℕ) → (x + S y) ≡ S (x + y)
t1 Z y = refl
t1 (S x) y = cong (t1 x y)

-- See this: https://github.com/dvanhorn/play/blob/master/agda/Rewrite.agda
-- for examples of rewrite.
-- Also read: http://agda.readthedocs.io/en/latest/language/with-abstraction.html#generalisation
commute : (x y : ℕ) → ((x + y) ≡ (y + x))
commute Z y = plus-z y
commute (S x) y rewrite t1 y x = cong (commute x y)
