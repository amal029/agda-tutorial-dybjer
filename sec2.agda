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
_≡_ : ℕ → ℕ → Bool
x ≡ y = (x ≥ y) & (x ≤ y)

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

head : {A : Set} → (x : List A) → So ((length x) ≥ 1) → A
head [] ()
head (x ∷ x₁) _ = x

tail : {A : Set} → (x : List A) → So ((length x) ≥ 1) → List A
tail [] ()
tail (x ∷ x₁) _ = x₁


if_then_else_ : {A : Set} → Bool → A → A → A
if T then x else _ = x
if F then _ else y = y
  

filter : {A : Set} → (A → Bool) → List A → List A
filter cmp [] = []
filter cmp (x ∷ x₁) = if (cmp x) 
                      then x ∷ (filter cmp x₁)
                      else filter cmp x₁

foldl : {A : Set} → (A → A → A) → List A → A → A
foldl _ [] y = y
foldl f (x ∷ x₁) y = foldl f x₁ (f x y)

test2 : ℕ
test2 = head (2 ∷ []) ok

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


zip : {A B : Set} → (xs : List A) → (ys : List B) → So ((length xs) ≡ (length ys)) → List (A Π B)
zip [] [] k = []
zip [] (x ∷ ys) ()
zip (x ∷ xs) [] ()
zip (x ∷ xs) (y ∷ ys) k = < x , y > ∷ zip xs ys k

-- TODO: Write unzip later on
unzip : {A B : Set} → List (A Π B) → (List A Π List B)
unzip xs = {!!}

test5 : List (ℕ Π ℕ)
test5 = zip ((1 ∷ [])) (2 ∷ []) ok
