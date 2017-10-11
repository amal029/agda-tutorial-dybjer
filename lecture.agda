open import Sec4

data ℕ : Set where
  Z : ℕ
  S : ℕ → ℕ


-- Now ≥ relation
_≥_ : ∀ (m : ℕ) → ∀ (n : ℕ) → Prop
Z ≥ Z = ⊤
S m ≥ Z = ⊤
Z ≥ S n = ⊥
S m ≥ S n = m ≥ n

-- Example proof
-- eqqr : ((S (S (S Z))) ≥ (S (S Z))) → ((S (S Z)) ≥ (S (S (S Z))))
-- eqqr ()

-- -- Now is ≥ equivalence relation?
-- relfexivity
reflexivity : ∀ (m : ℕ) → (m ≥ m)
reflexivity  Z = ⋆
reflexivity  (S m) = reflexivity m

-- -- -- Now symmetry
-- sym : ∀ (m : ℕ) → ∀ (n : ℕ) → m ≥ n → n ≥ m
-- sym Z Z p = ⋆
-- sym Z (S n) p = ⋆
-- sym (S m) Z ⋆ = {!!}
-- sym (S m) (S n) p = sym m n p

-- -- -- Now transitivity
trans'' : ∀ (m : ℕ) → ∀ (n : ℕ) → ∀ (p : ℕ) → m ≥ n → n ≥ p → m ≥ p
trans'' Z Z p p0 p1 = p1
trans'' Z (S n) p () p1
trans'' (S m) n Z p0 p1 = ⋆
trans'' (S m) Z (S p) p0 ()
trans'' (S m) (S n) (S p) p0 p1 = trans'' m n p p0 p1

-- Given the above three are satisfied, we know that it is an
-- equivalence relation!

-- Now let us try strictly greater than (>)

-- Definition of >
_>_ : ∀ (m : ℕ) → ∀ (n : ℕ) → Prop
Z > Z =  ⊥
Z > S n = ⊥
S m > Z = ⊤
S m > S n = m > n

-- Now let us see of > is an equivalence relation

-- reflixvity of > not possible!
-- refl-> : ∀ (m : ℕ) → m > m
-- refl-> Z = {!!}
-- refl-> (S m) = refl-> m

-- equality
_==_ : ∀ (m : ℕ) → ∀ (n : ℕ) → Prop
Z == Z =  ⊤
Z == S n = ⊥
S m == Z = ⊥
S m == S n = m == n

-- Is equiality an equivalence relation?

-- reflexivity
refl-≡ : ∀ (m : ℕ) → m == m
refl-≡ Z = ⋆
refl-≡ (S m) = refl-≡ m

-- Symmetry
sym-≡ : ∀ (m : ℕ) → ∀ (n : ℕ) → m == n → n == m
sym-≡ Z Z h = ⋆
sym-≡ Z (S n) ()
sym-≡ (S m) Z ()
sym-≡ (S m) (S n) h = sym-≡ m n h

-- Transitivity
trans-≡ : ∀ (m n p : ℕ) → m == n → n == p → m == p
trans-≡ Z n Z h0 h1 = ⋆
trans-≡ Z Z (S p) h0 h1 = h1
trans-≡ Z (S n) (S p) () h1
trans-≡ (S m) Z Z () h1
trans-≡ (S m) (S n) Z h0 ()
trans-≡ (S m) Z (S p) () h1
trans-≡ (S m) (S n) (S p) h0 h1 = trans-≡ m n p h0 h1

-- Homework ≤ on natural numbers

-- Addition of natural numbers
_+_ : ∀ (m n : ℕ) → ℕ
Z + n = n
S m + n = S (m + n)

-- Use equality, 2 + 3 == 3 + 2
eqq : ((S (S Z)) + (S ( S ( S Z)))) == ((S ( S ( S Z))) + (S (S Z)))
eqq = ⋆

infix 4 _≡_
data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x
{-# BUILTIN EQUALITY _≡_  #-}
{-# BUILTIN REFL     refl #-}

eqq2 : ((S (S Z)) + (S ( S ( S Z)))) ≡ ((S ( S ( S Z))) + (S (S Z)))
eqq2 = refl

cong : ∀ (n m : ℕ) → n ≡ m → S n ≡ S m
cong n .n refl = refl

-lemma-+ : ∀ (n : ℕ) → n ≡ (n + Z)
-lemma-+ Z = refl
-lemma-+ (S n) with -lemma-+ n
-lemma-+ (S n) | h = cong n (n + Z) h

lem2 : ∀ (m n : ℕ) → (m + S n) ≡ S (m + n)
lem2 Z n = refl
lem2 (S m) n = cong (m + S n) (S (m + n)) (lem2 m n)

-- Now prove commutativity of addition
commute-+ : ∀ (m n : ℕ) → (m + n) ≡ (n + m)
commute-+ Z n = -lemma-+ n
commute-+ (S m) n with (n + S m) | (lem2 n m)
commute-+ (S m) n | .(S (n + m)) | refl = cong (m + n) (n + m) (commute-+ m n)


_<_ : ∀ (m n : ℕ) → Prop
Z < Z = ⊥
Z < S n = ⊥
S m < Z = ⊤
S m < S n = m < n

-- refl-< : ∀ (m : ℕ) → m < m
-- refl-< Z = !!
-- refl-< (S m) = !!

-- Define booleans
data 𝔹 : Set where
 True : 𝔹
 False : 𝔹

-- Define &&
_&&_ : ∀ (A B : 𝔹) → 𝔹
True && True = True
True && False = False
False && B = False

-- Define ||
_||_ : ∀ (A B : 𝔹) → 𝔹
True || B = True
False || True = True
False || False = False

-- Prove equivalence of two hardware functions g and f
g : ∀ (A B C : 𝔹) → 𝔹
g A B C = B && (A || C)

ff : ∀ (A B C : 𝔹) → 𝔹
ff A B C = (A && B) || ((B && C) && (B || C))

-- Equality of booleans
_==̰_ : ∀ (A B : 𝔹) → Prop
True ==̰ True = ⊤
True ==̰ False = ⊥
False ==̰ True = ⊥
False ==̰ False = ⊤

-- Now prove that for any input A B C, g ≡ ff
g≃ff : ∀ (A B C : 𝔹) → (g A B C) ==̰ (ff A B C)
g≃ff True True True = ⋆
g≃ff True True False = ⋆
g≃ff True False C = ⋆
g≃ff False True True = ⋆
g≃ff False True False = ⋆
g≃ff False False C = ⋆

_≤_ : ∀ (m n : ℕ) → Prop
Z ≤ n = ⊤
S m ≤ Z = ⊥
S m ≤ S n = m ≤ n

-- Symmetry on ≤
-- sym-≤ : ∀ (m n : ℕ) → (m ≤ n) → (n ≤ m)
-- sym-≤ Z Z ⋆ = ⋆
-- sym-≤ Z (S n) ⋆ = {!!}
-- sym-≤ (S m) Z ()
-- sym-≤ (S m) (S n) p = sym-≤ m n p

-- ≠ 
_≠_ : ∀ (m n : ℕ) → Prop
Z ≠ Z =  ⊤
Z ≠ S n = ⊥
S m ≠ Z = ⊥
S m ≠ S n = m ≠ n

-- Is ≠ an equivalence relation?
-- ≠-refl
≠-relf : ∀ (m : ℕ) → (m ≠ m)
≠-relf Z = ⋆
≠-relf (S m) = ≠-relf m

-- Symmetry
≠-sym : ∀ (m n : ℕ) → (m ≠ n) → (n ≠ m)
≠-sym Z Z p = ⋆
≠-sym Z (S n) ()
≠-sym (S m) Z ()
≠-sym (S m) (S n) p = ≠-sym m n p

-- Transitivity
≠-trans : ∀ (m n p : ℕ) → (m ≠ n) → (n ≠ p) → (m ≠ p)
≠-trans Z n Z h0 h1 = ⋆
≠-trans Z Z (S p) h0 h1 = h1
≠-trans Z (S n) (S p) () h1
≠-trans (S m) Z Z () h1
≠-trans (S m) (S n) Z h0 ()
≠-trans (S m) Z (S p) h0 ()
≠-trans (S m) (S n) (S p) h0 h1 = ≠-trans m n p h0 h1
