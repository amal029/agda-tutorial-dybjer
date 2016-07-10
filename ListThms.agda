module ListThms where
open import Sec4
import Sec2

{-
  Definition of a list
-}
data List (A : Set) : Set where
  []  : List A                  -- Empty list
  _∷_ : A → List A → List A     -- Cons


infixr 4 _∷_


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


-- definition of a map
map : {A B : Set} → (A → B) → (List A) → List B
map f [] = []
map f (x ∷ l) = (f x) ∷ map f l


-- definition of fold left
fold : {A B : Set} → (A → B → B) → B → (List A) → B
fold f x [] = x
fold f x (x₁ ∷ l) = fold f (f x₁ x) l

-- reduce only works on lists of length > 0
reduce : {A : Set} → (l : List A) → (p : nelist l) → (A → A → A) → A 
reduce [] ()
reduce (x ∷ l) _ f = fold f x l

-- length of a list 
length : {A : Set} → (List A) → Sec2.ℕ
length [] = Sec2.Z
length (x ∷ l) = (Sec2.S Sec2.Z) Sec2.+ (length l)

-- Proposition on ≤
_<=_ : Sec2.ℕ  → Sec2.ℕ → Prop
Sec2.Z <= Sec2.Z = ⊤
Sec2.Z <= Sec2.S y = ⊤
Sec2.S x <= y = x <= y

_>=_ : Sec2.ℕ  → Sec2.ℕ → Prop
Sec2.Z >= Sec2.Z = ⊤
Sec2.Z >= Sec2.S y = ⊥
Sec2.S x >= y = x >= y

-- Indexing into the list
_!!_ : {A : Set} → ∀ (l : List A) → ∀ (i : Sec2.ℕ) → (nelist l)
                 → Exists A (λ _  → ((i >= Sec2.Z) ∧ (i <= (length l))))
([] !! i) () 
((x ∷ l) !! i) ⋆ = [ x , (and (lem1 i) (lem (x ∷ l) i))]
  where
  cong-<= : (x y : Sec2.ℕ) → (x <= y) → (x <= Sec2.S y)
  cong-<= Sec2.Z y p = ⋆
  cong-<= (Sec2.S x) Sec2.Z p = cong-<= x Sec2.Z p
  cong-<= (Sec2.S x) (Sec2.S y) p = cong-<= x (Sec2.S y) p

  lem1 : (i : Sec2.ℕ) → (i >= Sec2.Z)
  lem1 Sec2.Z = ⋆
  lem1 (Sec2.S i) = lem1 i

  lem2 : (i : Sec2.ℕ) → (i <= Sec2.Z)
  lem2 Sec2.Z = ⋆
  lem2 (Sec2.S i₁) = lem2 i₁

  lem : {A : Set} →  (l : List A) → (i : Sec2.ℕ) → (i <= (length l))
  lem [] Sec2.Z = ⋆
  lem [] (Sec2.S i) = lem2 i
  lem (x₁ ∷ l₁) i = cong-<= i (length l₁) (lem l₁ i)


data Maybe (A : Set) : Set where
  Nothing : Maybe A
  Just : A → Maybe A

index : {A : Set} → ∀ (l : List A)
                  → (nelist l)
                  → ∀ (i : Sec2.ℕ)
                  → Sec2.So ((i Sec2.≥ Sec2.Z) Sec2.& (i Sec2.< (length l)))
                  → Maybe A
index l _ i _ = index' l i (Sec2.Z)
  where
  index' : {A : Set} → ∀ (l : List A) → ∀(i : Sec2.ℕ)
                     → (c : Sec2.ℕ) → Maybe A
  index' [] i₁ c = Nothing
  index' (x₁ ∷ l₁) i₁ c with (i₁ Sec2.== c) 
  index' (x₁ ∷ l₁) i₁ c | Sec2.T = Just x₁
  index' (x₁ ∷ l₁) i₁ c | Sec2.F = index' l₁ i₁ (Sec2.S c)

exx1 : Maybe Sec2.ℕ
exx1 = index (1 ∷ []) ⋆ 0 Sec2.ok

index'' : {A : Set} → ∀ (l : List A)
                  → ∀ (i : Sec2.ℕ)
                  → Sec2.So (i Sec2.< (length l))
                  → A
index'' [] Sec2.Z ()
index'' [] (Sec2.S i) ()
index'' (x ∷ l) Sec2.Z Sec2.ok = x
index'' (x ∷ l) (Sec2.S i) p = index'' l i p

-- append two lists
_++_ : {A : Set} → (l : List A) → (l' : List A) → (List A)
[] ++ l' = l'
(x ∷ l) ++ l' = (x ∷ (l ++ l'))


-- composition of two functions
_∘_ : {A B C : Set} → (A → B) → (B → C) → (A → C)
f ∘ g = λ x → (g (f x))


cong : {A : Set} → (x : A) → (l m : List A) → (l Sec2.≡ m) → (x ∷ l) Sec2.≡ (x ∷ m)
cong x l .l Sec2.refl = Sec2.refl

cong2 : {A : Set} → (l m q : List A) → (l Sec2.≡ m) → (l ++ q) Sec2.≡ (m ++ q)
cong2 l .l q Sec2.refl = Sec2.refl

thm1-map : {A B : Set} → (f : A → B) → (l : List A) → (m : List A) → (map f (l ++ m)) Sec2.≡ (map f l) ++ (map f m)
thm1-map f [] m = Sec2.refl
thm1-map f (x ∷ l) m with (f x)
thm1-map f (x ∷ l) m | p  = cong p (map f (l ++ m)) (map f l ++ map f m) (thm1-map f l m)

-- map ∘
thm2-map : {A B C : Set} → (f : A → B) → (g : B → C) → (l : List A) → (map (f ∘ g) l Sec2.≡ ((map f) ∘ (map g)) l)
thm2-map f₁ g₁ [] = Sec2.refl
thm2-map f₁ g₁ (x ∷ l) with (thm2-map f₁ g₁ l)
thm2-map f₁ g₁ (x ∷ l) | p = cong (g₁ (f₁ x)) (map (λ z → g₁ (f₁ z)) l) (map g₁ (map f₁ l)) p

-- Non empty list by construction 
data NeList (A : Set) : Set where
  ^_^ : A → NeList A
  _∶_ : A → NeList A → NeList A

infixr 60 ^_^
infixr 60 _∶_



