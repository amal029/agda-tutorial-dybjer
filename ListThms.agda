module ListThms where
open import Sec4
import Sec2

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

-- append two lists
_++_ : {A : Set} → (l : List A) → (l' : List A) → (List A)
[] ++ l' = l'
(x ∷ l) ++ l' = (x ∷ (l ++ l'))


-- composition of two functions
_∘_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
g ∘ f = λ x → (g (f x))


cong : {A : Set} → (x : A) → (l m : List A) → (l Sec2.≡ m) → (x ∷ l) Sec2.≡ (x ∷ m)
cong x l .l Sec2.refl = Sec2.refl

cong2 : {A : Set} → (l m q : List A) → (l Sec2.≡ m) → (l ++ q) Sec2.≡ (m ++ q)
cong2 l .l q Sec2.refl = Sec2.refl

thm1-map : {A B : Set} → (f : A → B) → (l : List A) → (m : List A) → (map f (l ++ m)) Sec2.≡ (map f l) ++ (map f m)
thm1-map f [] m = Sec2.refl
thm1-map f (x ∷ l) m with (f x)
thm1-map f (x ∷ l) m | p  = cong p (map f (l ++ m)) (map f l ++ map f m) (thm1-map f l m)


