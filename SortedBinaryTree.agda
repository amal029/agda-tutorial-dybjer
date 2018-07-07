module SortedBinaryTree where
  infix 4 _≡_
  data _≡_ {a} {A : Set a} (x : A) : A → Set a where
    refl : x ≡ x
  {-# BUILTIN EQUALITY _≡_  #-}
  {-# BUILTIN REFL     refl #-}

  open import Sec4
  postulate A : Set -- XXX: E.g., Nat or Bool some base type

  -- XXX: Postulates for ≤
  postulate _≤_ : A → A → Prop
  postulate antisym-≤ : (a b : A) → (a ≤ b) → (b ≤ a) → (a ≡ b)
  postulate tot-≤ : (a b : A) → (a ≤ b) ∨ (b ≤ a)
  postulate refl-≤ : (a : A) → (a ≤ a)
  postulate trans-≤ : (a b c : A) → (a ≤ b) → (b ≤ a) → (a ≤ c)

  -- XXX: Postulates for ≥
  postulate _≥_ : A → A → Prop
  postulate antisym-≥ : (a b : A) → (a ≥ b) → (b ≥ a) → (a ≡ b)
  postulate tot-≥ : (a b : A) → (a ≥ b) ∨ (b ≥ a)
  postulate refl-≥ : (a : A) → (a ≥ a)
  postulate trans-≥ : (a b c : A) → (a ≥ b) → (b ≥ a) → (a ≥ c)

-- XXX: Definition of a binary tree.
  data SortedBinaryTree (A : Set) : Set where
    Leaf : SortedBinaryTree A
    Node : (a : A) → (l : SortedBinaryTree A) → (r : SortedBinaryTree A) → SortedBinaryTree A

  all-leq : (a : A) → (t : SortedBinaryTree A) → Prop
  all-leq a₁ Leaf = ⊤
  all-leq a₁ (Node a₂ l r) = (a₂ ≤ a₁) ∧ ((all-leq a₁ l) ∧ (all-leq a₁ r))
    
  all-geq : (a : A) → (t : SortedBinaryTree A) → Prop
  all-geq a₁ Leaf = ⊤
  all-geq a₁ (Node a₂ l r) = (a₂ ≥ a₁) ∧ ((all-geq a₁ l) ∧ (all-geq a₁ r))

-- XXX: What is a sorted tree. A BTree is sorted, if all elements in the
-- left substree are ≥ root and all elements in the right subtree are ≤
-- root.
  ordered : SortedBinaryTree A → Prop
  ordered Leaf = ⊤
  ordered (Node a l r) = ((all-leq a l) ∧ (all-geq a r)) ∧ ((ordered l) ∧ (ordered r))

-- XXX: Insert function for SortedBinaryTree
  insert : (a : A) → SortedBinaryTree A → SortedBinaryTree A
  insert x Leaf = Node x Leaf Leaf
  insert x (Node a t t₁) with (tot-≤ x a)
  insert x (Node a t t₁) | ora x₁ = insert x t
  insert x (Node a t t₁) | orb x₁ = insert x t₁

-- XXX: Prove that the tree obtained after insertion is sorted
  insert-sorted : (a : A)
                  → (t : SortedBinaryTree A)
                  → (p : ordered t)
                  → ordered (insert a t)
  insert-sorted a Leaf _ = and (and ⋆ ⋆) (and ⋆ ⋆)
  insert-sorted a (Node a₁ t t₁) (and (and x x1) (and x2 x3)) with (tot-≤ a a₁)
  insert-sorted a (Node a₁ t t₁) (and (and p1 p2) (and p3 p4)) | ora w = insert-sorted a t p3
  insert-sorted a (Node a₁ t t₁) (and (and p1 p2) (and p3 p4)) | orb w = insert-sorted a t₁ p4

-- XXX: Proof carrying code
  insert' : (a : A)
            → (t : SortedBinaryTree A)
            → (p : ordered t)
            → Exists (SortedBinaryTree A) (λ t' → ordered t')
  insert' a t p = [ insert a t , insert-sorted a t p ]

-- XXX: Write Proof that delete works.


-- XXX: Write a version with record and setoid carrying the ≤, etc


