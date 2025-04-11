
-- Demo code from 3rd AFP Agda lecture
module Demo.Demo3 where

-- From previous lectures
-------------------------

open import Agda.Builtin.Nat
open import Agda.Builtin.List
open import Agda.Builtin.Bool

_++_ : {A : Set} → (xs ys : List A) → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

data _∈_ {A : Set} (a : A) : List A → Set where
  here  : ∀{xs}   → a ∈ (a ∷ xs)
  there : ∀{x xs} → a ∈      xs
                  → a ∈ (x ∷ xs)

-- Not all types have values
----------------------------

ex1 : 42 ∈ (1 ∷ 8 ∷ 42 ∷ [])
ex1 = there (there here)

ex2 : 19 ∈ (1 ∷ 8 ∷ 42 ∷ [])
ex2 = {!   !}

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

ex3 : (42 ∈ []) × Bool
ex3 = {!   !} , false

data Exp (Γ : List {!   !}) : Set where
  -- ... (see last lecture)
  var : ∀ {t} → t ∈ Γ → Exp Γ

-- How to prove properties in Agda
----------------------------------

-- 1. Choose some property P
-- 2. Design an Agda type T (such that T has values => P is true)
-- 3. Write an expression of type T
-- 4. Conclude that P is proved

-- Examples
-----------

-- "Lemma 1: the list [1,8,42,7] contians the number 42"
-- "Proof of lemma 1: it's in the 3rd position"

lem1 = 42 ∈ (1 ∷ 8 ∷ 42 ∷ 7 ∷ [])

proof1 : lem1
proof1 = there (there here)

-- C-c C-.
-- C-u C-u C-c C-.

-- "Lemma 2: the list (reverse [1,8,42,7]) is non empty"
-- "Proof of lemma 2: by definition of empty"

data Non-Empty {A : Set} : List A → Set where
  non-empty : ∀{x xs} → Non-Empty (x ∷ xs)

rev-app : {A : Set} → (acc xs : List A) → List A
rev-app acc [] = acc
rev-app acc (x ∷ xs) = rev-app (x ∷ acc) xs
reverse : {A : Set} → (xs : List A) → List A
reverse = rev-app []

proof2 : Non-Empty (reverse (1 ∷ 8 ∷ 42 ∷ 7 ∷ []))
proof2 = non-empty

-- "Lemma 3: forall sets A. forall lists of A, xs ys. the list xs is non-empty => (xs ++ ys) is non empty"
-- "Proof of lemma 3:
--    let A, xs, ys be arbitrary.
--      assume that xs is non-empty.
--        xs ++ ys is obviously non empty.
--    QED
--  "

lem3 = {A : Set} {xs ys : List A} → Non-Empty xs → Non-Empty (xs ++ ys)

proof3 : lem3
proof3 {xs = (x ∷ xs')} non-empty = non-empty

-- "Lemma 4: forall properties P Q. P ∧ Q ⇒ Q ∧ P"
-- "Proof of lemma 4:
--    let P,Q be arbitrary.
--      assume P ∧ Q.
--        we now prove P.
--          recall P ∧ Q
--          ∴ P
--        we now prove Q.
--          recall P ∧ Q
--          ∴ Q
--        ∴ P ∧ Q
--      ∴ Q ∧ P ⇒ P ∧ Q
--    ∴ ∀ P Q. Q ∧ P ⇒ P ∧ Q
--    QED
--  "

proof4 : {P Q : Set} → P × Q → Q × P
proof4 (p , q) = q , p

-- Curry-Howard correspondence
------------------------------

--  | Agda type T       |     Theorem that holds if T has values
--- | ----------------- | ------------------------------------------
--  | x ∈ xs            | the list xs' contains the value x'
--  | Non-Empty xs      | the list xs' is non-empty
--  | A → B             | A' => B'
--  | Either A B        | A' ∨ B'
--  | A × B             | A' ∧ B'
--  | (a : A) → B       | ∀(a' ∈ A'). B'     (where B may contain a)
--  | Σ A (λ a → B)     | ∃(a' ∈ A'). B'     (where B may contain a)
--  | Unit              | true
--  | Nat               | true
--  | Bool              | true
--  | Void              | false
--  | (A → B) × (B → A) | (A' ⇒ B') ∧ (B' ⇒ A')
--  | (A → B) × (B → A) | A' ⇔ B'

data Σ (A : Set) (B : A → Set) : Set where
  _,_ : (a : A) → B a → Σ A B

ex4 : Σ Nat (_∈ (1 ∷ 2 ∷ 3 ∷ []))
ex4 = 2 , there here

data Unit : Set where
  unit : Unit

data Void : Set where
  -- (empty)
