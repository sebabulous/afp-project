
-- Demo code from 4th AFP Agda lecture
module Demo.Demo4 where

open import Agda.Builtin.List
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Primitive

-- From previous lectures
-------------------------

private variable
  ℓa ℓb : Level
  A : Set ℓa
  B : Set ℓb
  x y z : A

_++_ : (xs ys : List A) → List A
[]       ++ ys =            ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)
infixl 20 _++_

reverse : List A → List A
reverse [] = []
reverse (x ∷ xs) = reverse xs ++ (x ∷ [])

data _∈_ {A : Set} (a : A) : List A → Set where
  here  : ∀{xs}   → a ∈ (a ∷ xs)
  there : ∀{x xs} → a ∈      xs
                  → a ∈ (x ∷ xs)

data Void : Set where
  -- (empty)

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

-- New types
------------

--  | A → Void          | A' ⇒ false
--  | A → Void          | ¬ A'
--  | x ≡ y             | x' = y'

ex1 : (42 ∈ []) → Void
ex1 ()

ex2 : (42 ∈ (1 ∷ 1 ∷ 1 ∷ 1 ∷ [])) → Void
ex2 (there (there (there (there ()))))

-- refl
-------

ex3 : 4 ≡ 4
ex3 = refl

ex4 : 4 ≡ (1 + 3)
ex4 = refl

n : Nat
n = {!   !}

ex5 : 0 ≡ (0 * n)
ex5 = refl

ex6 : 0 ≡ (n * 0)
ex6 = {! refl !}

-- Equality combinators
-----------------------

transport
  : A ≡ B
  → A → B
transport refl a = a

_∵_
  : A
  → A ≡ B
  →     B
a ∵ pf = transport pf a

cong 
  : (f : A → B)
  →   x ≡   y
  → f x ≡ f y
cong _ refl = refl

_under_
  : (  x ≡   y) → (f : A → B)
  → (f x ≡ f y)
pf under f = cong f pf

sym
  : x ≡ y
  → y ≡ x
sym refl = refl

trans : x ≡ y
      →     y ≡ z
      → x ≡     z
trans = {!   !}
-- Exercise (easy)

-- Non-refl equality proofs
---------------------------

assoc-++ : (xs ys zs : List A)
         → ((xs ++ ys) ++ zs)
         ≡ (xs ++ (ys ++ zs))

assoc-++       [] ys zs = refl
assoc-++ (x ∷ xs) ys zs = cong (x ∷_) (assoc-++ xs ys zs)

++-[] : (xs : List A) → (xs ≡ xs ++ [])
++-[] = {!   !}
-- Exercise (medium)
--  hint: split, recurse, cong

lemma-rev : (xs ys : List A) → reverse (reverse xs ++ ys) ≡ reverse ys ++ xs
lemma-rev = {!   !}
-- Exercise (hard)
--  hint: split, ++-[], lemma-rev xs (x ∷ ys), trans x2, assoc-++, cong, assoc-++

rev-rev : (xs : List A) → reverse (reverse xs) ≡ xs
rev-rev xs = {!   !}
-- Exercise (medium)
--  hint: lemma-rev, trans, ++-[], cong

-- Hetrogenous lists & cong
---------------------------

data HetList : List Set → Set₁ where
  [] : HetList []
  _∷_ : ∀{A As} → A → HetList As → HetList (A ∷ As)

ex7 : ∀ xs ys zs
    → HetList ((xs ++ ys) ++ zs)
    ≡ HetList (xs ++ (ys ++ zs))
ex7 xs ys zs = cong HetList (assoc-++ xs ys zs)

-- Using transport
------------------

module _ (qs rs ts : List Set) (env : HetList (qs ++ (rs ++ ts))) where

  env1 : HetList ((qs ++ rs) ++ ts)
  env1 = env ∵ sym (ex7 qs rs ts)

  env2 : HetList (reverse (reverse(qs ++ (rs ++ ts))))
  env2 = env ∵ cong HetList {!   !}
  -- Exercise (medium)
  --  hint: rev-rev, sym