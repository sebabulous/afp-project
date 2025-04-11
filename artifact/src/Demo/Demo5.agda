
-- Demo code from 5th AFP Agda lecture
module Demo.Demo5 where

-- From previous lectures
-------------------------

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat
open import Agda.Builtin.List

private variable
  A B : Set
  x y : A

_++_ : (xs ys : List A) → List A
[]       ++ ys =            ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)
infixl 20 _++_

reverse : List A → List A
reverse [] = []
reverse (x ∷ xs) = reverse xs ++ (x ∷ [])

cong : (f : A → B)
  →   x ≡   y
  → f x ≡ f y
cong _ refl = refl

assoc-++ : (xs ys zs : List A)
  → ((xs ++ ys) ++ zs)
  ≡ (xs ++ (ys ++ zs))
assoc-++       [] ys zs = refl
assoc-++ (x ∷ xs) ys zs = cong (x ∷_) (assoc-++ xs ys zs)

-- Unit testing
---------------

ex8 : ∀ n → 0 ≡ (0 * n)
ex8 n = refl

ex8' : ∀ n → n ≡ (n * 0)
ex8' n = {! refl  !}  -- blocked on n

-- Equational reasoning
-----------------------

trans : ∀ {p q r : A} → p ≡ q → q ≡ r → p ≡ r
trans refl y=z = y=z

_≡⟨_⟩_ : ∀ p {q r : A} → p ≡ q → q ≡ r → p ≡ r
x ≡⟨ x=y ⟩ y=z = trans x=y y=z

_∎ : (a : A) → a ≡ a
a ∎ = refl

infixr 4 _≡⟨_⟩_
infixr 5 _∎

-- Answers to exercises
-----------------------

++-[] : (xs : List A) → (xs ≡ xs ++ [])
++-[] [] = refl
++-[] (x ∷ xs) = cong (x ∷_) (++-[] xs)

lemma-rev : (xs ys : List A) → reverse (reverse xs ++ ys) ≡ reverse ys ++ xs

lemma-rev [] ys = ++-[] (reverse ys)

-- lemma-rev (x ∷ xs) ys = {! lemma-rev xs (x ∷ ys) !}
-- lemma-rev (x ∷ xs) ys = trans {!   !} (trans (lemma-rev xs (x ∷ ys)) {!   !})
-- lemma-rev (x ∷ xs) ys = trans {! cong reverse (assoc-++ _ _ _) !} (trans (lemma-rev xs (x ∷ ys)) {!   !})
-- lemma-rev (x ∷ xs) ys = trans {! cong reverse (assoc-++ (reverse xs) _ _) !} (trans (lemma-rev xs (x ∷ ys)) {!   !})
-- lemma-rev (x ∷ xs) ys = trans {! cong reverse (assoc-++ (reverse xs) (x ∷ []) _) !} (trans (lemma-rev xs (x ∷ ys)) {!   !})
-- lemma-rev (x ∷ xs) ys = trans {! cong reverse (assoc-++ (reverse xs) (x ∷ []) ys) !} (trans (lemma-rev xs (x ∷ ys)) {!   !})
-- lemma-rev (x ∷ xs) ys = trans (cong reverse (assoc-++ (reverse xs) (x ∷ []) ys)) (trans (lemma-rev xs (x ∷ ys)) {!   !})
-- lemma-rev (x ∷ xs) ys = trans (cong reverse (assoc-++ (reverse xs) (x ∷ []) ys)) (trans (lemma-rev xs (x ∷ ys)) {! assoc-++ _ _ _  !})
-- lemma-rev (x ∷ xs) ys = trans (cong reverse (assoc-++ (reverse xs) (x ∷ []) ys)) (trans (lemma-rev xs (x ∷ ys)) {! assoc-++ (reverse ys) _ _  !})
-- lemma-rev (x ∷ xs) ys = trans (cong reverse (assoc-++ (reverse xs) (x ∷ []) ys)) (trans (lemma-rev xs (x ∷ ys)) {! assoc-++ (reverse ys) (x ∷ []) _  !})
-- lemma-rev (x ∷ xs) ys = trans (cong reverse (assoc-++ (reverse xs) (x ∷ []) ys)) (trans (lemma-rev xs (x ∷ ys)) {! assoc-++ (reverse ys) (x ∷ []) xs  !})
-- lemma-rev (x ∷ xs) ys = trans (cong reverse (assoc-++ (reverse xs) (x ∷ []) ys)) (trans (lemma-rev xs (x ∷ ys)) (assoc-++ (reverse ys) (x ∷ []) xs))

-- lemma-rev (x ∷ xs) ys =
--    trans
--      (cong reverse (assoc-++ (reverse xs) (x ∷ []) ys))
--   (trans
--      (lemma-rev xs (x ∷ ys))
--      (assoc-++ (reverse ys) (x ∷ []) xs
--   ))

-- lemma-rev (x ∷ xs) ys =
--    trans
--      (cong reverse (assoc-++ (reverse xs) (x ∷ []) ys))
--   (trans
--      (lemma-rev xs (x ∷ ys))
--   (trans
--      (assoc-++ (reverse ys) (x ∷ []) xs)
--   refl
--   ))

-- lemma-rev (x ∷ xs) ys =
--    trans  {p = reverse (reverse (x ∷ xs) ++ ys)}
--      (cong reverse (assoc-++ (reverse xs) (x ∷ []) ys))
--   (trans  {p = reverse (reverse xs ++ ((x ∷ []) ++ ys))}
--      (lemma-rev xs (x ∷ ys))
--   (trans  {p = reverse (x ∷ ys) ++ xs}
--      (assoc-++ (reverse ys) (x ∷ []) xs)
--   refl
--   ))

lemma-rev (x ∷ xs) ys =
    reverse (reverse (x ∷ xs) ++ ys)
      ≡⟨ cong reverse (assoc-++ (reverse xs) (x ∷ []) ys) ⟩
    reverse (reverse xs ++ ((x ∷ []) ++ ys))
      ≡⟨ lemma-rev xs ((x ∷ []) ++ ys) ⟩
    reverse (x ∷ ys) ++ xs
      ≡⟨ assoc-++ (reverse ys) (x ∷ []) xs ⟩
    reverse ys ++ ((x ∷ []) ++ xs)
      ∎

-- C-c C-s
-- C-c C-a

rev-rev : (xs : List A) → reverse (reverse xs) ≡ xs

-- rev-rev xs = {! lemma-rev _ _   !}
-- rev-rev xs = {! lemma-rev xs _  !}
-- rev-rev xs = {! lemma-rev xs [] !}
-- rev-rev xs = {! trans ? (lemma-rev xs []) !}
-- rev-rev xs = trans {!   !} (lemma-rev xs [])
-- rev-rev xs = trans {! cong reverse _ !} (lemma-rev xs [])
-- rev-rev xs = trans {! cong reverse (++-[] _) !} (lemma-rev xs [])
-- rev-rev xs = trans {! cong reverse (++-[] (reverse xs)) !} (lemma-rev xs [])
-- rev-rev xs = trans (cong reverse (++-[] (reverse xs))) (lemma-rev xs [])

rev-rev xs =
    reverse (reverse xs)
      ≡⟨ cong reverse (++-[] (reverse xs)) ⟩
    reverse (reverse xs ++ [])
      ≡⟨ lemma-rev xs [] ⟩
    xs
      ∎