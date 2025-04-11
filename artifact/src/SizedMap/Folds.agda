module SizedMap.Folds where

open import Agda.Builtin.Nat
open import Agda.Builtin.Strict

open import SizedMap.Map
open import Helpers.Comparable
open import Helpers.Pair

private variable
  K A V : Set
  m n : Nat

-- Fold the values in the map using the given right-associative binary operator, 
-- such that foldr f z == foldr f z . elems.
foldr : {V K A : Set} → (A → V → V) → V → Map K A n → V
foldr f v tip = v
foldr f v (node k a l r) = foldr f (f a (foldr f v r)) l

-- Fold the values in the map using the given left-associative binary operator, 
-- such that foldl f z == foldl f z . elems.
foldl : {V K A : Set} → (V → A → V) → V → Map K A n → V
foldl f v tip = v
foldl f v (node k a l r) = foldl f (f (foldl f v l) a) r

-- Fold the keys and values in the map using the given right-associative binary operator, 
-- such that foldrWithKey f z == foldr (uncurry f) z . toAscList.
foldrWithKey : {V K A : Set} → (K → A → V → V) → V → Map K A n → V
foldrWithKey f v tip = v
foldrWithKey f v (node k a l r) = foldrWithKey f (f k a (foldrWithKey f v r)) l

-- Fold the keys and values in the map using the given left-associative binary operator, 
-- such that foldlWithKey f z == foldl (\z' (kx, x) -> f z' kx x) z . toAscList.
foldlWithKey : {V K A : Set} → (V → K → A → V) → V → Map K A n → V
foldlWithKey f v tip = v
foldlWithKey f v (node k a l r) = foldlWithKey f (f (foldlWithKey f v l) k a) r

-- Fold the keys and values in the map using the given monoid, 
-- such that foldMapWithKey f = fold . mapWithKey f
foldMapWithKey : {K V M : Set} → {{Monoid M}} → (K → V → M) → Map K V n → M 
foldMapWithKey f tip = mempty
foldMapWithKey f (node k a tip tip) = f k a
foldMapWithKey f (node k a l r) = mappend (foldMapWithKey f l) (mappend (f k a) (foldMapWithKey f r)) 

-- %%%%%%%%%%%%% Strict folds %%%%%%%%%%%%%%%%%%%%%%

-- A strict version of foldr. Each application of the operator is evaluated before using 
-- the result in the next application. This function is strict in the starting value.
foldr' : {V K A : Set} → (A → V → V) → V → Map K A n → V
foldr' f v tip = v
foldr' f v (node k a l r) = foldr' f (primForce (foldr' f v r) (f a)) l

-- A strict version of foldl. Each application of the operator is evaluated before using 
-- the result in the next application. This function is strict in the starting value.
foldl' : {V K A : Set} → (V → A → V) → V → Map K A n → V
foldl' f v tip = v
foldl' f v (node k a l r) = foldl f (primForce ((foldl f v l)) (λ x → f x a)) r

-- A strict version of foldrWithKey. Each application of the operator is evaluated before using 
-- the result in the next application. This function is strict in the starting value.
foldrWithKey' : {V K A : Set} → (K → A → V → V) → V → Map K A n → V
foldrWithKey' f v tip = v
foldrWithKey' f v (node k a l r) = foldrWithKey' f (primForce (foldrWithKey' f v r) (f k a)) l

-- A strict version of foldlWithKey. Each application of the operator is evaluated before using 
-- the result in the next application. This function is strict in the starting value.
foldlWithKey' : {V K A : Set} → (V → K → A → V) → V → Map K A n → V
foldlWithKey' f v tip = v  
foldlWithKey' f v (node k a l r) = foldlWithKey' f (primForce (foldlWithKey' f v l) (λ x → f x k a)) r