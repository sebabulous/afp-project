module Map.Folds where

open import Agda.Builtin.Nat
open import Agda.Builtin.Strict

open import Map.Map

-- Fold the values in the map using the given right-associative binary operator, 
-- such that foldr f z == foldr f z . elems.
foldr : {B K A : Set} → (A → B → B) → B → Map K A → B
foldr _ b tip = b
foldr f b (node s k a l r) = foldr f (f a (foldr f b r)) l

-- Fold the values in the map using the given left-associative binary operator, 
-- such that foldl f z == foldl f z . elems.
foldl : {V K A : Set} → (V → A → V) → V → Map K A → V
foldl f v tip = v
foldl f v (node s k v₁ l r) = foldl f (f (foldl f v l) v₁) r

-- Fold the keys and values in the map using the given right-associative binary operator, 
-- such that foldrWithKey f z == foldr (uncurry f) z . toAscList.
foldrWithKey : {V K A : Set} → (K → A → V → V) → V → Map K A → V
foldrWithKey f v tip = v
foldrWithKey f v (node s k v₁ l r) = foldrWithKey f (f k v₁ (foldrWithKey f v r)) l

-- Fold the keys and values in the map using the given left-associative binary operator, 
-- such that foldlWithKey f z == foldl (\z' (kx, x) -> f z' kx x) z . toAscList.
foldlWithKey : {V K A : Set} → (V → K → A → V) → V → Map K A → V
foldlWithKey f v tip = v
foldlWithKey f v (node s k v₁ l r) = foldlWithKey f (f (foldlWithKey f v l) k v₁) r

-- fold : {{ Monoid m }} → t m -> m
fold : {K : Set} → Map K Nat → Nat
fold xs = foldr mappend mempty xs

-- Fold the keys and values in the map using the given monoid, 
-- such that foldMapWithKey f = fold . mapWithKey f
foldMapWithKey : {K V M : Set} → {{Monoid M}} → (K → V → M) → Map K V → M 
foldMapWithKey f tip = mempty
foldMapWithKey f (node 1 x₁ x₂ tip tip) = f x₁ x₂
foldMapWithKey f (node (suc (suc n)) x₁ x₂ m m₁) = mappend (foldMapWithKey f m) (mappend (f x₁ x₂) (foldMapWithKey f m₁)) 
foldMapWithKey f _ = {! error  !}

-- %%%%%%%%%%%%% Strict folds %%%%%%%%%%%%%%%%%%%%%%

-- A strict version of foldr. Each application of the operator is evaluated before using 
-- the result in the next application. This function is strict in the starting value.
foldr' : {V K A : Set} → (A → V → V) → V → Map K A → V
foldr' f v tip = v
foldr' f v (node s k v₁ l r) = foldr' f (primForce (foldr' f v r) (f v₁)) l

-- A strict version of foldl. Each application of the operator is evaluated before using 
-- the result in the next application. This function is strict in the starting value.
foldl' : {V K A : Set} → (V → A → V) → V → Map K A → V
foldl' f v tip = v
foldl' f v (node s k v₁ l r) = foldl' f (primForce ((foldl' f v l)) (λ x → f x v₁)) r

-- A strict version of foldrWithKey. Each application of the operator is evaluated before using 
-- the result in the next application. This function is strict in the starting value.
foldrWithKey' : {V K A : Set} → (K → A → V → V) → V → Map K A → V
foldrWithKey' f v tip = v
foldrWithKey' f v (node s k v₁ l r) = foldrWithKey' f (primForce (foldrWithKey' f v r) (f k v₁)) l

-- A strict version of foldlWithKey. Each application of the operator is evaluated before using 
-- the result in the next application. This function is strict in the starting value.
foldlWithKey' : {V K A : Set} → (V → K → A → V) → V → Map K A → V
foldlWithKey' f v tip = v  
foldlWithKey' f v (node s k v₁ l r) = foldlWithKey' f (primForce (foldlWithKey' f v l) (λ x → f x k v₁)) r 