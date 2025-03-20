module artifact.Folds where

open import Agda.Builtin.Strict

open import artifact.Main

foldr : {V K A : Set} → (A → V → V) → V → Map K A → V
foldr f v tip = v
foldr f v (node s k v₁ l r) = foldr f (f v₁ (foldr f v r)) l

foldl : {V K A : Set} → (V → A → V) → V → Map K A → V
foldl f v tip = v
foldl f v (node s k v₁ l r) = foldl f (f (foldl f v l) v₁) r

foldrWithKey : {V K A : Set} → (K → A → V → V) → V → Map K A → V
foldrWithKey f v tip = v
foldrWithKey f v (node s k v₁ l r) = foldrWithKey f (f k v₁ (foldrWithKey f v r)) l

foldlWithKey : {V K A : Set} → (V → K → A → V) → V → Map K A → V
foldlWithKey f v tip = v
foldlWithKey f v (node s k v₁ l r) = foldlWithKey f (f (foldlWithKey f v l) k v₁) r

-- foldMapWithKey


-- %%%%%%%%%%%%% Strict folds %%%%%%%%%%%%%%%%%%%%%%

foldr' : {V K A : Set} → (A → V → V) → V → Map K A → V
foldr' f v tip = v
foldr' f v (node s k v₁ l r) = foldr' f (primForce (foldr' f v r) (f v₁)) l

foldl' : {V K A : Set} → (V → A → V) → V → Map K A → V
foldl' f v tip = v
foldl' f v (node s k v₁ l r) = foldl f (primForce ((foldl f v l)) (λ x → f x v₁)) r

foldrWithKey' : {V K A : Set} → (K → A → V → V) → V → Map K A → V
foldrWithKey' f v tip = v
foldrWithKey' f v (node s k v₁ l r) = foldrWithKey' f (primForce (foldrWithKey' f v r) (f k v₁)) l

foldlWithKey' : {V K A : Set} → (V → K → A → V) → V → Map K A → V
foldlWithKey' f v tip = v
foldlWithKey' f v (node s k v₁ l r) = foldlWithKey' f (primForce (foldlWithKey' f v l) (λ x → f x k v₁)) r