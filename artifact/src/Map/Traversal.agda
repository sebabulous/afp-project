module Map.Traversal where

open import Agda.Builtin.Maybe

open import Map.Folds
open import Map.Insertion
open import Map.Map
open import Map.Balance

-- Map a function over all values in the map.
map : {A B K : Set} → (A → B) → Map K A → Map K B
map f tip = tip
map f (node s k v l r) = node s k (f v) (map f l) (map f r)

-- Map a function over all values in the map.
mapWithKey : {A B K : Set} → (K → A → B) → Map K A → Map K B
mapWithKey f tip = tip
mapWithKey f (node s k v l r) = node s k (f k v) (mapWithKey f l) (mapWithKey f r)

traverseWithKey : {K V B : Set}{F : Set → Set} → {{Applicative F}} →  (K → V → F B) → Map K V → F (Map K B) 
traverseWithKey f tip = pure tip
traverseWithKey f (node 1 k v _ _) = pure (λ v₁ → node 1 k v₁ tip tip) <*> f k v 
traverseWithKey f (node s k v l r) = liftA3 (λ l₁ v₁ r₁ → node s k v₁ l₁ r₁) (traverseWithKey f l) (f k v) (traverseWithKey f r) -- USE FLIP

traverseMaybeWithKey : {K V B : Set}{F : Set → Set} → {{Comparable K}} → {{Applicative F}} → (K → V → F (Maybe B)) → Map K V → F (Map K B)
traverseMaybeWithKey f tip = pure tip
traverseMaybeWithKey f (node _ k v tip tip) = pure(maybe tip (λ v₁ → node 1 k v₁ tip tip)) <*> f k v 
traverseMaybeWithKey f (node _ k v l r) = liftA3 (combine k) (traverseMaybeWithKey f l) (f k v) (traverseMaybeWithKey f r)  
   where
      combine : {K V : Set} → {{Comparable K}} → K → Map K V → Maybe V → Map K V → Map K V
      combine k₁ l₂ (just x) r₂ = link k₁ x l₂ r₂
      combine _ l₂ nothing r₂ = link2 l₂ r₂

-- `mapAccumWithKey` threads an accumulating argument through the map in ascending order of keys.
mapAccumWithKey : {A B C K : Set} → (A → K → B → Pair A C) → A → Map K B → Pair A (Map K C)
mapAccumWithKey _ a tip = a , tip
mapAccumWithKey f a (node s k v l r) = let 
    v1 , l' = mapAccumWithKey f a l 
    v2 , v' = f v1 k v
    v3 , r' = mapAccumWithKey f v2 r
  in v3 , node s k v' l' r'

-- `mapAccum` threads an accumulating argument through the map in ascending order of keys.
mapAccum : {A B C K : Set} → (A → B → Pair A C) → A -> Map K B → Pair A (Map K C)
mapAccum f a m = mapAccumWithKey (λ v' _ m' → f v' m') a m

-- `mapAccumRWithKey` threads an accumulating argument through the map in descending order of keys.
mapAccumRWithKey : {A B C K : Set} → (A → K → B → Pair A C) → A → Map K B → Pair A (Map K C)
mapAccumRWithKey _ a tip = a , tip
mapAccumRWithKey f a (node s k v l r) = let 
    v1 , r' = mapAccumWithKey f a r
    v2 , v' = f v1 k v
    v3 , l' = mapAccumWithKey f v2 l
  in v3 , node s k v' l' r'
   
-- `mapKeys` f s is the map obtained by applying f to each key of s.
mapKeys : {K1 K2 V : Set} → {{Comparable K2}} → (K1 → K2) → Map K1 V → Map K2 V
mapKeys f m = foldlWithKey' (λ b kx x → insert (f kx) x b) tip m 

-- `mapKeysWith` c f s is the map obtained by applying f to each key of s.
mapKeysWith : {K1 K2 V : Set} → {{Comparable K2}} → (V → V → V) → (K1 → K2) → Map K1 V → Map K2 V
mapKeysWith c f m = foldlWithKey' (λ b kx x → insertWith c (f kx) x b) tip m 

-- `mapKeysMonotonic` f s == `mapKeys` f s, but works only when f is strictly monotonic. That is, for any values x and y, if x < y then f x < f y. 
mapKeysMonotonic : {K1 K2 V : Set} → (K1 → K2) → Map K1 V → Map K2 V
mapKeysMonotonic _ tip = tip      
mapKeysMonotonic f (node s k v l r) = node s (f k) v (mapKeysMonotonic f l) (mapKeysMonotonic f r) 