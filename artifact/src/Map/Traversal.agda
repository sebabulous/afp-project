module Map.Traversal where

open import Agda.Builtin.Maybe
open import Agda.Builtin.Nat

open import Map.Folds
open import Map.Insertion
open import Map.Map

private variable
  A B K F : Set
  m n : Nat

-- Map a function over all values in the map.
map : (A → B) → Map K A n → Map K B n
map f tip = tip
map f (node s k v l r) = node s k (f v) (map f l) (map f r)

-- Map a function over all values in the map.
mapWithKey : (K → A → B) → Map K A n → Map K B n
mapWithKey f tip = tip
mapWithKey f (node s k v l r) = node s k (f k v) (mapWithKey f l) (mapWithKey f r)

--traverseWithKey : {{Applicative F}} → (K → V → F B) → Map K V → F (Map K B)
--traverseWithKey = ?  

--traverseMaybeWithKey : {{Applicative F}} → (K → V → F (Maybe B)) → Map K V → F (Map K B)
--traverseMaybeWithKey = ? 

-- `mapAccumWithKey` threads an accumulating argument through the map in ascending order of keys.
mapAccumWithKey : {A B C K : Set} → (A → K → B → Pair A C) → A → Map K B n → Pair A (Map K C n)
mapAccumWithKey _ a tip = a , tip
mapAccumWithKey f a (node s k v l r) = let 
    v1 , l' = mapAccumWithKey f a l 
    v2 , v' = f v1 k v
    v3 , r' = mapAccumWithKey f v2 r
  in v3 , node s k v' l' r'

-- `mapAccum` threads an accumulating argument through the map in ascending order of keys.
mapAccum : {A B C K : Set} → (A → B → Pair A C) → A -> Map K B n → Pair A (Map K C n)
mapAccum f a m = mapAccumWithKey (λ v' _ m' → f v' m') a m

-- `mapAccumRWithKey` threads an accumulating argument through the map in descending order of keys.
mapAccumRWithKey : {A B C K : Set} → (A → K → B → Pair A C) → A → Map K B n → Pair A (Map K C n)
mapAccumRWithKey _ a tip = a , tip
mapAccumRWithKey f a (node s k v l r) = let 
    v1 , r' = mapAccumWithKey f a r
    v2 , v' = f v1 k v
    v3 , l' = mapAccumWithKey f v2 l
  in v3 , node s k v' l' r'
   
-- `mapKeys` f s is the map obtained by applying f to each key of s.
mapKeys : {K1 K2 V : Set} → {{Comparable K2}} → (K1 → K2) → Map K1 V n → Map K2 V n
-- mapKeys f m = foldlWithKey' (λ b kx x → insert (f kx) x b) tip m 
mapKeys f m = {!   !}

-- `mapKeysWith` c f s is the map obtained by applying f to each key of s.
mapKeysWith : {K1 K2 V : Set} → {{Comparable K2}} → (V → V → V) → (K1 → K2) → Map K1 V n → Map K2 V n
-- mapKeysWith c f m = foldlWithKey' (λ b kx x → insertWith c (f kx) x b) tip m 
mapKeysWith c f m = {!   !}

-- `mapKeysMonotonic` f s == `mapKeys` f s, but works only when f is strictly monotonic. That is, for any values x and y, if x < y then f x < f y. 
mapKeysMonotonic : {K1 K2 V : Set} → (K1 → K2) → Map K1 V n → Map K2 V n
mapKeysMonotonic _ tip = tip
mapKeysMonotonic f (node s k v l r) = node s (f k) v (mapKeysMonotonic f l) (mapKeysMonotonic f r) 