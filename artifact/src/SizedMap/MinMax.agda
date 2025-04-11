module SizedMap.MinMax where

open import Agda.Builtin.Nat
open import Agda.Builtin.Maybe

open import SizedMap.Balance
open import SizedMap.Map
open import Helpers.Comparable
open import Helpers.Pair

open import SizedMap.DeletionUpdate

private variable
  K A : Set
  m n : Nat

-- The minimal key of the map. Returns Nothing if the map is empty.
lookupMin : Map K A n → Maybe (Pair K A)
lookupMin tip = nothing
lookupMin (node k v tip _) = just (k , v)
lookupMin (node _ _ l@(node _ _ _ _) _) = lookupMin l

-- The maximal key of the map. Returns Nothing if the map is empty.
lookupMax : Map K A n → Maybe (Pair K A)
lookupMax tip = nothing
lookupMax (node k v _ tip) = just (k , v)
lookupMax (node _ _ _ r@(node _ _ _ _)) = lookupMax r

-- The minimal key of the map. Calls error if the map is empty.
findMin : Map K A (suc n) → Pair K A
findMin (node k a tip _) = (k , a)
findMin (node _ _ l@(node _ _ _ _) _) = findMin l

-- The maximal key of the map. Calls error if the map is empty.
findMax : Map K A (suc n) → Pair K A
findMax (node k a _ tip) = (k , a)
findMax (node _ _ _ r@(node _ _ _ _)) = findMax r

-- Delete the minimal key. Returns an empty map if the map is empty.
deleteMin : {{Comparable K}} → Map K A (suc n) → Map K A n
deleteMin (node _ _ tip r) = r
deleteMin (node k v l@(node _ _ _ _) r) = balanceR k v (deleteMin l) r


-- Delete the maximal key. Returns an empty map if the map is empty.
deleteMax : {{Comparable K}} → Map K A (suc n) → Map K A n
deleteMax (node _ _ l tip) = l
deleteMax (node k v l r@(node _ _ _ _)) = balanceL k v l (deleteMax r)

-- Update the value at the minimal key.
updateMinWithKey : {{Comparable K}} → (K → A -> Maybe A) → Map K A n → MapMod K A n
updateMinWithKey f tip = modId tip
updateMinWithKey f (node k v tip r) with f k v 
... | nothing = modDelete r
... | just v₁ = modId (node k v₁ tip r)
updateMinWithKey f (node k v l r) with updateMinWithKey f l
... | modId l' = modId (balanceR k v l' r)
... | modInsert l' = modInsert (balanceR k v l' r)
... | modDelete l' = modDelete (balanceR k v l' r)

-- Update the value at the maximal key.
updateMaxWithKey : {{Comparable K}} → (K → A -> Maybe A) → Map K A n → MapMod K A n
updateMaxWithKey f tip = modId tip
updateMaxWithKey f (node k v l tip) with f k v 
... | nothing = modDelete l
... | just v₁ = modId (node k v₁ l tip)
updateMaxWithKey f (node k v l r) with updateMaxWithKey f r
... | modId r' = modId (balanceL k v l r')
... | modInsert r' = modInsert (balanceL k v l r')
... | modDelete r' = modDelete (balanceL k v l r')

-- Update the value at the minimal key.
updateMin : {{Comparable K}} → (A → Maybe A) → Map K A n → MapMod K A n
updateMin f m = updateMinWithKey (λ _ x → f x) m

-- Update the value at the maximal key.
updateMax : {{Comparable K}} → (A -> Maybe A) → Map K A n → MapMod K A n
updateMax f m = updateMaxWithKey (λ _ x → f x) m

-- Retrieves the minimal (key,value) pair of the map, 
-- and the map stripped of that element.
minViewWithKey : {{Comparable K}} → Map K A (suc n) → Pair (Pair K A) (Map K A n)
minViewWithKey (node k a tip r) = ((k , a) , r)
minViewWithKey (node k a l@(node _ _ _ _) r) = let (ka , l') = minViewWithKey l in (ka , balanceR k a l' r)

-- Retrieves the maximal (key,value) pair of the map, 
-- and the map stripped of that element.
maxViewWithKey : {{Comparable K}} → Map K A (suc n) → Pair (Pair K A) (Map K A n)
maxViewWithKey (node k a l tip) = ((k , a) , l)
maxViewWithKey (node k a l r@(node _ _ _ _)) = let (ka , r') = maxViewWithKey r in (ka , balanceL k a l r')

-- Retrieves the value associated with minimal key of the map, 
-- and the map stripped of that element.
minView : {{Comparable K}} → Map K A (suc n) → Pair A (Map K A n)
minView m = let ((_ , a) , l) = minViewWithKey m in (a , l)

-- Retrieves the value associated with maximal key of the map, 
-- and the map stripped of that element.
maxView : {{Comparable K}} → Map K A (suc n) → Pair A (Map K A n)
maxView m = let ((_ , a) , r) = maxViewWithKey m in (a , r)

-- Delete and find the minimal element.
deleteFindMin : {{Comparable K}} → Map K A (suc n) → Pair (Pair K A) (Map K A n)
deleteFindMin (node k a tip r) = ((k , a) , r)
deleteFindMin (node k a l@(node _ _ _ _) r) = let (res , l') = deleteFindMin l in (res , balanceR k a l' r)

-- Delete and find the maximal element.
deleteFindMax : {{Comparable K}} → Map K A (suc n) → Pair (Pair K A) (Map K A n)
deleteFindMax (node k a l tip) = ((k , a) , l)
deleteFindMax (node k a l r@(node _ _ _ _)) = let (res , r') = deleteFindMax r in (res , balanceL k a l r')