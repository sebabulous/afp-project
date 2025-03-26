module Map.MinMax where

open import Agda.Builtin.Nat
open import Agda.Builtin.Maybe

open import Map.Balance
open import Map.Map

open import Map.DeletionUpdate

private variable
  K A : Set
  m n : Nat

-- The minimal key of the map. Returns Nothing if the map is empty.
lookupMin : Map K A n → Maybe (Pair K A)
lookupMin tip = nothing
lookupMin (node _ k v tip _) = just (k , v)
lookupMin (node s k v l r) = lookupMin l

-- The maximal key of the map. Returns Nothing if the map is empty.
lookupMax : Map K A n → Maybe (Pair K A)
lookupMax tip = nothing
lookupMax (node _ k v _ tip) = just (k , v)
lookupMax (node s k v l r) = lookupMax r

-- The minimal key of the map. Calls error if the map is empty.
findMin : Map K A n → Pair K A
findMin m with lookupMin m 
... | nothing = {! error  !}
... | just m₁ = m₁

-- The maximal key of the map. Calls error if the map is empty.
findMax : Map K A n → Pair K A
findMax m with lookupMax m 
... | nothing = {! error  !}
... | just m₁ = m₁

-- Delete the minimal key. Returns an empty map if the map is empty.
deleteMin : {{Comparable K}} → Map K A (suc n) → Map K A n
-- deleteMin tip = tip
deleteMin (node _ _ _ tip r) = r
deleteMin (node _ k v l@(node _ _ _ _ _) r) = balanceR k v (deleteMin l) r


-- Delete the maximal key. Returns an empty map if the map is empty.
deleteMax : {{Comparable K}} → Map K A (suc n) → Map K A n
-- deleteMax tip = tip
deleteMax (node _ _ _ l tip) = l
deleteMax (node _ k v l r@(node _ _ _ _ _)) = balanceL k v l (deleteMax r)

-- Update the value at the minimal key.
updateMinWithKey : {{Comparable K}} → (K → A -> Maybe A) → Map K A n → MapMod K A n
updateMinWithKey f tip = modId tip
updateMinWithKey f (node s k v tip r) with f k v 
... | nothing = modDelete r
... | just v₁ = modId (node s k v₁ tip r)
-- updateMinWithKey f (node s k v l r) = balanceR k v (updateMinWithKey f l) r
updateMinWithKey f (node s k v l r) with updateMinWithKey f l
... | modId l' = modId (balanceR k v l' r)
... | modInsert l' = modInsert (balanceR k v l' r)
... | modDelete l' = modDelete (balanceR k v l' r)

-- Update the value at the maximal key.
updateMaxWithKey : {{Comparable K}} → (K → A -> Maybe A) → Map K A n → MapMod K A n
updateMaxWithKey f tip = modId tip
updateMaxWithKey f (node s k v l tip) with f k v 
... | nothing = modDelete l
... | just v₁ = modId (node s k v₁ l tip)
-- updateMaxWithKey f (node s k v l r) = balanceL k v l (updateMaxWithKey f r)
updateMaxWithKey f (node s k v l r) with updateMaxWithKey f r
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
-- and the map stripped of that element, or Nothing if passed an empty map.
minViewWithKey : {{Comparable K}} → Map K A (suc n) → Maybe (Pair (Pair K A) (Map K A n))
-- minViewWithKey tip = nothing
minViewWithKey (node s k v tip r) = just ((k , v) , r)
minViewWithKey (node s k v l@(node _ _ _ _ _) r) with minViewWithKey l 
... | nothing = nothing
... | just (m , l₁) = just (m , balanceR k v l₁ r)

-- Retrieves the maximal (key,value) pair of the map, 
-- and the map stripped of that element, or Nothing if passed an empty map.
maxViewWithKey : {{Comparable K}} → Map K A (suc n) → Maybe (Pair (Pair K A) (Map K A n))
-- maxViewWithKey tip = nothing
maxViewWithKey (node s k v l tip) = just ((k , v) , l)
maxViewWithKey (node s k v l r@(node _ _ _ _ _)) with maxViewWithKey r
... | nothing = nothing 
... | just (m , r₁) = just (m , balanceL k v l r₁)

-- Retrieves the value associated with minimal key of the map, 
-- and the map stripped of that element, or Nothing if passed an empty map.
minView : {{Comparable K}} → Map K A (suc n) → Maybe (Pair A (Map K A n))
minView m with minViewWithKey m 
... | nothing = nothing
... | just ((_ , x) , m₁) = just (x , m₁)

-- Retrieves the value associated with maximal key of the map, 
-- and the map stripped of that element, or Nothing if passed an empty map.
maxView : {{Comparable K}} → Map K A (suc n) → Maybe (Pair A (Map K A n))
maxView m with maxViewWithKey m 
... | nothing = nothing
... | just ((_ , x) , m₁) = just (x , m₁)

-- Delete and find the minimal element.
deleteFindMin : {{Comparable K}} → Map K A (suc n) → Pair (Pair K A) (Map K A n)
deleteFindMin m with minViewWithKey m
... | nothing = {!  error !}
... | just m₁ = m₁

-- Delete and find the maximal element.
deleteFindMax : {{Comparable K}} → Map K A (suc n) → Pair (Pair K A) (Map K A n)
deleteFindMax m with maxViewWithKey m
... | nothing = {!  error !}
... | just m₁ = m₁ 