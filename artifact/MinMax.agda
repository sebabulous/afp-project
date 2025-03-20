module artifact.MinMax where

open import Agda.Builtin.Maybe

open import artifact.Main

-- The minimal key of the map. Returns Nothing if the map is empty.
lookupMin : {K : Set}{V : Set} → Map K V → Maybe (Pair K V)
lookupMin tip = nothing
lookupMin (node _ k v tip _) = just (k , v)
lookupMin (node s k v l r) = lookupMin l

-- The maximal key of the map. Returns Nothing if the map is empty.
lookupMax : {K : Set}{V : Set} → Map K V → Maybe (Pair K V)
lookupMax tip = nothing
lookupMax (node _ k v _ tip) = just (k , v)
lookupMax (node s k v l r) = lookupMax r

-- The minimal key of the map. Calls error if the map is empty.
findMin : {K : Set}{V : Set} → Map K V → Pair K V
findMin m with lookupMin m 
... | nothing = {! error  !}
... | just m₁ = m₁

-- The maximal key of the map. Calls error if the map is empty.
findMax : {K : Set}{V : Set} → Map K V → Pair K V
findMax m with lookupMax m 
... | nothing = {! error  !}
... | just m₁ = m₁

-- Delete the minimal key. Returns an empty map if the map is empty.
deleteMin : {K : Set}{V : Set} → Map K V → Map K V
deleteMin tip = tip
deleteMin (node _ _ _ tip r) = r
deleteMin (node _ k v l r) = balanceR k v (deleteMin l) r

-- Delete the maximal key. Returns an empty map if the map is empty.
deleteMax : {K : Set}{V : Set} → Map K V → Map K V
deleteMax tip = tip
deleteMax (node _ _ _ l tip) = l
deleteMax (node _ k v l r) = balanceL k v l (deleteMax r)

-- Update the value at the minimal key.
updateMinWithKey : {K : Set} → {V : Set} → (K → V -> Maybe V) → Map K V → Map K V
updateMinWithKey f tip = tip
updateMinWithKey f (node s k v tip r) with f k v 
... | nothing = r
... | just v₁ = node s k v₁ tip r
updateMinWithKey f (node s k v l r) = balanceR k v (updateMinWithKey f l) r

-- Update the value at the maximal key.
updateMaxWithKey : {K : Set} → {V : Set} → (K → V -> Maybe V) → Map K V → Map K V
updateMaxWithKey f tip = tip
updateMaxWithKey f (node s k v l tip) with f k v 
... | nothing = l
... | just v₁ = node s k v₁ l tip
updateMaxWithKey f (node s k v l r) = balanceL k v l (updateMaxWithKey f r)

-- Update the value at the minimal key.
updateMin : {K : Set}{V : Set} → (V → Maybe V) → Map K V → Map K V
updateMin f m = updateMinWithKey (λ _ x → f x) m

-- Update the value at the maximal key.
updateMax : {K : Set}{V : Set} → (V -> Maybe V) → Map K V → Map K V
updateMax f m = updateMaxWithKey (λ _ x → f x) m

-- Retrieves the minimal (key,value) pair of the map, 
-- and the map stripped of that element, or Nothing if passed an empty map.
minViewWithKey : {K : Set} → {V : Set} → Map K V → Maybe (Pair (Pair K V) (Map K V))
minViewWithKey tip = nothing
minViewWithKey (node s k v tip r) = just ((k , v) , r)
minViewWithKey (node s k v l r) with minViewWithKey l 
... | nothing = nothing
... | just (m , l₁) = just (m , balanceR k v l₁ r)

-- Just $case minViewSure k x l r of
--    MinView km xm t -> ((km, xm), t)

-- Retrieves the maximal (key,value) pair of the map, 
-- and the map stripped of that element, or Nothing if passed an empty map.
maxViewWithKey : {K : Set} → {V : Set} → Map K V → Maybe (Pair (Pair K V) (Map K V))
maxViewWithKey tip = nothing
maxViewWithKey (node s k v l tip) = just ((k , v) , l)
maxViewWithKey (node s k v l r) with maxViewWithKey r
... | nothing = nothing 
... | just (m , r₁) = just (m , balanceL k v l r₁)

-- Retrieves the value associated with minimal key of the map, 
-- and the map stripped of that element, or Nothing if passed an empty map.
minView : {K : Set} → {V : Set} → Map K V → Maybe (Pair V (Map K V))
minView m with minViewWithKey m 
... | nothing = nothing
... | just ((_ , x) , m₁) = just (x , m₁)

-- Retrieves the value associated with maximal key of the map, 
-- and the map stripped of that element, or Nothing if passed an empty map.
maxView : {K : Set} → {V : Set} → Map K V → Maybe (Pair V (Map K V))
maxView m with maxViewWithKey m 
... | nothing = nothing
... | just ((_ , x) , m₁) = just (x , m₁)

-- Delete and find the minimal element.
deleteFindMin : {K : Set}{V : Set} → Map K V → Pair (Pair K V) (Map K V)
deleteFindMin m with minViewWithKey m
... | nothing = {!  error !}
... | just m₁ = m₁

-- Delete and find the maximal element.
deleteFindMax : {K : Set}{V : Set} → Map K V → Pair (Pair K V) (Map K V)
deleteFindMax m with maxViewWithKey m
... | nothing = {!  error !}
... | just m₁ = m₁