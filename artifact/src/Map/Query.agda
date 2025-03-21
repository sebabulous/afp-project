module Map.Query where

open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Map.Map
open import Agda.Builtin.Maybe


-- %%%%%%%%%%%%%%%%%%%%%%%%% Size functions %%%%%%%%%%%%%%%%%%%%%%%%%
null : {K : Set}{V : Set} → Map K V → Bool
null tip = true
null (node _ _ _ _ _) = false

size : {K : Set}{V : Set} → Map K V → Nat
size tip = 0
size (node s _ _ _ _) = s

-- %%%%%%%%%%%%%%%%%%%%%%%%% Lookup functions %%%%%%%%%%%%%%%%%%%%%%%%%

-- `lookup` will look up the value at a key in the map. Returns the corresponding value as (Just value), or Nothing if the key isn't in the map
lookup : {K : Set} → {V : Set} → {{Comparable K}} → K → Map K V → Maybe V
lookup k tip = nothing
lookup k (node s k' v' l r) with compare k k'
... | eq = just v'
... | lt = lookup k l
... | gt = lookup k r

-- Find the value at a key. Returns Nothing when the element can not be found.
_!?_ : {K : Set} → {V : Set} → {{Comparable K}} → Map K V → K → Maybe V
m !? k = lookup k m

infixl 9 _!?_

-- Find the value at a key. Calls error when the element can not be found.
_!_ : {K : Set} → {V : Set} → {{Comparable K}} → Map K V → K → V
tip ! k =  {! throw the error "Map.!: given key is not an element in the map" !}
(node s k' v' l r) ! k with compare k k' 
... | eq = v'
... | lt = l ! k
... | gt = r ! k

infixl 9 _!_

-- `findWithDefault` returns the value at key k or returns default value def when the key is not in the map.
findWithDefault : {K : Set} → {V : Set} → {{Comparable K}} → V → K → Map K V → V
findWithDefault v k tip = v
findWithDefault v k (node s k' v' l r) with compare k k'
... | eq = v'
... | lt = findWithDefault v k l
... | gt = findWithDefault v k r

-- `member` returns True if the key is in the map, False otherwise
member : {K : Set} → {V : Set} → {{Comparable K}} → K → Map K V → Bool
member k tip = false
member k (node s k' v' l r) with compare k k'
... | eq = true
... | lt = member k l
... | gt = member k r

-- `notMember` returns False if the key is in the map, True otherwise
notMember : {K : Set} → {V : Set} → {{Comparable K}} → K → Map K V → Bool
notMember k tip = true
notMember k (node s k' v' l r) with compare k k'
... | eq = false
... | lt = notMember k l
... | gt = notMember k r

-- `lookupLT` finds largest key smaller than the given one and return the corresponding (key, value) pair.
lookupLT : {K : Set} → {V : Set} → {{Comparable K}} → K → Map K V → Maybe (Pair K V)
lookupLT k tip = nothing
lookupLT k (node s k' v' l r) with compare k k' 
... | gt = goJust k k' v' r
        where 
           goJust : {K : Set} → {V : Set} → {{Comparable K}} → K → K → V → Map K V → Maybe (Pair K V)
           goJust k k' v' tip = just (k' , v')
           goJust k k' v' (node x x₁ x₂ m m₁) with compare k k' 
           ... | gt = goJust k k' v' m₁
           ... | _ = goJust k x₁ x₂ m -- eq or lt
... | _ = lookupLT k l -- eq or lt

-- `lookupGT` finds smallest key greater than the given one and return the corresponding (key, value) pair.
lookupGT : {K : Set} → {V : Set} → {{Comparable K}} → K → Map K V → Maybe (Pair K V)
lookupGT k tip = nothing
lookupGT k (node s k' v' l r) with compare k k' 
... | lt = goJust k k' v' l
        where 
           goJust : {K : Set} → {V : Set} → {{Comparable K}} → K → K → V → Map K V → Maybe (Pair K V)
           goJust k k' v' tip = just (k' , v')
           goJust k k' v' (node x x₁ x₂ m m₁) with compare k k' 
           ... | lt = goJust k x₁ x₂ m
           ... | _ = goJust k k' v' m₁ -- eq or gt
... | _ = lookupGT k r -- eq or gt

-- `lookupLE` finds largest key smaller or equal to the given one and return the corresponding (key, value) pair.
lookupLE : {K V : Set} → {{Comparable K}} → K → Map K V → Maybe (Pair K V)
lookupLE = goNothing
  where
    goNothing : {K V : Set} → {{Comparable K}} → K → Map K V → Maybe (Pair K V)
    goNothing _ tip = nothing
    goNothing k (node _ kx v l r) with compare k kx
    ...                           | lt = goNothing k l
    ...                           | eq = just (kx , v)
    ...                           | gt = goJust k kx v r
      where
        goJust : {K V : Set} → {{Comparable K}} → K → K → V → Map K V → Maybe (Pair K V)
        goJust _ kx' v' tip = just (kx' , v')
        goJust k' kx' v' (node _ kx'' v'' l r) with compare k' kx''
        ...                                 | lt = goJust k' kx' v' l
        ...                                 | eq = just (kx'' , v'')
        ...                                 | gt = goJust k' kx'' v'' r

-- `lookupGE` finds smallest key greater or equal to the given one and return the corresponding (key, value) pair.
lookupGE : {K : Set} → {V : Set} → {{Comparable K}} → K → Map K V → Maybe (Pair K V)
lookupGE k tip = nothing
lookupGE k (node s k' v' l r) with compare k k'
... | eq = just (k' , v')
... | lt = goJust k k' v' l
        where
           goJust : {K : Set} → {V : Set} → {{Comparable K}} → K → K → V → Map K V → Maybe (Pair K V)
           goJust k k' v' tip = just (k' , v')
           goJust k k' v' (node x x₁ x₂ m m₁) with compare k k'
           ... | eq = just (x₁ , x₂)
           ... | lt = goJust k x₁ x₂ m
           ... | gt = goJust k k' v' m₁
... | gt = lookupGE k r