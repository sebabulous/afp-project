module SizedMap.Query where

open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.Maybe

open import SizedMap.Map
open import Helpers.Comparable
open import Helpers.Pair


private variable
  K V : Set
  m n : Nat

-- %%%%%%%%%%%%%%%%%%%%%%%%% Size functions %%%%%%%%%%%%%%%%%%%%%%%%%
-- Doesn't really make sense anymore with a sized list
-- null : Map K V n → Bool
-- null tip = true
-- null (node _ _ _ _ _) = false

null : MapMod K V n → Bool
null (modDelete tip) = true
null (modDelete _) = false
null (modInsert _) = false
null (modId tip) = true
null (modId _) = false

size : Map K V m → Nat
size {m = m} _ = m

-- %%%%%%%%%%%%%%%%%%%%%%%%% Lookup functions %%%%%%%%%%%%%%%%%%%%%%%%%

-- `lookup` will look up the value at a key in the map. Returns the corresponding value as (Just value), or Nothing if the key isn't in the map
lookup : {{Comparable K}} → K → Map K V n → Maybe V
lookup k tip = nothing
lookup k (node k' v' l r) with compare k k'
... | eq = just v'
... | lt = lookup k l
... | gt = lookup k r

-- Find the value at a key. Returns Nothing when the element can not be found.
_!?_ : {{Comparable K}} → Map K V n → K → Maybe V
m !? k = lookup k m

infixl 9 _!?_

-- Find the value at a key. Calls error when the element can not be found.
_!_ : {{Comparable K}} → Map K V n → K → V
tip ! k =  {! throw the error "Map.!: given key is not an element in the map" !}
(node k' v' l r) ! k with compare k k' 
... | eq = v'
... | lt = l ! k
... | gt = r ! k

infixl 9 _!_

-- `findWithDefault` returns the value at key k or returns default value def when the key is not in the map.
findWithDefault : {{Comparable K}} → V → K → Map K V n → V
findWithDefault v k tip = v
findWithDefault v k (node k' v' l r) with compare k k'
... | eq = v'
... | lt = findWithDefault v k l
... | gt = findWithDefault v k r

-- `member` returns True if the key is in the map, False otherwise
member : {{Comparable K}} → K → Map K V n → Bool
member k tip = false
member k (node k' v' l r) with compare k k'
... | eq = true
... | lt = member k l
... | gt = member k r

-- `notMember` returns False if the key is in the map, True otherwise
notMember : {{Comparable K}} → K → Map K V n → Bool
notMember k tip = true
notMember k (node k' v' l r) with compare k k'
... | eq = false
... | lt = notMember k l
... | gt = notMember k r

-- `lookupLT` finds largest key smaller than the given one and return the corresponding (key, value) pair.
lookupLT : {{Comparable K}} → K → Map K V n → Maybe (Pair K V)
lookupLT k tip = nothing
lookupLT k (node k' v' l r) with compare k k' 
... | gt = goJust k k' v' r
        where 
           goJust : {{Comparable K}} → K → K → V → Map K V n → Maybe (Pair K V)
           goJust k k' v' tip = just (k' , v')
           goJust k k' v' (node x₁ x₂ m m₁) with compare k k' 
           ... | gt = goJust k k' v' m₁
           ... | eq = goJust k x₁ x₂ m
           ... | lt = goJust k x₁ x₂ m
... | eq = lookupLT k l
... | lt = lookupLT k l

-- `lookupGT` finds smallest key greater than the given one and return the corresponding (key, value) pair.
lookupGT : {{Comparable K}} → K → Map K V n → Maybe (Pair K V)
lookupGT k tip = nothing
lookupGT k (node k' v' l r) with compare k k' 
... | lt = goJust k k' v' l
        where 
           goJust : {{Comparable K}} → K → K → V → Map K V n → Maybe (Pair K V)
           goJust k k' v' tip = just (k' , v')
           goJust k k' v' (node x₁ x₂ m m₁) with compare k k' 
           ... | lt = goJust k x₁ x₂ m
           ... | eq = goJust k k' v' m₁
           ... | gt = goJust k k' v' m₁
... | eq = lookupGT k r
... | gt = lookupGT k r

-- `lookupLE` finds largest key smaller or equal to the given one and return the corresponding (key, value) pair.
lookupLE : {{Comparable K}} → K → Map K V n → Maybe (Pair K V)
lookupLE = goNothing
  where
    goNothing : {{Comparable K}} → K → Map K V n → Maybe (Pair K V)
    goNothing _ tip = nothing
    goNothing k (node kx v l r) with compare k kx
    ...                           | lt = goNothing k l
    ...                           | eq = just (kx , v)
    ...                           | gt = goJust k kx v r
      where
        goJust : {{Comparable K}} → K → K → V → Map K V n → Maybe (Pair K V)
        goJust _ kx' v' tip = just (kx' , v')
        goJust k' kx' v' (node kx'' v'' l r) with compare k' kx''
        ...                                 | lt = goJust k' kx' v' l
        ...                                 | eq = just (kx'' , v'')
        ...                                 | gt = goJust k' kx'' v'' r

-- `lookupGE` finds smallest key greater or equal to the given one and return the corresponding (key, value) pair.
lookupGE : {{Comparable K}} → K → Map K V n → Maybe (Pair K V)
lookupGE k tip = nothing
lookupGE k (node k' v' l r) with compare k k'
... | eq = just (k' , v')
... | lt = goJust k k' v' l
        where
           goJust : {{Comparable K}} → K → K → V → Map K V n → Maybe (Pair K V)
           goJust k k' v' tip = just (k' , v')
           goJust k k' v' (node x₁ x₂ m m₁) with compare k k'
           ... | eq = just (x₁ , x₂)
           ... | lt = goJust k x₁ x₂ m
           ... | gt = goJust k k' v' m₁
... | gt = lookupGE k r