open import Agda.Primitive
open import Agda.Builtin.Nat
open import Agda.Builtin.Unit
open import Agda.Builtin.Bool
open import Agda.Builtin.Sigma
open import Agda.Builtin.Equality
open import Agda.Builtin.Maybe 

_&&_ : Bool → Bool → Bool
false && _ = false
_ && false = false
_ && _ = true

data Ord : Set where
  eq : Ord
  lt : Ord
  gt : Ord




record Comparable (A : Set) : Set where
  field
    compare : A → A → Ord

open Comparable {{...}} public

-- source: https://agda.readthedocs.io/en/v2.5.2/language/record-types.html
record Pair (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

instance
  NatCmp : Comparable Nat
  compare {{ NatCmp }} zero zero = eq
  compare {{ NatCmp }} zero (suc _) = gt
  compare {{ NatCmp }} (suc _) zero = lt
  compare {{ NatCmp }} (suc x) (suc y) = compare x y

data Map (K : Set) (V : Set) : Set where
  tip : Map K V
  node : Nat → K → V → Map K V → Map K V → Map K V

null : {K : Set}{V : Set} → Map K V → Bool
null tip = true
null (node _ _ _ _ _) = false

size : {K : Set}{V : Set} → Map K V → Nat
size tip = 0
size (node s _ _ _ _) = s

isValid : {K : Set} → {V : Set} → {{Comparable K}} → Map K V → Bool
isValid tip = true
isValid (node s k' v' l r) with size l + size r
isValid (node s k' v' l r) | s' = ((s' + 1 == s) && isValid l) && isValid r

----------------------------------
-- Data.Map functions
----------------------------------

empty : {K : Set}{V : Set} -> Map K V
empty = tip

singleton : {K : Set}{V : Set} -> K -> V -> Map K V
singleton k v = node 1 k v tip tip

insert : {K : Set} → {V : Set} → {{Comparable K}} → K → V → Map K V → Map K V
insert k v tip = node 1 k v tip tip
insert k v (node s k' v' l r) with compare k k'
insert k v (node s k' v' l r) | eq = node s k v l r
insert k v (node s k' v' l r) | lt = let l' = insert k v l in node (1 + size l' + size r) k' v' l' r
insert k v (node s k' v' l r) | gt = let r' = insert k v r in node (1 + size l + size r') k' v' l r'

-- fromList : {K : Set}{V : Set}{{Comparable K}} -> List -> Map K V

insertWith : {K : Set} → {V : Set} → {{Comparable K}} → (V -> V -> V) -> K → V → Map K V → Map K V
insertWith f k v tip = node 1 k v tip tip
insertWith f k v (node s k' v' l r) with compare k k'
insertWith f k v (node s k' v' l r) | eq = node s k (f v v') l r
insertWith f k v (node s k' v' l r) | lt = let l' = insertWith f k v l in node (1 + size l' + size r) k' v' l' r
insertWith f k v (node s k' v' l r) | gt = let r' = insertWith f k v r in node (1 + size l + size r') k' v' l r'

insertWithKey : {K : Set} → {V : Set} → {{Comparable K}} → (K -> V -> V -> V) -> K → V → Map K V → Map K V
insertWithKey f k v tip = node 1 k v tip tip
insertWithKey f k v (node s k' v' l r) with compare k k'
insertWithKey f k v (node s k' v' l r) | eq = node s k (f k v v') l r
insertWithKey f k v (node s k' v' l r) | lt = let l' = insertWithKey f k v l in node (1 + size l' + size r) k' v' l' r
insertWithKey f k v (node s k' v' l r) | gt = let r' = insertWithKey f k v r in node (1 + size l + size r') k' v' l r'

-- insertLookupWithKey

-- delete : {K : Set} → {V : Set} → {{Comparable K}} → K → Map K V → Map K V
-- delete _ tip = tip
-- delete k (node s k' v l r) with compare k k'
-- delete k (node s k' v l r) | eq = 

-- deleteRoot : {K : Set} → {V : Set} → {{Comparable K}} → Map K V → Map K V
-- deleteRoot tip = tip
-- deleteRoot (node s _ _ tip tip) = tip
-- deleteRoot (node s _ _ tip r) = r
-- deleteRoot (node s _ _ l tip) = l
-- deleteRoot (node s _ _ l r) with compare (

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
tip ! k = {! throw the error "Map.!: given key is not an element in the map" !}
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
           ... | gt = goJust k x₁ x₂ m₁
           ... | _ = goJust k k' v' m -- eq or lt
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
lookupLE : {K : Set} → {V : Set} → {{Comparable K}} → K → Map K V → Maybe (Pair K V)
lookupLE k tip = nothing
lookupLE k (node s k' v' l r) with compare k k' 
... | eq = just (k' , v')
... | lt = lookupLE k l
... | gt = goJust k k' v' r
        where 
           goJust : {K : Set} → {V : Set} → {{Comparable K}} → K → K → V → Map K V → Maybe (Pair K V)
           goJust k k' v' tip = just (k' , v')
           goJust k k' v' (node x x₁ x₂ m m₁) with compare k k' 
           ... | eq = just (x₁ , x₂)
           ... | lt = goJust k k' v' m 
           ... | gt = goJust k x₁ x₂ m₁

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