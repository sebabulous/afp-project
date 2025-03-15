open import Agda.Primitive
open import Agda.Builtin.Nat
open import Agda.Builtin.Unit
open import Agda.Builtin.Bool
open import Agda.Builtin.Sigma
open import Agda.Builtin.Equality

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

instance
  NatCmp : Comparable Nat
  compare {{ NatCmp }} zero zero = eq
  compare {{ NatCmp }} zero (suc _) = gt
  compare {{ NatCmp }} (suc _) zero = lt
  compare {{ NatCmp }} (suc x) (suc y) = compare x y

data Map (K : Set) (V : Set) : Set where
  tip : Map K V
  node : Nat → K → V → Map K V → Map K V → Map K V

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