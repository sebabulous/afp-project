module Map.Insertion where

open import Agda.Builtin.Nat

open import Map.Query
open import Map.Map
open import Helpers.Comparable

private variable
  K A : Set

insert : {{Comparable K}} → K → A → Map K A → Map K A
insert k v tip = node 1 k v tip tip
insert k v (node s k' v' l r) with compare k k'
... | eq = node s k v l r
... | lt = let l' = insert k v l in node (1 + size l' + size r) k' v' l' r
... | gt = let r' = insert k v r in node (1 + size l + size r') k' v' l r'

insertWith : {{Comparable K}} → (A -> A -> A) -> K → A → Map K A → Map K A
insertWith f k v tip = node 1 k v tip tip
insertWith f k v (node s k' v' l r) with compare k k'
... | eq = node s k (f v v') l r
... | lt = let l' = insertWith f k v l in node (1 + size l' + size r) k' v' l' r
... | gt = let r' = insertWith f k v r in node (1 + size l + size r') k' v' l r'

insertWithKey : {{Comparable K}} → (K -> A -> A -> A) -> K → A → Map K A → Map K A
insertWithKey f k v tip = node 1 k v tip tip
insertWithKey f k v (node s k' v' l r) with compare k k'
... | eq = node s k (f k v v') l r
... | lt = let l' = insertWithKey f k v l in node (1 + size l' + size r) k' v' l' r
... | gt = let r' = insertWithKey f k v r in node (1 + size l + size r') k' v' l r'