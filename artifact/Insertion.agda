module artifact.Insertion where

open import Agda.Builtin.Nat

open import artifact.Main
open import artifact.Query

insert : {K : Set} → {V : Set} → {{Comparable K}} → K → V → Map K V → Map K V
insert k v tip = node 1 k v tip tip
insert k v (node s k' v' l r) with compare k k'
insert k v (node s k' v' l r) | eq = node s k v l r
insert k v (node s k' v' l r) | lt = let l' = insert k v l in node (1 + size l' + size r) k' v' l' r
insert k v (node s k' v' l r) | gt = let r' = insert k v r in node (1 + size l + size r') k' v' l r'

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
