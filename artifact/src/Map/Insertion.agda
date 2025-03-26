module Map.Insertion where

open import Agda.Builtin.Nat

open import Map.Query
open import Map.Map
open import Map.Construction
open import Map.Balance

private variable
  K V : Set
  n : Nat

insert : {{Comparable K}} → K → V → Map K V n → MapIns K V n
insert = go
  where
    go : {{Comparable K}} → K → V → Map K V n → MapIns K V n
    go kx x tip = insInsert (singleton kx x)
    go kx x (node sz ky y l r) with compare kx ky
    -- ...                        | lt = balanceL ky y (go kx x l) r
    ...                        | lt with go kx x l
    ...                             | insId l' = insId (balanceL ky y l' r)
    ...                             | insInsert l' = insInsert (balanceL ky y l' r)
    -- ...                        | gt = balanceR ky y l (go kx x r)
    go kx x (node sz ky y l r) | gt with go kx x r
    ...                             | insId r' = insId (balanceR ky y l r')
    ...                             | insInsert r' = insInsert (balanceR ky y l r')
    go kx x (node sz ky y l r) | eq = insId (node sz kx x l r)
-- insert : {{Comparable K}} → K → V → Map K V n → Map K V (n + 1)
-- insert = go
--   where
--     go : {{Comparable K}} → K → V → Map K V n → Map K V (n + 1)
--     go kx x tip = singleton kx x
--     go kx x (node sz ky y l r) with compare kx ky
--     ...                        | lt = balanceL ky y (go kx x l) r
--     ...                        | gt = balanceR ky y l (go kx x r)
--     ...                        | eq = node sz kx x l r
-- insert k v tip = node 1 k v tip tip
-- insert k v (node s k' v' l r) with compare k k'
-- insert k v (node s k' v' l r) | eq = node s k v l r
-- insert k v (node s k' v' l r) | lt = let l' = insert k v l in node (1 + size l' + size r) k' v' l' r
-- insert k v (node s k' v' l r) | gt = let r' = insert k v r in node (1 + size l + size r') k' v' l r'

insertWith : {{Comparable K}} → (V -> V -> V) -> K → V → Map K V n → MapIns K V n
insertWith f k v tip = insInsert (node 1 k v tip tip)
insertWith f k v (node s k' v' l r) with compare k k'
insertWith f k v (node s k' v' l r) | eq = insId (node s k (f v v') l r)
insertWith f k v (node s k' v' l r) | lt with insertWith f k v l
...                                      | insId l' = insId (node (1 + size l' + size r) k' v' l' r)
...                                      | insInsert l' = insInsert (node (1 + size l' + size r) k' v' l' r)
insertWith f k v (node s k' v' l r) | gt with insertWith f k v r
...                                      | insId r' = insId (node (1 + size l + size r') k' v' l r')
...                                      | insInsert r' = insInsert (node (1 + size l + size r') k' v' l r')

insertWithKey : {{Comparable K}} → (K -> V -> V -> V) -> K → V → Map K V n → MapIns K V n
insertWithKey f k v tip = insInsert (node 1 k v tip tip)
insertWithKey f k v (node s k' v' l r) with compare k k'
...                                    | eq = insId (node s k (f k v v') l r)
...                                    | lt with insertWithKey f k v l
...                                         | insId l' = insId (node (1 + size l' + size r) k' v' l' r)
...                                         | insInsert l' = insInsert (node (1 + size l' + size r) k' v' l' r)
insertWithKey f k v (node s k' v' l r) | gt  with insertWithKey f k v r
...                                          | insId r' = insId (node (1 + size l + size r') k' v' l r')
...                                          | insInsert r' = insInsert (node (1 + size l + size r') k' v' l r')