module SizedMap.Insertion where

open import Agda.Builtin.Nat

open import SizedMap.Query
open import Helpers.Comparable
open import Helpers.Pair
open import SizedMap.Map
open import SizedMap.Balance

private variable
  K V : Set
  n : Nat


insert : {{Comparable K}} → K → V → Map K V n → MapIns K V n
insert = go
  where
    go : {{Comparable K}} → K → V → Map K V n → MapIns K V n
    go kx x tip = insInsert (node kx x tip tip)
    go kx x (node ky y l r) with compare kx ky
    ...                        | lt with go kx x l
    ...                             | insId l' = insId (balanceL ky y l' r)
    ...                             | insInsert l' = insInsert (balanceL ky y l' r)
    go kx x (node ky y l r) | gt with go kx x r
    ...                             | insId r' = insId (balanceR ky y l r')
    ...                             | insInsert r' = insInsert (balanceR ky y l r')
    go kx x (node ky y l r) | eq = insId (node kx x l r)

insertWith : {{Comparable K}} → (V -> V -> V) -> K → V → Map K V n → MapIns K V n
insertWith f k v tip = insInsert (node k v tip tip)
insertWith f k v (node k' v' l r) with compare k k'
insertWith f k v (node k' v' l r) | eq = insId (node k (f v v') l r)
insertWith f k v (node k' v' l r) | lt with insertWith f k v l
...                                      | insId l' = insId (node k' v' l' r)
...                                      | insInsert l' = insInsert (node k' v' l' r)
insertWith f k v (node k' v' l r) | gt with insertWith f k v r
...                                      | insId r' = insId (node k' v' l r')
...                                      | insInsert r' = insInsert (node k' v' l r')

insertWithKey : {{Comparable K}} → (K -> V -> V -> V) -> K → V → Map K V n → MapIns K V n
insertWithKey f k v tip = insInsert (node k v tip tip)
insertWithKey f k v (node k' v' l r) with compare k k'
...                                    | eq = insId (node k (f k v v') l r)
...                                    | lt with insertWithKey f k v l
...                                         | insId l' = insId (node k' v' l' r)
...                                         | insInsert l' = insInsert (node k' v' l' r)
insertWithKey f k v (node k' v' l r) | gt  with insertWithKey f k v r
...                                          | insId r' = insId (node k' v' l r')
...                                          | insInsert r' = insInsert (node k' v' l r')