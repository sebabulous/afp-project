module Map.Conversion where

open import Agda.Builtin.List

open import Map.Map
open import Map.Folds

elems : {K V : Set} → Map K V → List V
elems = foldr _∷_ []

keys : {K V : Set} → Map K V → List K
keys = foldrWithKey (λ k _ ks → k ∷ ks) []

toList : {K V : Set} → Map K V → List (Pair K V)
toAscList : {K V : Set} → Map K V → List (Pair K V)
toDescList : {K V : Set} → Map K V → List (Pair K V)
assocs : {K V : Set} → Map K V → List (Pair K V)

-- does the set collection not exist in agda?
-- keysSet
-- argSet

toList = toAscList

toAscList = foldrWithKey (λ k v kvs → (k , v) ∷ kvs) []

toDescList = foldlWithKey (λ kvs k v → (k , v) ∷ kvs) []

assocs = toAscList