module SizedMap.Conversion where

open import Agda.Builtin.Nat

open import SizedMap.Map
open import SizedMap.Folds
open import Helpers.Comparable
open import Helpers.Pair
open import Helpers.List

private variable
  K V : Set
  n : Nat

elems : Map K V n → Vec V n
elems tip = []
elems (node k a l r) = elems l ++ (a ∷ elems r)

keys : Map K V n → Vec K n
keys tip = []
keys (node k _ l r) = keys l ++ (k ∷ keys r)

toVec : Map K V n → Vec (Pair K V) n
toVec tip = []
toVec (node k a l r) = toVec l ++ ((k , a) ∷ toVec r)