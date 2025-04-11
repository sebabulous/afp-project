module SizedMap.Construction where

open import Agda.Builtin.List
open import Agda.Builtin.Sigma
open import Agda.Builtin.Nat

open import SizedMap.Map
open import SizedMap.Insertion
open import Helpers.Comparable
open import Helpers.Pair

private variable
  K A B : Set
  m n : Nat

empty : Map K A zero
empty = tip

singleton : K -> A -> Map K A (suc zero)
singleton k v = node k v tip tip

foldrVec : (A → B → B) → B → Vec A n → B
foldrVec _ b [] = b
foldrVec f b (a ∷ vec) = f a (foldrVec f b vec)

foldlVec : (B → A → B) → B → Vec (Pair K A) n → B
foldlVec _ b [] = b
foldlVec f b ((_ , a) ∷ vec) = foldlVec f (f b a) vec

fromVec : {{Comparable K}} → Vec (Pair K A) n → Σ Nat (Map K A)
fromVec [] = (zero , tip)
fromVec ((k , a) ∷ vec) with fromVec vec
fromVec ((k , a) ∷ vec) | (n , map) with insert k a map
fromVec ((k , a) ∷ vec) | (n , map) | insInsert map' = (suc n , map')
fromVec ((k , a) ∷ vec) | (n , map) | insId map' = (n , map')