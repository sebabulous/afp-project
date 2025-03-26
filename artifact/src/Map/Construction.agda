module Map.Construction where

open import Agda.Builtin.List
open import Agda.Builtin.Nat

open import Map.Map

empty : {K : Set}{V : Set} -> Map K V zero
empty = tip

singleton : {K : Set}{V : Set} -> K -> V -> Map K V (suc zero)
singleton k v = node 1 k v tip tip

length : ∀{A B} → List (Pair A B) → Nat
length [] = zero
length (x ∷ xs) = suc (length xs)

fromList : {K : Set} → {V : Set} → {{Comparable K}} → (l : List (Pair K V)) → Map K V (length l)
fromList = {!   !}