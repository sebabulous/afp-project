{-# OPTIONS --allow-unsolved-metas #-}
module artifact.Construction where

open import Agda.Builtin.List

open import artifact.Main

empty : {K : Set}{V : Set} -> Map K V
empty = tip

singleton : {K : Set}{V : Set} -> K -> V -> Map K V
singleton k v = node 1 k v tip tip

fromList : {K : Set} → {V : Set} → {{Comparable K}} → List (Pair K V) → Map K V 
fromList = {!   !}