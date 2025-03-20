{-# OPTIONS --allow-unsolved-metas #-}
module artifact.Construction where

open import Agda.Builtin.List

open import artifact.Main

fromList : {K : Set} → {V : Set} → {{Comparable K}} → List (Pair K V) → Map K V 
fromList = {!   !}