{-# OPTIONS --allow-unsolved-metas #-}
module Map.Conversion where

open import Agda.Builtin.List

open import Map.Map

elems : {K : Set} → {V : Set} → Map K V → List V
elems = {!   !}

toList : {K : Set} → {V : Set} → Map K V → List (Pair K V)
toList = {!   !}


-- Note: there are more functions