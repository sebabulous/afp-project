module Map.Conversion where

open import Agda.Builtin.Nat
open import Agda.Builtin.List

open import Map.Map

private variable
  K V : Set
  n : Nat

elems : Map K V n → List V
elems = {!   !}

toList : Map K V n → List (Pair K V)
toList = {!   !}


-- Note: there are more functions