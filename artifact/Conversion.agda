module artifact.Conversion where

open import Agda.Builtin.List

open import artifact.Main

toList : {K : Set} → {V : Set} → Map K V → List (Pair K V)
toList = {!   !}


-- Note: there are more functions