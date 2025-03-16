module artifact.Debugging where

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool

open import artifact.Main
open import artifact.Query

-- TO DO: check if the code corresponds with the haskell function
valid : {K : Set} → {V : Set} → {{Comparable K}} → Map K V → Bool
valid tip = true
valid (node s k' v' l r) with size l + size r
valid (node s k' v' l r) | s' = ((s' + 1 == s) && valid l) && valid r