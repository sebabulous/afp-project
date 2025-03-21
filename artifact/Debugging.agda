{-# OPTIONS --allow-unsolved-metas #-} 
module artifact.Debugging where

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool

open import artifact.Main
open import artifact.Query

-- TO DO: check if the code corresponds with the haskell function
valid : {K : Set} → {V : Set} → {{Comparable K}} → Map K V → Bool
valid m = {!   !}