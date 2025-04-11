module Helpers.Provers where

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Primitive

private variable
  ℓa ℓb : Level
  A : Set ℓa
  B : Set ℓb
  x y z : A

cong 
  : (f : A → B)
  →   x ≡   y
  → f x ≡ f y
cong _ refl = refl