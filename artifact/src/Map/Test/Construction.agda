module Map.Test.Construction where

open import Agda.Builtin.Nat
open import Agda.Builtin.List
open import Agda.Builtin.String
open import Agda.Builtin.Equality

open import Map.Test.Cases
open import Map.Construction
open import Map.Conversion
open import Map.Map
open import Helpers.Pair
open import Helpers.Comparable

private variable
  K A : Set
  k : K
  a : A
  m n : Nat

inp1 : List (Pair Nat Nat)
inp1 = (10 , 3) ∷ (22 , 6) ∷ (34 , 9) ∷ (46 , 2) ∷ (58 , 5) ∷ (70 , 8) ∷ (82 , 7) ∷ (94 , 1) ∷ (106 , 4) ∷ (118 , 10) ∷ (130 , 11) ∷ (142 , 13) ∷ (154 , 12) ∷ (166 , 14) ∷ (178 , 15) ∷ (190 , 17) ∷ (202 , 16) ∷ (214 , 18) ∷ []

_ : toAscList (fromList inp1) ≡ sortKeysAsc inp1
_ = refl

