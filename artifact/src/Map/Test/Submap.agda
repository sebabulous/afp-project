module Map.Test.Submap where

open import Agda.Builtin.Nat
open import Agda.Builtin.String
open import Agda.Builtin.Equality

open import Map.Test.Cases
open import Map.Submap
open import Map.Map

-- TO DO: write tests

private variable
  K A B : Set

isSubmapOfCorrect : {{_ : Comparable K}} → {{_ : Equal A}} → {ml mr : Map K A} → isSubmapOf ml mr ≡ isSubmapOfBy equal ml mr
isSubmapOfCorrect = refl

-- The expression (isSubmapOfBy f t1 t2) returns True if all keys in t1 are in tree t2, and when f returns True when applied to their respective values.
-- isProperSubmapOfByCorrect : {{_ : Comparable K}} → {{_ : Equal A}} → {f : A → B → Bool} → {ml : Map K A} → {mr : Map K B} → isSubmapOfBy f ml mk ≡ true → (k ∈k ml → k ∈k mr , f 