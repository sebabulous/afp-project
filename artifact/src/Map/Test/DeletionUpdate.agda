module Map.Test.DeletionUpdate where

open import Agda.Builtin.List
open import Agda.Builtin.Nat
open import Agda.Builtin.String
open import Agda.Builtin.Equality

open import Map.Test.Cases
open import Map.Construction
open import Map.Insertion
open import Map.DeletionUpdate
open import Map.Conversion
open import Map.Map
open import Helpers.Comparable
open import Helpers.Pair

-- TO DO: write tests

private variable
  K A : Set
  k : K
  a : A

test123 : Map Nat Nat
test123 = insert 1 1 (insert 2 2 (insert 3 3 tip))

test23 : Map Nat Nat
test23 = insert 2 2 (insert 3 3 tip)

insertOne : {{_ : Comparable K}} → List Nat → Nat → Map Nat Nat
insertOne [] n = insert n n tip
insertOne {K} (x ∷ xs) n = insert x x (insertOne {K} xs n)

insertNone : {{_ : Comparable K}} → List Nat → Map Nat Nat
insertNone [] = tip
insertNone {K} (x ∷ xs) = insert x x (insertNone {K} xs)


deleteDeletes : {n : Nat} → {xs : List Nat} → elems (delete n (insertOne xs n)) ≡ elems (insertNone xs)
deleteDeletes {n} {xs} = {!   !}

_ : elems (delete 1 test123) ≡ elems test23
_ = refl