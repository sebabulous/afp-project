module Helpers.List where

open import Agda.Builtin.List
open import Agda.Builtin.Nat

open import Helpers.Comparable
open import Helpers.Pair

private variable
  K A : Set

insertWith : {{Comparable K}} → (A → A → A) → K → A → List (Pair K A) → List (Pair K A)
insertWith _ k' a' [] = (k' , a') ∷ []
insertWith f k' a' ((k , a) ∷ xs) with compare k' k
insertWith f k' a' ((k , a) ∷ xs) | eq = (k , f a' a) ∷ xs
insertWith f k' a' ((k , a) ∷ xs) | _ = (k , a) ∷ insertWith f k' a' xs

combineWith : {{Comparable K}} → (A → A → A) → List (Pair K A) → List (Pair K A) → List (Pair K A)
combineWith _ [] ys = ys
combineWith f ((k , a) ∷ xs) ys = combineWith f xs (insertWith f k a ys)

insertWithKey : {{Comparable K}} → (K → A → A → A) → K → A → List (Pair K A) → List (Pair K A)
insertWithKey _ k' a' [] = (k' , a') ∷ []
insertWithKey f k' a' ((k , a) ∷ xs) with compare k' k
insertWithKey f k' a' ((k , a) ∷ xs) | eq = (k , f k a' a) ∷ xs
insertWithKey f k' a' ((k , a) ∷ xs) | _ = (k , a) ∷ insertWithKey f k' a' xs

combineWithKey : {{Comparable K}} → (K → A → A → A) → List (Pair K A) → List (Pair K A) → List (Pair K A)
combineWithKey _ [] ys = ys
combineWithKey f ((k , a) ∷ xs) ys = combineWithKey f xs (insertWithKey f k a ys)

insertPair : Pair Nat Nat → List (Pair Nat Nat) → List (Pair Nat Nat)
insertPair (k' , a') [] = (k' , a') ∷ [] 
insertPair (k' , a') ((k , a) ∷ xs) with compare k' k
insertPair (k' , a') ((k , a) ∷ xs) | eq = (k , a') ∷ xs
insertPair (k' , a') ((k , a) ∷ xs) | gt = (k , a) ∷ insertPair (k' , a') xs
insertPair (k' , a') ((k , a) ∷ xs) | lt = (k' , a') ∷ (k , a) ∷ xs

sortKeysAsc : List (Pair Nat Nat) → List (Pair Nat Nat)
sortKeysAsc [] = []
sortKeysAsc (x ∷ xs) = insertPair x (sortKeysAsc xs)

takeList : Nat → List A → List A
takeList zero _ = []
takeList _ [] = []
takeList (suc n) (x ∷ xs) = x ∷ takeList n xs

dropList : Nat → List A → List A
dropList zero xs = xs
dropList _ [] = []
dropList (suc n) (x ∷ xs) = dropList n xs